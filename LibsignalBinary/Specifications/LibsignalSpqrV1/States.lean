/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth

/-!
# SPQR V1: braid state machine and incremental ML-KEM-768 (`src/incremental_mlkem768.rs`, `src/v1/`)

**Trusted in part.** The theorems of `Computational/Theorems/` use only part of this file (see
`Computational/docs/TRUSTED_BASE.md`): the rest is mostly the camelCase aliases (`fromPb` /
`intoPb`), model-only helpers (`SharedSecret`, `KeyPair`, `decapsulate`, `validate_pk`,
`States.epoch`), the self-test stubs (`stubMlKem`, `stubPolyApi`, `stubAuthApi`, `StubEncoder`,
`StubDecoder`), and the `check*` / `guard_*` test drivers (`guard_issue1275`,
`guard_message_serialize`, `guard_full_braid_and_pb_roundtrip`, `guard_panics_and_errors`), all
checked by Lean.

Models SPQR V1 sparse continuous key agreement (SCKA) over abstract `MlKem`, erasure-coding
`PolyApi`, and authenticator/KDF `AuthApi`, with explicit panic/error outcomes (`StatesPanic`,
`StatesError`, `StatesResult`):
- `src/incremental_mlkem768.rs`: `Keys`, `generate`, `encaps1`, `encaps2`, `decaps`,
  `ek_matches_header` (`validate_pk_bytes`),
  `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`, and
  `flip_endianness_of_encapsulation_state`.
- `src/v1/unchunked/{send_ek, send_ct}`: unchunked states (`KeysUnsampled`, `HeaderSent`, `EkSent`,
  `EkSentCt1Received`; `NoHeaderReceived`, `HeaderReceived`, `Ct1Sent`, `Ct1SentEkReceived`,
  `Ct2Sent`), transitions (`send_ek`, ...), and `into_pb` / `from_pb`.
- `src/v1/chunked/`: the 11-variant `States` braid machine (`States.init_a`, `States.init_b`,
  `States.send` -> `V1Send`, `States.recv` -> `V1Recv`, `States.into_pb`, `States.from_pb`) and
  SCKA wire messages (`MessagePayload`, `Message`, `MessageType`, `Message.serialize`,
  `Message.deserialize`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

/-! ## Byte helpers -/

/-- Big-endian 8-byte encoding (`u64::to_be_bytes`). -/
def u64ToBeBytes (v : BitVec 64) : Bytes :=
  [ v.extractLsb' 56 8, v.extractLsb' 48 8, v.extractLsb' 40 8, v.extractLsb' 32 8,
    v.extractLsb' 24 8, v.extractLsb' 16 8, v.extractLsb'  8 8, v.extractLsb'  0 8 ]

def bytesToVector? (n : Nat) (xs : Bytes) : Option (List.Vector (BitVec 8) n) :=
  if h : xs.length = n then some ⟨xs, h⟩ else none

/-! ## Panics and results (`src/incremental_mlkem768.rs`, `src/v1/`) -/

/-- Explicit Rust panic sites in `src/incremental_mlkem768.rs` and `src/v1/{unchunked,chunked}/`. -/
inductive StatesPanic where
  | spqr (p : SpqrPanic)
  | rngExhausted (needed available : Nat)
  | encaps1Failed
  | encaps2BadSize (esLen ekLen : Nat)
  | issue1275BadLen (esLen : Nat)
  | flipEndiannessBadLen (esLen : Nat)
  | decapsBadSize (dkLen ct1Len ct2Len : Nat)
  | unchunkedRecvCt1EpochMismatch (epoch selfEpoch : Epoch)
  | unchunkedRecvCt2EpochOverflow
  | unchunkedRecvHeaderEpochMismatch (epoch selfEpoch : Epoch)
  | unchunkedRecvEkEpochMismatch (epoch selfEpoch : Epoch)
  | unchunkedRecvNextEpochOverflow
  | unchunkedRecvNextEpochMismatch (expected nextEpoch : Epoch)
  | polyExpectFailed (site : String)
  | chunkedEpochMismatch (site : String) (epoch selfEpoch : Epoch)
  | decodedSliceBounds (site : String) (decodedLen splitAt : Nat)
  deriving DecidableEq, Repr, Inhabited

class ToStatesPanic (ε : Type) where
  toStatesPanic : ε → StatesPanic

instance : ToStatesPanic StatesPanic where
  toStatesPanic := id

instance : ToStatesPanic SpqrPanic where
  toStatesPanic := StatesPanic.spqr

def liftSpqrPanic {α : Type} (r : Except SpqrPanic α) : Except StatesPanic α :=
  match r with
  | .ok v => .ok v
  | .error p => .error (.spqr p)

instance : MonadLift (Except SpqrPanic) (Except StatesPanic) where
  monadLift r := liftSpqrPanic r

/-- Clean `Err(Error)` return versus Rust panic (`StatesPanic`). -/
inductive StatesError where
  | err (e : Error)
  | panic (p : StatesPanic)
  deriving DecidableEq, Repr, Inhabited

namespace StatesError

def isPanic : StatesError → Bool
  | .panic _ => true
  | .err _ => false

end StatesError

abbrev StatesResult (α : Type) := Except StatesError α

namespace StatesResult

def ofPanic {ε : Type} [ToStatesPanic ε] (r : Except ε α) : StatesResult α :=
  match r with
  | .ok v => .ok v
  | .error p => .error (.panic (ToStatesPanic.toStatesPanic p))

def ofError (r : Except Error α) : StatesResult α :=
  match r with
  | .ok v => .ok v
  | .error e => .error (.err e)

def isPanic (r : StatesResult α) : Bool :=
  match r with
  | .ok _ => false
  | .error e => e.isPanic

end StatesResult

/-! ## Parameter APIs: `PolyApi`, `AuthApi` -/

/-- Abstract polynomial erasure-coding interface (`src/encoding.rs`, `src/encoding/polynomial.rs`). -/
structure PolyApi where
  Chunk : Type
  PolynomialError : Type
  EncodingError : Type
  PolyEncoder : Type
  PolyDecoder : Type
  [decEqChunk : DecidableEq Chunk]
  [reprChunk : Repr Chunk]
  [inhabitedChunk : Inhabited Chunk]
  [decEqPolyErr : DecidableEq PolynomialError]
  [reprPolyErr : Repr PolynomialError]
  [decEqEncErr : DecidableEq EncodingError]
  [reprEncErr : Repr EncodingError]
  [decEqEncoder : DecidableEq PolyEncoder]
  [decEqDecoder : DecidableEq PolyDecoder]
  [reprEncoder : Repr PolyEncoder]
  [reprDecoder : Repr PolyDecoder]
  mkChunk : BitVec 16 → List.Vector (BitVec 8) 32 → Chunk
  chunkIndex : Chunk → BitVec 16
  chunkData : Chunk → List.Vector (BitVec 8) 32
  encode_bytes : Bytes → Except SpqrPanic (Except EncodingError PolyEncoder)
  next_chunk : PolyEncoder → Except SpqrPanic (PolyEncoder × Chunk)
  encoder_into_pb : PolyEncoder → PolynomialEncoder
  encoder_from_pb : PolynomialEncoder → Except SpqrPanic (Except PolynomialError PolyEncoder)
  decoder_new : Nat → Except SpqrPanic (Except EncodingError PolyDecoder)
  add_chunk : PolyDecoder → Chunk → Except SpqrPanic PolyDecoder
  decoded_message : PolyDecoder → Except SpqrPanic (Option Bytes)
  decoder_into_pb : PolyDecoder → PolynomialDecoder
  decoder_from_pb : PolynomialDecoder → Except SpqrPanic (Except PolynomialError PolyDecoder)

attribute [instance]
  PolyApi.decEqChunk PolyApi.reprChunk PolyApi.inhabitedChunk
  PolyApi.decEqPolyErr PolyApi.reprPolyErr
  PolyApi.decEqEncErr PolyApi.reprEncErr
  PolyApi.decEqEncoder PolyApi.decEqDecoder PolyApi.reprEncoder PolyApi.reprDecoder

def AUTHENTICATOR_MACSIZE : Nat := 32

/-- Abstract authenticator and HKDF interface (`src/authenticator.rs`, `src/kdf.rs`). -/
structure AuthApi where
  Authenticator : Type
  [decEqAuth : DecidableEq Authenticator]
  [reprAuth : Repr Authenticator]
  new : Bytes → Epoch → Except SpqrPanic Authenticator
  update : Authenticator → Epoch → Bytes → Except SpqrPanic Authenticator
  mac_hdr : Authenticator → Epoch → Bytes → Except SpqrPanic Bytes
  mac_ct : Authenticator → Epoch → Bytes → Except SpqrPanic Bytes
  /-- `Authenticator::verify_hdr` (`util::compare` panics if `expected_mac.len() > 32`). -/
  verify_hdr : Authenticator → Epoch → Bytes → Bytes →
    Except SpqrPanic (Except Error Unit)
  /-- `Authenticator::verify_ct` (`util::compare` panics if `expected_mac.len() > 32`). -/
  verify_ct : Authenticator → Epoch → Bytes → Bytes →
    Except SpqrPanic (Except Error Unit)
  into_pb : Authenticator → ProtoAuthenticator
  from_pb : ProtoAuthenticator → Authenticator
  /-- `kdf::hkdf_to_vec` (`src/kdf.rs:6–18`; panics if `okm_len > 255 * 32`). -/
  hkdf_to_vec : Bytes → Bytes → Bytes → Nat → Except SpqrPanic Bytes

attribute [instance] AuthApi.decEqAuth AuthApi.reprAuth

/-! ## Incremental ML-KEM-768 and issue-1275 fix-up (`src/incremental_mlkem768.rs`) -/

def CIPHERTEXT1_SIZE : Nat := 960

def CIPHERTEXT2_SIZE : Nat := 128

def HEADER_SIZE : Nat := 64

def ENCAPSULATION_KEY_SIZE : Nat := 1152

def ENCAPSULATION_STATE_SIZE : Nat := 2080

def DECAPSULATION_KEY_SIZE : Nat := 2400

def KEY_GENERATION_SEED_SIZE : Nat := 64

def SHARED_SECRET_SIZE : Nat := 32

abbrev Ciphertext1 := Bytes

abbrev EncapsulationState := Bytes

abbrev Ciphertext2 := Bytes

abbrev Header := Bytes

abbrev EncapsulationKey := Bytes

abbrev DecapsulationKey := Bytes

abbrev SharedSecret := Secret

/-- Split ML-KEM-768 key pair (`pub struct Keys`, `src/incremental_mlkem768.rs:22–26`). -/
structure Keys where
  ek : EncapsulationKey
  dk : DecapsulationKey
  hdr : Header
  deriving DecidableEq, Repr, Inhabited

abbrev KeyPair := Keys

/-- Swap adjacent byte pairs `(b0, b1) ↦ (b1, b0)`. -/
def swapAdjacentPairs : Bytes → Bytes
  | b0 :: b1 :: rest => b1 :: b0 :: swapAdjacentPairs rest
  | xs => xs

/-- Swap each 2-byte pair in `es[0 .. es.len() - 32]`, leaving the trailing 32-byte randomness unchanged. -/
def flipEndiannessOfEncapsulationStateBytes (es : EncapsulationState) : EncapsulationState :=
  let prefixLen := es.length - 32
  swapAdjacentPairs (es.take prefixLen) ++ es.drop prefixLen

/-- `flip_endianness_of_encapsulation_state` (`src/incremental_mlkem768.rs:143–153`). -/
def flip_endianness_of_encapsulation_state (es : EncapsulationState) :
    Except StatesPanic EncapsulationState :=
  if es.length % 2 != 0 || !(es.length > 32) then
    .error (.flipEndiannessBadLen es.length)
  else
    .ok (flipEndiannessOfEncapsulationStateBytes es)

/-- Scan `es[1536..2048]` in 2-byte LE words (`src/incremental_mlkem768.rs:117–137`): skip `0`/`-1`,
return `false` on valid LE (`1`, `2`, `0xFFFE`), `true` on byte-swapped BE (`0x0100`, `0x0200`,
`0xFEFF`), and `false` otherwise. -/
def issue1275NeedsFlip : Bytes → Bool
  | b0 :: b1 :: rest =>
    let w : BitVec 16 := (b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16
    if w == 0x0000#16 || w == 0xFFFF#16 then
      issue1275NeedsFlip rest
    else if w == 0x0001#16 || w == 0x0002#16 || w == 0xFFFE#16 then
      false
    else if w == 0x0100#16 || w == 0x0200#16 || w == 0xFEFF#16 then
      true
    else
      false
  | _ => false

def potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes
    (es : EncapsulationState) : Option EncapsulationState :=
  let error2Bytes := (es.drop 1536).take (2080 - 32 - 1536)
  if issue1275NeedsFlip error2Bytes then
    some (flipEndiannessOfEncapsulationStateBytes es)
  else
    none

/-- `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`
(`src/incremental_mlkem768.rs:92–138`), checking `es.len() == 2080`. -/
def potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
    (es : EncapsulationState) : Except StatesPanic (Option EncapsulationState) :=
  if es.length != ENCAPSULATION_STATE_SIZE then
    .error (.issue1275BadLen es.length)
  else
    let error2Bytes := (es.drop 1536).take (2080 - 32 - 1536)
    if issue1275NeedsFlip error2Bytes then do
      let fixed ← flip_endianness_of_encapsulation_state es
      .ok (some fixed)
    else
      .ok none

/-- `ek_matches_header` (`src/incremental_mlkem768.rs:28–30`). -/
def ek_matches_header (K : MlKem) (ek : EncapsulationKey) (hdr : Header) : Bool :=
  K.validPkBytes hdr ek

def validate_pk_bytes (K : MlKem) (hdr : Header) (ek : EncapsulationKey) : Bool :=
  K.validPkBytes hdr ek

abbrev validate_pk := validate_pk_bytes

/-- `generate` (`src/incremental_mlkem768.rs:34–43`): consumes 64 seed bytes from `tape`. -/
def generate (K : MlKem) (tape : Bytes) : Except StatesPanic (Keys × Bytes) :=
  match bytesToVector? KEY_GENERATION_SEED_SIZE (tape.take KEY_GENERATION_SEED_SIZE) with
  | none => .error (.rngExhausted KEY_GENERATION_SEED_SIZE tape.length)
  | some seed =>
    let (hdr, ek, dk) := K.fromSeed seed
    .ok ({ ek := ek.toList, dk := dk.toList, hdr := hdr.toList },
      tape.drop KEY_GENERATION_SEED_SIZE)

/-- `encaps1` (`src/incremental_mlkem768.rs:48–66`): consumes 32 random bytes from `tape` and panics
if `K.encaps1` returns `none`. -/
def encaps1 (K : MlKem) (hdr : Header) (tape : Bytes) :
    Except StatesPanic ((Ciphertext1 × EncapsulationState × Secret) × Bytes) :=
  match bytesToVector? SHARED_SECRET_SIZE (tape.take SHARED_SECRET_SIZE) with
  | none => .error (.rngExhausted SHARED_SECRET_SIZE tape.length)
  | some rand =>
    match K.encaps1 hdr rand with
    | none => .error .encaps1Failed
    | some (ct1, es, ss) =>
      .ok ((ct1.toList, es.toList, ss.toList), tape.drop SHARED_SECRET_SIZE)

/-- `encaps2` (`src/incremental_mlkem768.rs:71–79`), applying the issue-1275 fix-up before `K.encaps2`. -/
def encaps2 (K : MlKem) (ek : EncapsulationKey) (es : EncapsulationState) :
    Except StatesPanic Ciphertext2 := do
  let maybeFix ← potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es
  let es' := maybeFix.getD es
  match bytesToVector? ENCAPSULATION_STATE_SIZE es', bytesToVector? ENCAPSULATION_KEY_SIZE ek with
  | some esVec, some ekVec => .ok (K.encaps2 esVec ekVec).toList
  | _, _ => .error (.encaps2BadSize es'.length ek.length)

/-- `decaps` (`src/incremental_mlkem768.rs:158–171`). -/
def decaps (K : MlKem) (dk : DecapsulationKey) (ct1 : Ciphertext1) (ct2 : Ciphertext2) :
    Except StatesPanic Secret :=
  match bytesToVector? CIPHERTEXT1_SIZE ct1,
        bytesToVector? CIPHERTEXT2_SIZE ct2,
        bytesToVector? DECAPSULATION_KEY_SIZE dk with
  | some ct1Vec, some ct2Vec, some dkVec => .ok (K.decaps dkVec ct1Vec ct2Vec).toList
  | _, _, _ => .error (.decapsBadSize dk.length ct1.length ct2.length)

abbrev decapsulate := decaps

/-! ## Unchunked state machine (`src/v1/unchunked/{send_ek, send_ct}`) -/

def sckaKeyInfoPrefix : Bytes :=
  asciiBytes "Signal_PQCKA_V1_MLKEM768:SCKA Key"

namespace Unchunked

namespace SendCt

structure NoHeaderReceived (Au : AuthApi) where
  epoch : Epoch
  auth : Au.Authenticator
  deriving DecidableEq, Repr

structure HeaderReceived (Au : AuthApi) where
  epoch : Epoch
  auth : Au.Authenticator
  hdr : Header
  deriving DecidableEq, Repr

structure Ct1Sent (Au : AuthApi) where
  epoch : Epoch
  auth : Au.Authenticator
  hdr : Header
  es : EncapsulationState
  ct1 : Ciphertext1
  deriving DecidableEq, Repr

structure Ct1SentEkReceived (Au : AuthApi) where
  epoch : Epoch
  auth : Au.Authenticator
  es : EncapsulationState
  ek : EncapsulationKey
  ct1 : Ciphertext1
  deriving DecidableEq, Repr

structure Ct2Sent (Au : AuthApi) where
  epoch : Epoch
  auth : Au.Authenticator
  deriving DecidableEq, Repr

end SendCt

namespace SendEk

structure KeysUnsampled (Au : AuthApi) where
  epoch : Epoch
  auth : Au.Authenticator
  deriving DecidableEq, Repr

structure HeaderSent (Au : AuthApi) where
  epoch : Epoch
  auth : Au.Authenticator
  ek : EncapsulationKey
  dk : DecapsulationKey
  deriving DecidableEq, Repr

structure EkSent (Au : AuthApi) where
  epoch : Epoch
  auth : Au.Authenticator
  dk : DecapsulationKey
  deriving DecidableEq, Repr

structure EkSentCt1Received (Au : AuthApi) where
  epoch : Epoch
  auth : Au.Authenticator
  dk : DecapsulationKey
  ct1 : Ciphertext1
  deriving DecidableEq, Repr

namespace KeysUnsampled

def new (Au : AuthApi) (authKey : Bytes) : Except StatesPanic (KeysUnsampled Au) := do
  let auth ← Au.new authKey 1#64
  .ok { epoch := 1#64, auth := auth }

/-- `KeysUnsampled::send_header` (`src/v1/unchunked/send_ek.rs:84–100`). -/
def send_header (K : MlKem) {Au : AuthApi} (self : KeysUnsampled Au) (tape : Bytes) :
    Except StatesPanic (HeaderSent Au × Header × Mac × Bytes) := do
  let (keys, tape') ← generate K tape
  let mac ← Au.mac_hdr self.auth self.epoch keys.hdr
  .ok ({ epoch := self.epoch, auth := self.auth, ek := keys.ek, dk := keys.dk },
    keys.hdr, mac, tape')

def into_pb {Au : AuthApi} (self : KeysUnsampled Au) : V1State.Unchunked.KeysUnsampled :=
  { epoch := self.epoch, auth := some (Au.into_pb self.auth) }

abbrev intoPb := @into_pb

def from_pb (Au : AuthApi) (pb : V1State.Unchunked.KeysUnsampled) : StatesResult (KeysUnsampled Au) :=
  match pb.auth with
  | none => .error (.err .stateDecode)
  | some a => .ok { epoch := pb.epoch, auth := Au.from_pb a }

abbrev fromPb := from_pb

end KeysUnsampled

namespace HeaderSent

/-- `HeaderSent::send_ek` (`src/v1/unchunked/send_ek.rs:106–115`). -/
def send_ek {Au : AuthApi} (self : HeaderSent Au) : EkSent Au × EncapsulationKey :=
  ({ epoch := self.epoch, auth := self.auth, dk := self.dk }, self.ek)

def into_pb {Au : AuthApi} (self : HeaderSent Au) : V1State.Unchunked.HeaderSent :=
  { epoch := self.epoch, auth := some (Au.into_pb self.auth), ek := self.ek, dk := self.dk }

abbrev intoPb := @into_pb

def from_pb (Au : AuthApi) (pb : V1State.Unchunked.HeaderSent) : StatesResult (HeaderSent Au) :=
  if pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ek.length == ENCAPSULATION_KEY_SIZE then
    match pb.auth with
    | none => .error (.err .stateDecode)
    | some a => .ok { epoch := pb.epoch, auth := Au.from_pb a, ek := pb.ek, dk := pb.dk }
  else
    .error (.err .stateDecode)

abbrev fromPb := from_pb

end HeaderSent

namespace EkSent

/-- `EkSent::recv_ct1` (`src/v1/unchunked/send_ek.rs:121–133`). -/
def recv_ct1 {Au : AuthApi} (self : EkSent Au) (epoch : Epoch) (ct1 : Ciphertext1) :
    Except StatesPanic (EkSentCt1Received Au) :=
  if epoch != self.epoch then
    .error (.unchunkedRecvCt1EpochMismatch epoch self.epoch)
  else
    .ok { epoch := self.epoch, auth := self.auth, dk := self.dk, ct1 := ct1 }

def into_pb {Au : AuthApi} (self : EkSent Au) : V1State.Unchunked.EkSent :=
  { epoch := self.epoch, auth := some (Au.into_pb self.auth), dk := self.dk }

abbrev intoPb := @into_pb

def from_pb (Au : AuthApi) (pb : V1State.Unchunked.EkSent) : StatesResult (EkSent Au) :=
  if pb.dk.length == DECAPSULATION_KEY_SIZE then
    match pb.auth with
    | none => .error (.err .stateDecode)
    | some a => .ok { epoch := pb.epoch, auth := Au.from_pb a, dk := pb.dk }
  else
    .error (.err .stateDecode)

abbrev fromPb := from_pb

end EkSent

namespace EkSentCt1Received

/-- `EkSentCt1Received::recv_ct2` (`src/v1/unchunked/send_ek.rs:139–172`). -/
def recv_ct2 (K : MlKem) {Au : AuthApi} (self : EkSentCt1Received Au)
    (ct2 : Ciphertext2) (mac : Mac) : StatesResult (SendCt.NoHeaderReceived Au × EpochSecret) := do
  let ss ← StatesResult.ofPanic (decaps K self.dk self.ct1 ct2)
  let info := sckaKeyInfoPrefix ++ u64ToBeBytes self.epoch
  let ss ← StatesResult.ofPanic (Au.hkdf_to_vec (List.replicate 32 0#8) ss info 32)
  let auth ← StatesResult.ofPanic (Au.update self.auth self.epoch ss)
  let ct1Full := self.ct1 ++ ct2
  let verifyRes ← StatesResult.ofPanic (Au.verify_ct auth self.epoch ct1Full mac)
  match verifyRes with
  | .error _ => .error (.err .macVerifyFailed)
  | .ok () =>
    if self.epoch == BitVec.allOnes 64 then
      .error (.panic .unchunkedRecvCt2EpochOverflow)
    else
      .ok ({ epoch := self.epoch + 1#64, auth := auth },
        { epoch := self.epoch, secret := ss })

def into_pb {Au : AuthApi} (self : EkSentCt1Received Au) : V1State.Unchunked.EkSentCt1Received :=
  { epoch := self.epoch, auth := some (Au.into_pb self.auth), dk := self.dk, ct1 := self.ct1 }

abbrev intoPb := @into_pb

def from_pb (Au : AuthApi) (pb : V1State.Unchunked.EkSentCt1Received) :
    StatesResult (EkSentCt1Received Au) :=
  if pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE then
    match pb.auth with
    | none => .error (.err .stateDecode)
    | some a => .ok { epoch := pb.epoch, auth := Au.from_pb a, dk := pb.dk, ct1 := pb.ct1 }
  else
    .error (.err .stateDecode)

abbrev fromPb := from_pb

end EkSentCt1Received

end SendEk

namespace SendCt

namespace NoHeaderReceived

def new (Au : AuthApi) (authKey : Bytes) : Except StatesPanic (NoHeaderReceived Au) := do
  let auth ← Au.new authKey 1#64
  .ok { epoch := 1#64, auth := auth }

/-- `NoHeaderReceived::recv_header` (`src/v1/unchunked/send_ct.rs:100–113`). -/
def recv_header {Au : AuthApi} (self : NoHeaderReceived Au)
    (epoch : Epoch) (hdr : Header) (mac : Mac) : StatesResult (HeaderReceived Au) := do
  if epoch != self.epoch then
    .error (.panic (.unchunkedRecvHeaderEpochMismatch epoch self.epoch))
  else
    let verifyRes ← StatesResult.ofPanic (Au.verify_hdr self.auth self.epoch hdr mac)
    match verifyRes with
    | .error _ => .error (.err .macVerifyFailed)
    | .ok () => .ok { epoch := self.epoch, auth := self.auth, hdr := hdr }

def into_pb {Au : AuthApi} (self : NoHeaderReceived Au) : V1State.Unchunked.NoHeaderReceived :=
  { epoch := self.epoch, auth := some (Au.into_pb self.auth) }

abbrev intoPb := @into_pb

def from_pb (Au : AuthApi) (pb : V1State.Unchunked.NoHeaderReceived) :
    StatesResult (NoHeaderReceived Au) :=
  match pb.auth with
  | none => .error (.err .stateDecode)
  | some a => .ok { epoch := pb.epoch, auth := Au.from_pb a }

abbrev fromPb := from_pb

end NoHeaderReceived

namespace HeaderReceived

/-- `HeaderReceived::send_ct1` (`src/v1/unchunked/send_ct.rs:120–148`). -/
def send_ct1 (K : MlKem) {Au : AuthApi} (self : HeaderReceived Au) (tape : Bytes) :
    Except StatesPanic (Ct1Sent Au × Ciphertext1 × EpochSecret × Bytes) := do
  let ((ct1, es, secret), tape') ← encaps1 K self.hdr tape
  let info := sckaKeyInfoPrefix ++ u64ToBeBytes self.epoch
  let secret ← Au.hkdf_to_vec (List.replicate 32 0#8) secret info 32
  let auth ← Au.update self.auth self.epoch secret
  .ok ({ epoch := self.epoch, auth := auth, hdr := self.hdr, es := es, ct1 := ct1 },
    ct1, { epoch := self.epoch, secret := secret }, tape')

def into_pb {Au : AuthApi} (self : HeaderReceived Au) : V1State.Unchunked.HeaderReceived :=
  { epoch := self.epoch, auth := some (Au.into_pb self.auth), hdr := self.hdr }

abbrev intoPb := @into_pb

def from_pb (Au : AuthApi) (pb : V1State.Unchunked.HeaderReceived) :
    StatesResult (HeaderReceived Au) :=
  if pb.hdr.length == HEADER_SIZE then
    match pb.auth with
    | none => .error (.err .stateDecode)
    | some a => .ok { epoch := pb.epoch, auth := Au.from_pb a, hdr := pb.hdr }
  else
    .error (.err .stateDecode)

abbrev fromPb := from_pb

end HeaderReceived

namespace Ct1Sent

/-- `Ct1Sent::recv_ek` (`src/v1/unchunked/send_ct.rs:154–171`). -/
def recv_ek (K : MlKem) {Au : AuthApi} (self : Ct1Sent Au)
    (epoch : Epoch) (ek : EncapsulationKey) : StatesResult (Ct1SentEkReceived Au) :=
  if epoch != self.epoch then
    .error (.panic (.unchunkedRecvEkEpochMismatch epoch self.epoch))
  else if ek_matches_header K ek self.hdr then
    .ok { epoch := self.epoch, auth := self.auth, es := self.es, ek := ek, ct1 := self.ct1 }
  else
    .error (.err .erroneousDataReceived)

def into_pb {Au : AuthApi} (self : Ct1Sent Au) : V1State.Unchunked.Ct1Sent :=
  { epoch := self.epoch, auth := some (Au.into_pb self.auth),
    hdr := self.hdr, es := self.es, ct1 := self.ct1 }

abbrev intoPb := @into_pb

def from_pb (Au : AuthApi) (pb : V1State.Unchunked.Ct1Sent) : StatesResult (Ct1Sent Au) :=
  if pb.hdr.length == HEADER_SIZE &&
     pb.es.length == ENCAPSULATION_STATE_SIZE &&
     pb.ct1.length == CIPHERTEXT1_SIZE then
    match pb.auth with
    | none => .error (.err .stateDecode)
    | some a =>
      .ok { epoch := pb.epoch, auth := Au.from_pb a, hdr := pb.hdr, es := pb.es, ct1 := pb.ct1 }
  else
    .error (.err .stateDecode)

abbrev fromPb := from_pb

end Ct1Sent

namespace Ct1SentEkReceived

/-- `Ct1SentEkReceived::send_ct2` (`src/v1/unchunked/send_ct.rs:177–195`). -/
def send_ct2 (K : MlKem) {Au : AuthApi} (self : Ct1SentEkReceived Au) :
    Except StatesPanic (Ct2Sent Au × Ciphertext2 × Mac) := do
  let ct2 ← encaps2 K self.ek self.es
  let ct1Full := self.ct1 ++ ct2
  let mac ← Au.mac_ct self.auth self.epoch ct1Full
  .ok ({ epoch := self.epoch, auth := self.auth }, ct2, mac)

def into_pb {Au : AuthApi} (self : Ct1SentEkReceived Au) : V1State.Unchunked.Ct1SentEkReceived :=
  { epoch := self.epoch, auth := some (Au.into_pb self.auth),
    es := self.es, ek := self.ek, ct1 := self.ct1 }

abbrev intoPb := @into_pb

def from_pb (Au : AuthApi) (pb : V1State.Unchunked.Ct1SentEkReceived) :
    StatesResult (Ct1SentEkReceived Au) :=
  if pb.es.length == ENCAPSULATION_STATE_SIZE &&
     pb.ct1.length == CIPHERTEXT1_SIZE &&
     pb.ek.length == ENCAPSULATION_KEY_SIZE then
    match pb.auth with
    | none => .error (.err .stateDecode)
    | some a =>
      .ok { epoch := pb.epoch, auth := Au.from_pb a, es := pb.es, ek := pb.ek, ct1 := pb.ct1 }
  else
    .error (.err .stateDecode)

abbrev fromPb := from_pb

end Ct1SentEkReceived

namespace Ct2Sent

/-- `Ct2Sent::recv_next_epoch` (`src/v1/unchunked/send_ct.rs:201–208`). -/
def recv_next_epoch {Au : AuthApi} (self : Ct2Sent Au) (nextEpoch : Epoch) :
    Except StatesPanic (SendEk.KeysUnsampled Au) :=
  if self.epoch == BitVec.allOnes 64 then
    .error .unchunkedRecvNextEpochOverflow
  else
    let next := self.epoch + 1#64
    if next != nextEpoch then
      .error (.unchunkedRecvNextEpochMismatch next nextEpoch)
    else
      .ok { epoch := next, auth := self.auth }

def into_pb {Au : AuthApi} (self : Ct2Sent Au) : V1State.Unchunked.Ct2Sent :=
  { epoch := self.epoch, auth := some (Au.into_pb self.auth) }

abbrev intoPb := @into_pb

def from_pb (Au : AuthApi) (pb : V1State.Unchunked.Ct2Sent) : StatesResult (Ct2Sent Au) :=
  match pb.auth with
  | none => .error (.err .stateDecode)
  | some a => .ok { epoch := pb.epoch, auth := Au.from_pb a }

abbrev fromPb := from_pb

end Ct2Sent

end SendCt

end Unchunked

/-! ## Chunked braid state machine (`src/v1/chunked/{send_ek, send_ct}`) -/

def expectEncodeBytes (P : PolyApi) (site : String) (msg : Bytes) :
    Except StatesPanic P.PolyEncoder := do
  let res ← P.encode_bytes msg
  match res with
  | .ok enc => .ok enc
  | .error _ => .error (.polyExpectFailed site)

def expectDecoderNew (P : PolyApi) (site : String) (lenBytes : Nat) :
    Except StatesPanic P.PolyDecoder := do
  let res ← P.decoder_new lenBytes
  match res with
  | .ok dec => .ok dec
  | .error _ => .error (.polyExpectFailed site)

def encoderFromPbStateDecode (P : PolyApi) (pb? : Option PolynomialEncoder) :
    StatesResult P.PolyEncoder :=
  match pb? with
  | none => .error (.err .stateDecode)
  | some pb => do
    let res ← StatesResult.ofPanic (P.encoder_from_pb pb)
    match res with
    | .ok enc => .ok enc
    | .error _ => .error (.err .stateDecode)

def decoderFromPbStateDecode (P : PolyApi) (pb? : Option PolynomialDecoder) :
    StatesResult P.PolyDecoder :=
  match pb? with
  | none => .error (.err .stateDecode)
  | some pb => do
    let res ← StatesResult.ofPanic (P.decoder_from_pb pb)
    match res with
    | .ok dec => .ok dec
    | .error _ => .error (.err .stateDecode)

namespace Chunked

namespace SendCt

structure NoHeaderReceived (P : PolyApi) (Au : AuthApi) where
  uc : Unchunked.SendCt.NoHeaderReceived Au
  receiving_hdr : P.PolyDecoder
  deriving DecidableEq, Repr

structure HeaderReceived (P : PolyApi) (Au : AuthApi) where
  uc : Unchunked.SendCt.HeaderReceived Au
  receiving_ek : P.PolyDecoder
  deriving DecidableEq, Repr

structure Ct1Sampled (P : PolyApi) (Au : AuthApi) where
  uc : Unchunked.SendCt.Ct1Sent Au
  sending_ct1 : P.PolyEncoder
  receiving_ek : P.PolyDecoder
  deriving DecidableEq, Repr

structure EkReceivedCt1Sampled (P : PolyApi) (Au : AuthApi) where
  uc : Unchunked.SendCt.Ct1SentEkReceived Au
  sending_ct1 : P.PolyEncoder
  deriving DecidableEq, Repr

structure Ct1Acknowledged (P : PolyApi) (Au : AuthApi) where
  uc : Unchunked.SendCt.Ct1Sent Au
  receiving_ek : P.PolyDecoder
  deriving DecidableEq, Repr

structure Ct2Sampled (P : PolyApi) (Au : AuthApi) where
  uc : Unchunked.SendCt.Ct2Sent Au
  sending_ct2 : P.PolyEncoder
  deriving DecidableEq, Repr

end SendCt

namespace SendEk

structure KeysUnsampled (Au : AuthApi) where
  uc : Unchunked.SendEk.KeysUnsampled Au
  deriving DecidableEq, Repr

structure KeysSampled (P : PolyApi) (Au : AuthApi) where
  uc : Unchunked.SendEk.HeaderSent Au
  sending_hdr : P.PolyEncoder
  deriving DecidableEq, Repr

structure HeaderSent (P : PolyApi) (Au : AuthApi) where
  uc : Unchunked.SendEk.EkSent Au
  sending_ek : P.PolyEncoder
  receiving_ct1 : P.PolyDecoder
  deriving DecidableEq, Repr

structure Ct1Received (P : PolyApi) (Au : AuthApi) where
  uc : Unchunked.SendEk.EkSentCt1Received Au
  sending_ek : P.PolyEncoder
  deriving DecidableEq, Repr

structure EkSentCt1Received (P : PolyApi) (Au : AuthApi) where
  uc : Unchunked.SendEk.EkSentCt1Received Au
  receiving_ct2 : P.PolyDecoder
  deriving DecidableEq, Repr

inductive HeaderSentRecvChunk (P : PolyApi) (Au : AuthApi) where
  | stillReceiving (s : HeaderSent P Au)
  | done (s : Ct1Received P Au)
  deriving DecidableEq, Repr

inductive EkSentCt1ReceivedRecvChunk (P : PolyApi) (Au : AuthApi) where
  | stillReceiving (s : EkSentCt1Received P Au)
  | done (res : SendCt.NoHeaderReceived P Au × EpochSecret)
  deriving DecidableEq, Repr

namespace KeysUnsampled

def new (Au : AuthApi) (authKey : Bytes) : Except StatesPanic (KeysUnsampled Au) := do
  let uc ← Unchunked.SendEk.KeysUnsampled.new Au authKey
  .ok { uc := uc }

def epoch {Au : AuthApi} (self : KeysUnsampled Au) : Epoch := self.uc.epoch

/-- `KeysUnsampled::send_hdr_chunk` (`src/v1/chunked/send_ek.rs:59–66`). -/
def send_hdr_chunk (K : MlKem) (P : PolyApi) {Au : AuthApi}
    (self : KeysUnsampled Au) (tape : Bytes) :
    Except StatesPanic (KeysSampled P Au × P.Chunk × Bytes) := do
  let (uc, toSend, mac, tape') ← self.uc.send_header K tape
  let toSendFull := toSend ++ mac
  let sendingHdr ← expectEncodeBytes P "v1/chunked/send_ek.rs:63" toSendFull
  let (sendingHdr, chunk) ← P.next_chunk sendingHdr
  .ok ({ uc := uc, sending_hdr := sendingHdr }, chunk, tape')

def into_pb {Au : AuthApi} (self : KeysUnsampled Au) : V1State.Chunked.KeysUnsampled :=
  { uc := some self.uc.into_pb }

abbrev intoPb := @into_pb

def from_pb (Au : AuthApi) (pb : V1State.Chunked.KeysUnsampled) : StatesResult (KeysUnsampled Au) :=
  match pb.uc with
  | none => .error (.err .stateDecode)
  | some u => do
    let uc ← Unchunked.SendEk.KeysUnsampled.from_pb Au u
    .ok { uc := uc }

abbrev fromPb := from_pb

end KeysUnsampled

namespace KeysSampled

def epoch {P : PolyApi} {Au : AuthApi} (self : KeysSampled P Au) : Epoch := self.uc.epoch

def send_hdr_chunk {P : PolyApi} {Au : AuthApi} (self : KeysSampled P Au) :
    Except StatesPanic (KeysSampled P Au × P.Chunk) := do
  let (sendingHdr, chunk) ← P.next_chunk self.sending_hdr
  .ok ({ uc := self.uc, sending_hdr := sendingHdr }, chunk)

/-- `KeysSampled::recv_ct1_chunk` (`src/v1/chunked/send_ek.rs:85–98`). -/
def recv_ct1_chunk {P : PolyApi} {Au : AuthApi} (self : KeysSampled P Au)
    (epoch : Epoch) (chunk : P.Chunk) : Except StatesPanic (HeaderSent P Au) := do
  if epoch != self.uc.epoch then
    .error (.chunkedEpochMismatch "v1/chunked/send_ek.rs:86" epoch self.uc.epoch)
  else
    let receivingCt1 ← expectDecoderNew P "v1/chunked/send_ek.rs:88" CIPHERTEXT1_SIZE
    let receivingCt1 ← P.add_chunk receivingCt1 chunk
    let (uc, ek) := self.uc.send_ek
    let sendingEk ← expectEncodeBytes P "v1/chunked/send_ek.rs:92" ek
    .ok { uc := uc, sending_ek := sendingEk, receiving_ct1 := receivingCt1 }

def into_pb {P : PolyApi} {Au : AuthApi} (self : KeysSampled P Au) : V1State.Chunked.KeysSampled :=
  { uc := some self.uc.into_pb, sendingHdr := some (P.encoder_into_pb self.sending_hdr) }

abbrev intoPb := @into_pb

def from_pb (P : PolyApi) (Au : AuthApi) (pb : V1State.Chunked.KeysSampled) :
    StatesResult (KeysSampled P Au) := do
  let u ← match pb.uc with
    | none => .error (.err .stateDecode)
    | some u => .ok u
  let uc ← Unchunked.SendEk.HeaderSent.from_pb Au u
  let sendingHdr ← encoderFromPbStateDecode P pb.sendingHdr
  .ok { uc := uc, sending_hdr := sendingHdr }

abbrev fromPb := from_pb

end KeysSampled

namespace HeaderSent

def epoch {P : PolyApi} {Au : AuthApi} (self : HeaderSent P Au) : Epoch := self.uc.epoch

def send_ek_chunk {P : PolyApi} {Au : AuthApi} (self : HeaderSent P Au) :
    Except StatesPanic (HeaderSent P Au × P.Chunk) := do
  let (sendingEk, chunk) ← P.next_chunk self.sending_ek
  .ok ({ uc := self.uc, sending_ek := sendingEk, receiving_ct1 := self.receiving_ct1 }, chunk)

/-- `HeaderSent::recv_ct1_chunk` (`src/v1/chunked/send_ek.rs:131–149`). -/
def recv_ct1_chunk {P : PolyApi} {Au : AuthApi} (self : HeaderSent P Au)
    (epoch : Epoch) (chunk : P.Chunk) : Except StatesPanic (HeaderSentRecvChunk P Au) := do
  if epoch != self.uc.epoch then
    .error (.chunkedEpochMismatch "v1/chunked/send_ek.rs:132" epoch self.uc.epoch)
  else
    let receivingCt1 ← P.add_chunk self.receiving_ct1 chunk
    let decoded? ← P.decoded_message receivingCt1
    match decoded? with
    | some decoded =>
      let uc ← self.uc.recv_ct1 epoch decoded
      .ok (.done { uc := uc, sending_ek := self.sending_ek })
    | none =>
      .ok (.stillReceiving
        { uc := self.uc, sending_ek := self.sending_ek, receiving_ct1 := receivingCt1 })

def into_pb {P : PolyApi} {Au : AuthApi} (self : HeaderSent P Au) : V1State.Chunked.HeaderSent :=
  { uc := some self.uc.into_pb,
    sendingEk := some (P.encoder_into_pb self.sending_ek),
    receivingCt1 := some (P.decoder_into_pb self.receiving_ct1) }

abbrev intoPb := @into_pb

/-- `HeaderSent::from_pb` (`src/v1/chunked/send_ek/serialize.rs:52–67`; returns `MsgDecode` if
`receiving_ct1.pts_needed != 480`). -/
def from_pb (P : PolyApi) (Au : AuthApi) (pb : V1State.Chunked.HeaderSent) :
    StatesResult (HeaderSent P Au) := do
  match pb.receivingCt1 with
  | some d =>
    if d.ptsNeeded.toNat != CIPHERTEXT1_SIZE / 2 then
      .error (.err .msgDecode)
    else
      .ok ()
  | none => .ok ()
  let u ← match pb.uc with
    | none => .error (.err .stateDecode)
    | some u => .ok u
  let uc ← Unchunked.SendEk.EkSent.from_pb Au u
  let sendingEk ← encoderFromPbStateDecode P pb.sendingEk
  let receivingCt1 ← decoderFromPbStateDecode P pb.receivingCt1
  .ok { uc := uc, sending_ek := sendingEk, receiving_ct1 := receivingCt1 }

abbrev fromPb := from_pb

end HeaderSent

namespace Ct1Received

def epoch {P : PolyApi} {Au : AuthApi} (self : Ct1Received P Au) : Epoch := self.uc.epoch

def send_ek_chunk {P : PolyApi} {Au : AuthApi} (self : Ct1Received P Au) :
    Except StatesPanic (Ct1Received P Au × P.Chunk) := do
  let (sendingEk, chunk) ← P.next_chunk self.sending_ek
  .ok ({ uc := self.uc, sending_ek := sendingEk }, chunk)

/-- `Ct1Received::recv_ct2_chunk` (`src/v1/chunked/send_ek.rs:165–180`). -/
def recv_ct2_chunk {P : PolyApi} {Au : AuthApi} (self : Ct1Received P Au)
    (epoch : Epoch) (chunk : P.Chunk) : Except StatesPanic (EkSentCt1Received P Au) := do
  if epoch != self.uc.epoch then
    .error (.chunkedEpochMismatch "v1/chunked/send_ek.rs:166" epoch self.uc.epoch)
  else
    let receivingCt2 ←
      expectDecoderNew P "v1/chunked/send_ek.rs:174" (CIPHERTEXT2_SIZE + AUTHENTICATOR_MACSIZE)
    let receivingCt2 ← P.add_chunk receivingCt2 chunk
    .ok { uc := self.uc, receiving_ct2 := receivingCt2 }

def into_pb {P : PolyApi} {Au : AuthApi} (self : Ct1Received P Au) : V1State.Chunked.Ct1Received :=
  { uc := some self.uc.into_pb, sendingEk := some (P.encoder_into_pb self.sending_ek) }

abbrev intoPb := @into_pb

def from_pb (P : PolyApi) (Au : AuthApi) (pb : V1State.Chunked.Ct1Received) :
    StatesResult (Ct1Received P Au) := do
  let u ← match pb.uc with
    | none => .error (.err .stateDecode)
    | some u => .ok u
  let uc ← Unchunked.SendEk.EkSentCt1Received.from_pb Au u
  let sendingEk ← encoderFromPbStateDecode P pb.sendingEk
  .ok { uc := uc, sending_ek := sendingEk }

abbrev fromPb := from_pb

end Ct1Received

namespace EkSentCt1Received

def epoch {P : PolyApi} {Au : AuthApi} (self : EkSentCt1Received P Au) : Epoch := self.uc.epoch

/-- `EkSentCt1Received::recv_ct2_chunk` (`src/v1/chunked/send_ek.rs:195–227`). -/
def recv_ct2_chunk (K : MlKem) {P : PolyApi} {Au : AuthApi} (self : EkSentCt1Received P Au)
    (epoch : Epoch) (chunk : P.Chunk) : StatesResult (EkSentCt1ReceivedRecvChunk P Au) := do
  if epoch != self.uc.epoch then
    .error (.panic (.chunkedEpochMismatch "v1/chunked/send_ek.rs:200" epoch self.uc.epoch))
  else
    let receivingCt2 ← StatesResult.ofPanic (P.add_chunk self.receiving_ct2 chunk)
    let decoded? ← StatesResult.ofPanic (P.decoded_message receivingCt2)
    match decoded? with
    | some ct2Full =>
      if ct2Full.length < CIPHERTEXT2_SIZE then
        .error (.panic (.decodedSliceBounds "v1/chunked/send_ek.rs:209" ct2Full.length CIPHERTEXT2_SIZE))
      else
        let mac := ct2Full.drop CIPHERTEXT2_SIZE
        let ct2 := ct2Full.take CIPHERTEXT2_SIZE
        let (uc, sec) ← self.uc.recv_ct2 K ct2 mac
        let receivingHdr ← StatesResult.ofPanic
          (expectDecoderNew P "v1/chunked/send_ek.rs:218" (HEADER_SIZE + AUTHENTICATOR_MACSIZE))
        .ok (.done ({ uc := uc, receiving_hdr := receivingHdr }, sec))
    | none =>
      .ok (.stillReceiving { uc := self.uc, receiving_ct2 := receivingCt2 })

def into_pb {P : PolyApi} {Au : AuthApi} (self : EkSentCt1Received P Au) :
    V1State.Chunked.EkSentCt1Received :=
  { uc := some self.uc.into_pb, receivingCt2 := some (P.decoder_into_pb self.receiving_ct2) }

abbrev intoPb := @into_pb

/-- `EkSentCt1Received::from_pb` (`src/v1/chunked/send_ek/serialize.rs:95–111`; returns `MsgDecode`
if `receiving_ct2.pts_needed != 80`). -/
def from_pb (P : PolyApi) (Au : AuthApi) (pb : V1State.Chunked.EkSentCt1Received) :
    StatesResult (EkSentCt1Received P Au) := do
  match pb.receivingCt2 with
  | some d =>
    if d.ptsNeeded.toNat != (CIPHERTEXT2_SIZE + AUTHENTICATOR_MACSIZE) / 2 then
      .error (.err .msgDecode)
    else
      .ok ()
  | none => .ok ()
  let u ← match pb.uc with
    | none => .error (.err .stateDecode)
    | some u => .ok u
  let uc ← Unchunked.SendEk.EkSentCt1Received.from_pb Au u
  let receivingCt2 ← decoderFromPbStateDecode P pb.receivingCt2
  .ok { uc := uc, receiving_ct2 := receivingCt2 }

abbrev fromPb := from_pb

end EkSentCt1Received

end SendEk

namespace SendCt

inductive NoHeaderReceivedRecvChunk (P : PolyApi) (Au : AuthApi) where
  | stillReceiving (s : NoHeaderReceived P Au)
  | done (s : HeaderReceived P Au)
  deriving DecidableEq, Repr

inductive Ct1SampledRecvChunk (P : PolyApi) (Au : AuthApi) where
  | stillReceivingStillSending (s : Ct1Sampled P Au)
  | stillReceiving (s : Ct1Acknowledged P Au)
  | stillSending (s : EkReceivedCt1Sampled P Au)
  | done (s : Ct2Sampled P Au)
  deriving DecidableEq, Repr

inductive Ct1AcknowledgedRecvChunk (P : PolyApi) (Au : AuthApi) where
  | stillReceiving (s : Ct1Acknowledged P Au)
  | done (s : Ct2Sampled P Au)
  deriving DecidableEq, Repr

def send_ct2_encoder (P : PolyApi) (ct2 mac : Bytes) : Except StatesPanic P.PolyEncoder :=
  expectEncodeBytes P "v1/chunked/send_ct.rs:162" (ct2 ++ mac)

abbrev sendCt2Encoder := send_ct2_encoder

namespace NoHeaderReceived

/-- `NoHeaderReceived::new` (`src/v1/chunked/send_ct.rs:71–79`), preserving Rust evaluation order:
`PolyDecoder::new`, `unchunked::NoHeaderReceived::new`, then `decoder.expect(...)`. -/
def new (P : PolyApi) (Au : AuthApi) (authKey : Bytes) :
    Except StatesPanic (NoHeaderReceived P Au) := do
  let decoderRes ← P.decoder_new (HEADER_SIZE + AUTHENTICATOR_MACSIZE)
  let uc ← Unchunked.SendCt.NoHeaderReceived.new Au authKey
  match decoderRes with
  | .ok decoder => .ok { uc := uc, receiving_hdr := decoder }
  | .error _ => .error (.polyExpectFailed "v1/chunked/send_ct.rs:77")

def epoch {P : PolyApi} {Au : AuthApi} (self : NoHeaderReceived P Au) : Epoch := self.uc.epoch

/-- `NoHeaderReceived::recv_hdr_chunk` (`src/v1/chunked/send_ct.rs:82–110`). -/
def recv_hdr_chunk {P : PolyApi} {Au : AuthApi} (self : NoHeaderReceived P Au)
    (epoch : Epoch) (chunk : P.Chunk) : StatesResult (NoHeaderReceivedRecvChunk P Au) := do
  if epoch != self.uc.epoch then
    .error (.panic (.chunkedEpochMismatch "v1/chunked/send_ct.rs:87" epoch self.uc.epoch))
  else
    let receivingHdr ← StatesResult.ofPanic (P.add_chunk self.receiving_hdr chunk)
    let decoded? ← StatesResult.ofPanic (P.decoded_message receivingHdr)
    match decoded? with
    | some hdrFull =>
      if hdrFull.length < HEADER_SIZE then
        .error (.panic (.decodedSliceBounds "v1/chunked/send_ct.rs:96" hdrFull.length HEADER_SIZE))
      else
        let mac := hdrFull.drop HEADER_SIZE
        let hdr := hdrFull.take HEADER_SIZE
        let receivingEkRes ← StatesResult.ofPanic (P.decoder_new ENCAPSULATION_KEY_SIZE)
        let uc ← self.uc.recv_header epoch hdr mac
        match receivingEkRes with
        | .ok receivingEk =>
          .ok (.done { uc := uc, receiving_ek := receivingEk })
        | .error _ =>
          .error (.panic (.polyExpectFailed "v1/chunked/send_ct.rs:102"))
    | none =>
      .ok (.stillReceiving { uc := self.uc, receiving_hdr := receivingHdr })

def into_pb {P : PolyApi} {Au : AuthApi} (self : NoHeaderReceived P Au) :
    V1State.Chunked.NoHeaderReceived :=
  { uc := some self.uc.into_pb, receivingHdr := some (P.decoder_into_pb self.receiving_hdr) }

abbrev intoPb := @into_pb

def from_pb (P : PolyApi) (Au : AuthApi) (pb : V1State.Chunked.NoHeaderReceived) :
    StatesResult (NoHeaderReceived P Au) := do
  match pb.receivingHdr with
  | some rhdr =>
    if rhdr.ptsNeeded != BitVec.ofNat 32 ((HEADER_SIZE + AUTHENTICATOR_MACSIZE) / 2) then
      .error (.err .msgDecode)
    else
      .ok ()
  | none => .ok ()
  let u ← match pb.uc with
    | none => .error (.err .stateDecode)
    | some u => .ok u
  let uc ← Unchunked.SendCt.NoHeaderReceived.from_pb Au u
  let receivingHdr ← decoderFromPbStateDecode P pb.receivingHdr
  .ok { uc := uc, receiving_hdr := receivingHdr }

abbrev fromPb := from_pb

end NoHeaderReceived

namespace HeaderReceived

def epoch {P : PolyApi} {Au : AuthApi} (self : HeaderReceived P Au) : Epoch := self.uc.epoch

/-- `HeaderReceived::send_ct1_chunk` (`src/v1/chunked/send_ct.rs:123–142`). -/
def send_ct1_chunk (K : MlKem) {P : PolyApi} {Au : AuthApi}
    (self : HeaderReceived P Au) (tape : Bytes) :
    Except StatesPanic (Ct1Sampled P Au × P.Chunk × EpochSecret × Bytes) := do
  let (uc, ct1, epochSecret, tape') ← self.uc.send_ct1 K tape
  let sendingCt1 ← expectEncodeBytes P "v1/chunked/send_ct.rs:131" ct1
  let (sendingCt1, chunk) ← P.next_chunk sendingCt1
  .ok ({ uc := uc, sending_ct1 := sendingCt1, receiving_ek := self.receiving_ek },
    chunk, epochSecret, tape')

def into_pb {P : PolyApi} {Au : AuthApi} (self : HeaderReceived P Au) :
    V1State.Chunked.HeaderReceived :=
  { uc := some self.uc.into_pb, receivingEk := some (P.decoder_into_pb self.receiving_ek) }

abbrev intoPb := @into_pb

def from_pb (P : PolyApi) (Au : AuthApi) (pb : V1State.Chunked.HeaderReceived) :
    StatesResult (HeaderReceived P Au) := do
  match pb.receivingEk with
  | some d =>
    if d.ptsNeeded.toNat != ENCAPSULATION_KEY_SIZE / 2 then
      .error (.err .msgDecode)
    else
      .ok ()
  | none => .ok ()
  let u ← match pb.uc with
    | none => .error (.err .stateDecode)
    | some u => .ok u
  let uc ← Unchunked.SendCt.HeaderReceived.from_pb Au u
  let receivingEk ← decoderFromPbStateDecode P pb.receivingEk
  .ok { uc := uc, receiving_ek := receivingEk }

abbrev fromPb := from_pb

end HeaderReceived

namespace Ct1Sampled

def epoch {P : PolyApi} {Au : AuthApi} (self : Ct1Sampled P Au) : Epoch := self.uc.epoch

/-- `Ct1Sampled::recv_ek_chunk` (`src/v1/chunked/send_ct.rs:168–200`; no chunk-level epoch assert). -/
def recv_ek_chunk (K : MlKem) {P : PolyApi} {Au : AuthApi} (self : Ct1Sampled P Au)
    (epoch : Epoch) (chunk : P.Chunk) (ct1Ack : Bool) :
    StatesResult (Ct1SampledRecvChunk P Au) := do
  let receivingEk ← StatesResult.ofPanic (P.add_chunk self.receiving_ek chunk)
  let decoded? ← StatesResult.ofPanic (P.decoded_message receivingEk)
  match decoded? with
  | some decoded =>
    let uc ← self.uc.recv_ek K epoch decoded
    if ct1Ack then
      let (uc, ct2, mac) ← StatesResult.ofPanic (uc.send_ct2 K)
      let sendingCt2 ← StatesResult.ofPanic (send_ct2_encoder P ct2 mac)
      .ok (.done { uc := uc, sending_ct2 := sendingCt2 })
    else
      .ok (.stillSending { uc := uc, sending_ct1 := self.sending_ct1 })
  | none =>
    if ct1Ack then
      .ok (.stillReceiving { uc := self.uc, receiving_ek := receivingEk })
    else
      .ok (.stillReceivingStillSending
        { uc := self.uc, sending_ct1 := self.sending_ct1, receiving_ek := receivingEk })

def send_ct1_chunk {P : PolyApi} {Au : AuthApi} (self : Ct1Sampled P Au) :
    Except StatesPanic (Ct1Sampled P Au × P.Chunk) := do
  let (sendingCt1, chunk) ← P.next_chunk self.sending_ct1
  .ok ({ uc := self.uc, sending_ct1 := sendingCt1, receiving_ek := self.receiving_ek }, chunk)

def into_pb {P : PolyApi} {Au : AuthApi} (self : Ct1Sampled P Au) : V1State.Chunked.Ct1Sampled :=
  { uc := some self.uc.into_pb,
    sendingCt1 := some (P.encoder_into_pb self.sending_ct1),
    receivingEk := some (P.decoder_into_pb self.receiving_ek) }

abbrev intoPb := @into_pb

def from_pb (P : PolyApi) (Au : AuthApi) (pb : V1State.Chunked.Ct1Sampled) :
    StatesResult (Ct1Sampled P Au) := do
  match pb.receivingEk with
  | some d =>
    if d.ptsNeeded.toNat != ENCAPSULATION_KEY_SIZE / 2 then
      .error (.err .msgDecode)
    else
      .ok ()
  | none => .ok ()
  let u ← match pb.uc with
    | none => .error (.err .stateDecode)
    | some u => .ok u
  let uc ← Unchunked.SendCt.Ct1Sent.from_pb Au u
  let sendingCt1 ← encoderFromPbStateDecode P pb.sendingCt1
  let receivingEk ← decoderFromPbStateDecode P pb.receivingEk
  .ok { uc := uc, sending_ct1 := sendingCt1, receiving_ek := receivingEk }

abbrev fromPb := from_pb

end Ct1Sampled

namespace EkReceivedCt1Sampled

def epoch {P : PolyApi} {Au : AuthApi} (self : EkReceivedCt1Sampled P Au) : Epoch := self.uc.epoch

def send_ct1_chunk {P : PolyApi} {Au : AuthApi} (self : EkReceivedCt1Sampled P Au) :
    Except StatesPanic (EkReceivedCt1Sampled P Au × P.Chunk) := do
  let (sendingCt1, chunk) ← P.next_chunk self.sending_ct1
  .ok ({ uc := self.uc, sending_ct1 := sendingCt1 }, chunk)

/-- `EkReceivedCt1Sampled::recv_ct1_ack` (`src/v1/chunked/send_ct.rs:236–243`). -/
def recv_ct1_ack (K : MlKem) {P : PolyApi} {Au : AuthApi}
    (self : EkReceivedCt1Sampled P Au) (epoch : Epoch) :
    Except StatesPanic (Ct2Sampled P Au) := do
  if epoch != self.uc.epoch then
    .error (.chunkedEpochMismatch "v1/chunked/send_ct.rs:237" epoch self.uc.epoch)
  else
    let (uc, ct2, mac) ← self.uc.send_ct2 K
    let sendingCt2 ← send_ct2_encoder P ct2 mac
    .ok { uc := uc, sending_ct2 := sendingCt2 }

def into_pb {P : PolyApi} {Au : AuthApi} (self : EkReceivedCt1Sampled P Au) :
    V1State.Chunked.EkReceivedCt1Sampled :=
  { uc := some self.uc.into_pb, sendingCt1 := some (P.encoder_into_pb self.sending_ct1) }

abbrev intoPb := @into_pb

def from_pb (P : PolyApi) (Au : AuthApi) (pb : V1State.Chunked.EkReceivedCt1Sampled) :
    StatesResult (EkReceivedCt1Sampled P Au) := do
  let u ← match pb.uc with
    | none => .error (.err .stateDecode)
    | some u => .ok u
  let uc ← Unchunked.SendCt.Ct1SentEkReceived.from_pb Au u
  let sendingCt1 ← encoderFromPbStateDecode P pb.sendingCt1
  .ok { uc := uc, sending_ct1 := sendingCt1 }

abbrev fromPb := from_pb

end EkReceivedCt1Sampled

namespace Ct1Acknowledged

def epoch {P : PolyApi} {Au : AuthApi} (self : Ct1Acknowledged P Au) : Epoch := self.uc.epoch

/-- `Ct1Acknowledged::recv_ek_chunk` (`src/v1/chunked/send_ct.rs:259–279`; no chunk-level epoch assert). -/
def recv_ek_chunk (K : MlKem) {P : PolyApi} {Au : AuthApi} (self : Ct1Acknowledged P Au)
    (epoch : Epoch) (chunk : P.Chunk) : StatesResult (Ct1AcknowledgedRecvChunk P Au) := do
  let receivingEk ← StatesResult.ofPanic (P.add_chunk self.receiving_ek chunk)
  let decoded? ← StatesResult.ofPanic (P.decoded_message receivingEk)
  match decoded? with
  | some decoded =>
    let uc ← self.uc.recv_ek K epoch decoded
    let (uc, ct2, mac) ← StatesResult.ofPanic (uc.send_ct2 K)
    let sendingCt2 ← StatesResult.ofPanic (send_ct2_encoder P ct2 mac)
    .ok (.done { uc := uc, sending_ct2 := sendingCt2 })
  | none =>
    .ok (.stillReceiving { uc := self.uc, receiving_ek := receivingEk })

def into_pb {P : PolyApi} {Au : AuthApi} (self : Ct1Acknowledged P Au) :
    V1State.Chunked.Ct1Acknowledged :=
  { uc := some self.uc.into_pb, receivingEk := some (P.decoder_into_pb self.receiving_ek) }

abbrev intoPb := @into_pb

def from_pb (P : PolyApi) (Au : AuthApi) (pb : V1State.Chunked.Ct1Acknowledged) :
    StatesResult (Ct1Acknowledged P Au) := do
  match pb.receivingEk with
  | some d =>
    if d.ptsNeeded.toNat != ENCAPSULATION_KEY_SIZE / 2 then
      .error (.err .msgDecode)
    else
      .ok ()
  | none => .ok ()
  let u ← match pb.uc with
    | none => .error (.err .stateDecode)
    | some u => .ok u
  let uc ← Unchunked.SendCt.Ct1Sent.from_pb Au u
  let receivingEk ← decoderFromPbStateDecode P pb.receivingEk
  .ok { uc := uc, receiving_ek := receivingEk }

abbrev fromPb := from_pb

end Ct1Acknowledged

namespace Ct2Sampled

def epoch {P : PolyApi} {Au : AuthApi} (self : Ct2Sampled P Au) : Epoch := self.uc.epoch

def send_ct2_chunk {P : PolyApi} {Au : AuthApi} (self : Ct2Sampled P Au) :
    Except StatesPanic (Ct2Sampled P Au × P.Chunk) := do
  let (sendingCt2, chunk) ← P.next_chunk self.sending_ct2
  .ok ({ uc := self.uc, sending_ct2 := sendingCt2 }, chunk)

def recv_next_epoch {P : PolyApi} {Au : AuthApi} (self : Ct2Sampled P Au) (epoch : Epoch) :
    Except StatesPanic (SendEk.KeysUnsampled Au) := do
  let uc ← self.uc.recv_next_epoch epoch
  .ok { uc := uc }

def into_pb {P : PolyApi} {Au : AuthApi} (self : Ct2Sampled P Au) : V1State.Chunked.Ct2Sampled :=
  { uc := some self.uc.into_pb, sendingCt2 := some (P.encoder_into_pb self.sending_ct2) }

abbrev intoPb := @into_pb

def from_pb (P : PolyApi) (Au : AuthApi) (pb : V1State.Chunked.Ct2Sampled) :
    StatesResult (Ct2Sampled P Au) := do
  let u ← match pb.uc with
    | none => .error (.err .stateDecode)
    | some u => .ok u
  let uc ← Unchunked.SendCt.Ct2Sent.from_pb Au u
  let sendingCt2 ← encoderFromPbStateDecode P pb.sendingCt2
  .ok { uc := uc, sending_ct2 := sendingCt2 }

abbrev fromPb := from_pb

end Ct2Sampled

end SendCt

end Chunked

/-! ## Top-level `States` and `Message` (`src/v1/chunked/states.rs`) -/

/-- SCKA message payload (`pub enum MessagePayload`, `src/v1/chunked/states.rs:31–39`). -/
inductive MessagePayload (P : PolyApi) where
  | none
  | hdr (c : P.Chunk)
  | ek (c : P.Chunk)
  | ekCt1Ack (c : P.Chunk)
  | ct1Ack (b : Bool)
  | ct1 (c : P.Chunk)
  | ct2 (c : P.Chunk)
  deriving DecidableEq, Repr, Inhabited

/-- SCKA message (`pub struct Message`, `src/v1/chunked/states.rs:41–44`). -/
structure Message (P : PolyApi) where
  epoch : Epoch
  payload : MessagePayload P
  deriving DecidableEq, Repr, Inhabited

/-- One-byte wire tag of `MessagePayload` (`enum MessageType`, `src/v1/chunked/states/serialize.rs:95–103`). -/
inductive MessageType where
  | none
  | hdr
  | ek
  | ekCt1Ack
  | ct1Ack
  | ct1
  | ct2
  deriving DecidableEq, Repr, Inhabited

namespace MessageType

def toU8 : MessageType → BitVec 8
  | .none => 0#8
  | .hdr => 1#8
  | .ek => 2#8
  | .ekCt1Ack => 3#8
  | .ct1Ack => 4#8
  | .ct1 => 5#8
  | .ct2 => 6#8

def tryFromU8 (v : BitVec 8) : Option MessageType :=
  if v == 0#8 then some .none
  else if v == 1#8 then some .hdr
  else if v == 2#8 then some .ek
  else if v == 3#8 then some .ekCt1Ack
  else if v == 4#8 then some .ct1Ack
  else if v == 5#8 then some .ct1
  else if v == 6#8 then some .ct2
  else Option.none

def from_payload {P : PolyApi} : MessagePayload P → MessageType
  | .none => .none
  | .hdr _ => .hdr
  | .ek _ => .ek
  | .ekCt1Ack _ => .ekCt1Ack
  | .ct1Ack _ => .ct1Ack
  | .ct1 _ => .ct1
  | .ct2 _ => .ct2

end MessageType

def encode_chunk {P : PolyApi} (c : P.Chunk) (into : SerializedMessage := []) : SerializedMessage :=
  encode_varint ((P.chunkIndex c).zeroExtend 64) into ++ (P.chunkData c).toList

def decode_chunk (P : PolyApi) (fromSlice : Bytes) : Except Error (P.Chunk × Bytes) := do
  let (index, rest) ← decode_varint fromSlice
  if rest.length < 32 || index.toNat > 65535 then
    .error .msgDecode
  else
    match bytesToVector? 32 (rest.take 32) with
    | some dataVec => .ok (P.mkChunk (index.truncate 16) dataVec, rest.drop 32)
    | none => .error .msgDecode

namespace Message

/-- `Message::serialize` (`src/v1/chunked/states/serialize.rs:172–197`). -/
def serialize {P : PolyApi} (self : Message P) (index : BitVec 32) : SerializedMessage :=
  let into : SerializedMessage := [1#8]
  let into := encode_varint self.epoch into
  let into := encode_varint (index.zeroExtend 64) into
  let into := into ++ [(MessageType.from_payload self.payload).toU8]
  match self.payload with
  | .hdr chunk | .ek chunk | .ekCt1Ack chunk | .ct1 chunk | .ct2 chunk =>
    encode_chunk chunk into
  | .none | .ct1Ack _ =>
    into

/-- `Message::deserialize` (`src/v1/chunked/states/serialize.rs:200–219`). -/
def deserialize (P : PolyApi) (epoch : Epoch) (fromBytes : Bytes) : Except Error (Message P) :=
  match fromBytes with
  | [] => .error .msgDecode
  | b0 :: rest =>
    match MessageType.tryFromU8 b0 with
    | Option.none => .error .msgDecode
    | some msgType => do
      let payload ← match msgType with
        | .none => .ok MessagePayload.none
        | .ct1Ack => .ok (MessagePayload.ct1Ack true)
        | .hdr => do
          let (c, _) ← decode_chunk P rest
          .ok (MessagePayload.hdr c)
        | .ek => do
          let (c, _) ← decode_chunk P rest
          .ok (MessagePayload.ek c)
        | .ekCt1Ack => do
          let (c, _) ← decode_chunk P rest
          .ok (MessagePayload.ekCt1Ack c)
        | .ct1 => do
          let (c, _) ← decode_chunk P rest
          .ok (MessagePayload.ct1 c)
        | .ct2 => do
          let (c, _) ← decode_chunk P rest
          .ok (MessagePayload.ct2 c)
      .ok { epoch := epoch, payload := payload }

end Message

/-- Top-level 11-variant SPQR V1 SCKA state (`pub enum States`, `src/v1/chunked/states.rs:16–29`). -/
inductive States (P : PolyApi) (Au : AuthApi) where
  | keysUnsampled (s : Chunked.SendEk.KeysUnsampled Au)
  | keysSampled (s : Chunked.SendEk.KeysSampled P Au)
  | headerSent (s : Chunked.SendEk.HeaderSent P Au)
  | ct1Received (s : Chunked.SendEk.Ct1Received P Au)
  | ekSentCt1Received (s : Chunked.SendEk.EkSentCt1Received P Au)
  | noHeaderReceived (s : Chunked.SendCt.NoHeaderReceived P Au)
  | headerReceived (s : Chunked.SendCt.HeaderReceived P Au)
  | ct1Sampled (s : Chunked.SendCt.Ct1Sampled P Au)
  | ekReceivedCt1Sampled (s : Chunked.SendCt.EkReceivedCt1Sampled P Au)
  | ct1Acknowledged (s : Chunked.SendCt.Ct1Acknowledged P Au)
  | ct2Sampled (s : Chunked.SendCt.Ct2Sampled P Au)
  deriving DecidableEq, Repr

/-- Output of `States.send` (`pub struct Send`, `src/v1/chunked/states.rs:46–50`). -/
structure V1Send (P : PolyApi) (Au : AuthApi) where
  msg : Message P
  key : Option EpochSecret
  state : States P Au
  deriving DecidableEq, Repr

/-- Output of `States.recv` (`pub struct Recv`, `src/v1/chunked/states.rs:52–55`). -/
structure V1Recv (P : PolyApi) (Au : AuthApi) where
  key : Option EpochSecret
  state : States P Au
  deriving DecidableEq, Repr

namespace States

/-- Initial `send_ek` state (`States::init_a`, `src/v1/chunked/states.rs:58–60`). -/
def init_a (P : PolyApi) (Au : AuthApi) (authKey : Bytes) :
    Except StatesPanic (States P Au) := do
  let s ← Chunked.SendEk.KeysUnsampled.new Au authKey
  .ok (.keysUnsampled s)

abbrev initA := init_a

/-- Initial `send_ct` state (`States::init_b`, `src/v1/chunked/states.rs:62–64`). -/
def init_b (P : PolyApi) (Au : AuthApi) (authKey : Bytes) :
    Except StatesPanic (States P Au) := do
  let s ← Chunked.SendCt.NoHeaderReceived.new P Au authKey
  .ok (.noHeaderReceived s)

abbrev initB := init_b

def epoch {P : PolyApi} {Au : AuthApi} : States P Au → Epoch
  | .keysUnsampled s => s.epoch
  | .keysSampled s => s.epoch
  | .headerSent s => s.epoch
  | .ct1Received s => s.epoch
  | .ekSentCt1Received s => s.epoch
  | .noHeaderReceived s => s.epoch
  | .headerReceived s => s.epoch
  | .ct1Sampled s => s.epoch
  | .ekReceivedCt1Sampled s => s.epoch
  | .ct1Acknowledged s => s.epoch
  | .ct2Sampled s => s.epoch

def into_pb {P : PolyApi} {Au : AuthApi} (self : States P Au) : V1State :=
  { innerState := some <| match self with
      | .keysUnsampled s => .keysUnsampled s.into_pb
      | .keysSampled s => .keysSampled s.into_pb
      | .headerSent s => .headerSent s.into_pb
      | .ct1Received s => .ct1Received s.into_pb
      | .ekSentCt1Received s => .ekSentCt1Received s.into_pb
      | .noHeaderReceived s => .noHeaderReceived s.into_pb
      | .headerReceived s => .headerReceived s.into_pb
      | .ct1Sampled s => .ct1Sampled s.into_pb
      | .ekReceivedCt1Sampled s => .ekReceivedCt1Sampled s.into_pb
      | .ct1Acknowledged s => .ct1Acknowledged s.into_pb
      | .ct2Sampled s => .ct2Sampled s.into_pb }

abbrev intoPb := @into_pb

def from_pb (P : PolyApi) (Au : AuthApi) (pb : V1State) : StatesResult (States P Au) :=
  match pb.innerState with
  | none => .error (.err .stateDecode)
  | some (.keysUnsampled s) => .keysUnsampled <$> Chunked.SendEk.KeysUnsampled.from_pb Au s
  | some (.keysSampled s) => .keysSampled <$> Chunked.SendEk.KeysSampled.from_pb P Au s
  | some (.headerSent s) => .headerSent <$> Chunked.SendEk.HeaderSent.from_pb P Au s
  | some (.ct1Received s) => .ct1Received <$> Chunked.SendEk.Ct1Received.from_pb P Au s
  | some (.ekSentCt1Received s) =>
    .ekSentCt1Received <$> Chunked.SendEk.EkSentCt1Received.from_pb P Au s
  | some (.noHeaderReceived s) =>
    .noHeaderReceived <$> Chunked.SendCt.NoHeaderReceived.from_pb P Au s
  | some (.headerReceived s) =>
    .headerReceived <$> Chunked.SendCt.HeaderReceived.from_pb P Au s
  | some (.ct1Sampled s) => .ct1Sampled <$> Chunked.SendCt.Ct1Sampled.from_pb P Au s
  | some (.ekReceivedCt1Sampled s) =>
    .ekReceivedCt1Sampled <$> Chunked.SendCt.EkReceivedCt1Sampled.from_pb P Au s
  | some (.ct1Acknowledged s) =>
    .ct1Acknowledged <$> Chunked.SendCt.Ct1Acknowledged.from_pb P Au s
  | some (.ct2Sampled s) => .ct2Sampled <$> Chunked.SendCt.Ct2Sampled.from_pb P Au s

abbrev fromPb := from_pb

/-- `States::send` (`src/v1/chunked/states.rs:115–273`), threading the RNG `tape`. -/
def send (K : MlKem) {P : PolyApi} {Au : AuthApi} (self : States P Au) (tape : Bytes) :
    StatesResult (V1Send P Au × Bytes) :=
  match self with
  | .keysUnsampled state => do
    let epoch := state.epoch
    let (state', chunk, tape') ← StatesResult.ofPanic (state.send_hdr_chunk K P tape)
    .ok ({ state := .keysSampled state',
           msg := { epoch := epoch, payload := .hdr chunk },
           key := none }, tape')
  | .keysSampled state => do
    let epoch := state.epoch
    let (state', chunk) ← StatesResult.ofPanic state.send_hdr_chunk
    .ok ({ state := .keysSampled state',
           msg := { epoch := epoch, payload := .hdr chunk },
           key := none }, tape)
  | .headerSent state => do
    let epoch := state.epoch
    let (state', chunk) ← StatesResult.ofPanic state.send_ek_chunk
    .ok ({ state := .headerSent state',
           msg := { epoch := epoch, payload := .ek chunk },
           key := none }, tape)
  | .ct1Received state => do
    let epoch := state.epoch
    let (state', chunk) ← StatesResult.ofPanic state.send_ek_chunk
    .ok ({ state := .ct1Received state',
           msg := { epoch := epoch, payload := .ekCt1Ack chunk },
           key := none }, tape)
  | .ekSentCt1Received state =>
    let epoch := state.epoch
    .ok ({ state := .ekSentCt1Received state,
           msg := { epoch := epoch, payload := .ct1Ack true },
           key := none }, tape)
  | .noHeaderReceived state =>
    let epoch := state.epoch
    .ok ({ state := .noHeaderReceived state,
           msg := { epoch := epoch, payload := .none },
           key := none }, tape)
  | .headerReceived state => do
    let epoch := state.epoch
    let (state', chunk, epochSecret, tape') ← StatesResult.ofPanic (state.send_ct1_chunk K tape)
    .ok ({ state := .ct1Sampled state',
           msg := { epoch := epoch, payload := .ct1 chunk },
           key := some epochSecret }, tape')
  | .ct1Sampled state => do
    let epoch := state.epoch
    let (state', chunk) ← StatesResult.ofPanic state.send_ct1_chunk
    .ok ({ state := .ct1Sampled state',
           msg := { epoch := epoch, payload := .ct1 chunk },
           key := none }, tape)
  | .ekReceivedCt1Sampled state => do
    let epoch := state.epoch
    let (state', chunk) ← StatesResult.ofPanic state.send_ct1_chunk
    .ok ({ state := .ekReceivedCt1Sampled state',
           msg := { epoch := epoch, payload := .ct1 chunk },
           key := none }, tape)
  | .ct1Acknowledged state =>
    let epoch := state.epoch
    .ok ({ state := .ct1Acknowledged state,
           msg := { epoch := epoch, payload := .none },
           key := none }, tape)
  | .ct2Sampled state => do
    let epoch := state.epoch
    let (state', chunk) ← StatesResult.ofPanic state.send_ct2_chunk
    .ok ({ state := .ct2Sampled state',
           msg := { epoch := epoch, payload := .ct2 chunk },
           key := none }, tape)

/-- `States::recv` (`src/v1/chunked/states.rs:275–533`). -/
def recv (K : MlKem) {P : PolyApi} {Au : AuthApi} (self : States P Au) (msg : Message P) :
    StatesResult (V1Recv P Au) :=
  match self with
  | .keysUnsampled state =>
    if msg.epoch > state.epoch then
      .error (.err (.epochOutOfRange msg.epoch))
    else
      .ok { key := none, state := .keysUnsampled state }
  | .keysSampled state =>
    if msg.epoch > state.epoch then
      .error (.err (.epochOutOfRange msg.epoch))
    else if msg.epoch < state.epoch then
      .ok { key := none, state := .keysSampled state }
    else
      match msg.payload with
      | .ct1 chunk => do
        let s' ← StatesResult.ofPanic (state.recv_ct1_chunk msg.epoch chunk)
        .ok { key := none, state := .headerSent s' }
      | _ => .ok { key := none, state := .keysSampled state }
  | .headerSent state =>
    if msg.epoch > state.epoch then
      .error (.err (.epochOutOfRange msg.epoch))
    else if msg.epoch < state.epoch then
      .ok { key := none, state := .headerSent state }
    else
      match msg.payload with
      | .ct1 chunk => do
        let res ← StatesResult.ofPanic (state.recv_ct1_chunk msg.epoch chunk)
        match res with
        | .stillReceiving s' => .ok { key := none, state := .headerSent s' }
        | .done s' => .ok { key := none, state := .ct1Received s' }
      | _ => .ok { key := none, state := .headerSent state }
  | .ct1Received state =>
    if msg.epoch > state.epoch then
      .error (.err (.epochOutOfRange msg.epoch))
    else if msg.epoch < state.epoch then
      .ok { key := none, state := .ct1Received state }
    else
      match msg.payload with
      | .ct2 chunk => do
        let s' ← StatesResult.ofPanic (state.recv_ct2_chunk msg.epoch chunk)
        .ok { key := none, state := .ekSentCt1Received s' }
      | _ => .ok { key := none, state := .ct1Received state }
  | .ekSentCt1Received state =>
    if msg.epoch > state.epoch then
      .error (.err (.epochOutOfRange msg.epoch))
    else if msg.epoch < state.epoch then
      .ok { key := none, state := .ekSentCt1Received state }
    else
      match msg.payload with
      | .ct2 chunk => do
        let res ← state.recv_ct2_chunk K msg.epoch chunk
        match res with
        | .stillReceiving s' => .ok { key := none, state := .ekSentCt1Received s' }
        | .done (s', sec) => .ok { key := some sec, state := .noHeaderReceived s' }
      | _ => .ok { key := none, state := .ekSentCt1Received state }
  | .noHeaderReceived state =>
    if msg.epoch > state.epoch then
      .error (.err (.epochOutOfRange msg.epoch))
    else if msg.epoch < state.epoch then
      .ok { key := none, state := .noHeaderReceived state }
    else
      match msg.payload with
      | .hdr chunk => do
        let res ← state.recv_hdr_chunk msg.epoch chunk
        match res with
        | .stillReceiving s' => .ok { key := none, state := .noHeaderReceived s' }
        | .done s' => .ok { key := none, state := .headerReceived s' }
      | _ => .ok { key := none, state := .noHeaderReceived state }
  | .headerReceived state =>
    if msg.epoch > state.epoch then
      .error (.err (.epochOutOfRange msg.epoch))
    else
      .ok { key := none, state := .headerReceived state }
  | .ct1Sampled state =>
    if msg.epoch > state.epoch then
      .error (.err (.epochOutOfRange msg.epoch))
    else if msg.epoch < state.epoch then
      .ok { key := none, state := .ct1Sampled state }
    else
      let chunkAck? : Option (P.Chunk × Bool) := match msg.payload with
        | .ek chunk => some (chunk, false)
        | .ekCt1Ack chunk => some (chunk, true)
        | _ => none
      match chunkAck? with
      | none => .ok { key := none, state := .ct1Sampled state }
      | some (chunk, ack) => do
        let res ← state.recv_ek_chunk K msg.epoch chunk ack
        match res with
        | .stillReceivingStillSending s' => .ok { key := none, state := .ct1Sampled s' }
        | .stillReceiving s' => .ok { key := none, state := .ct1Acknowledged s' }
        | .stillSending s' => .ok { key := none, state := .ekReceivedCt1Sampled s' }
        | .done s' => .ok { key := none, state := .ct2Sampled s' }
  | .ekReceivedCt1Sampled state =>
    if msg.epoch > state.epoch then
      .error (.err (.epochOutOfRange msg.epoch))
    else if msg.epoch < state.epoch then
      .ok { key := none, state := .ekReceivedCt1Sampled state }
    else
      let isAck := match msg.payload with
        | .ct1Ack true => true
        | .ekCt1Ack _ => true
        | _ => false
      if isAck then do
        let s' ← StatesResult.ofPanic (state.recv_ct1_ack K msg.epoch)
        .ok { key := none, state := .ct2Sampled s' }
      else
        .ok { key := none, state := .ekReceivedCt1Sampled state }
  | .ct1Acknowledged state =>
    if msg.epoch > state.epoch then
      .error (.err (.epochOutOfRange msg.epoch))
    else if msg.epoch < state.epoch then
      .ok { key := none, state := .ct1Acknowledged state }
    else
      let chunk? : Option P.Chunk := match msg.payload with
        | .ek chunk => some chunk
        | .ekCt1Ack chunk => some chunk
        | _ => none
      match chunk? with
      | none => .ok { key := none, state := .ct1Acknowledged state }
      | some chunk => do
        let res ← state.recv_ek_chunk K msg.epoch chunk
        match res with
        | .stillReceiving s' => .ok { key := none, state := .ct1Acknowledged s' }
        | .done s' => .ok { key := none, state := .ct2Sampled s' }
  | .ct2Sampled state =>
    if msg.epoch > state.epoch then
      -- `msg.epoch > state.epoch` implies `state.epoch < u64::MAX`, so `state.epoch + 1` cannot overflow.
      if msg.epoch == state.epoch + 1#64 then do
        let s' ← StatesResult.ofPanic (state.recv_next_epoch msg.epoch)
        .ok { key := none, state := .keysUnsampled s' }
      else
        .error (.err (.epochOutOfRange msg.epoch))
    else
      .ok { key := none, state := .ct2Sampled state }

end States

/-! ## Deterministic test stubs and guards -/

section Guards

/-- Deterministic `MlKem` test stub (`src/incremental_mlkem768.rs:180–187`). -/
def stubMlKem : MlKem where
  keyPair := fun seed => List.Vector.replicate 2400 seed.head
  encaps1 := fun hdr rand =>
    match hdr with
    | [] => none
    | h0 :: _ =>
      let tag := h0 ^^^ rand.head
      some (List.Vector.replicate 960 tag,
            List.Vector.replicate 2080 0#8,
            List.Vector.replicate 32 tag)
  encaps2 := fun _es ek =>
    List.Vector.replicate 128 ek.head
  decaps := fun _dk ct1 _ct2 =>
    List.Vector.replicate 32 ct1.head
  validPk := fun hdr ek =>
    match hdr, ek with
    | h :: _, e :: _ => h == e
    | _, _ => false

instance : Repr Chunk where
  reprPrec c p := reprPrec (c.index, c.data.toList) p

structure StubEncoder where
  idx : BitVec 32
  msg : Bytes
  deriving DecidableEq, Repr

structure StubDecoder where
  pts_needed : BitVec 32
  chunks : List (BitVec 16 × Bytes)
  is_complete : Bool
  deriving DecidableEq, Repr

def lookupChunk (idx : BitVec 16) : List (BitVec 16 × Bytes) → Option Bytes
  | [] => none
  | (k, v) :: rest => if k == idx then some v else lookupChunk idx rest

def reconstructChunks (numChunks : Nat) (chunks : List (BitVec 16 × Bytes)) : Option Bytes :=
  let rec go (i : Nat) (fuel : Nat) (acc : Bytes) : Option Bytes :=
    match fuel with
    | 0 => some acc
    | fuel' + 1 =>
      match lookupChunk (BitVec.ofNat 16 i) chunks with
      | some c => go (i + 1) fuel' (acc ++ c)
      | none => none
  go 0 numChunks []

def deserializeStubChunks : Nat → Bytes → Option (List (BitVec 16 × Bytes))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, hi :: lo :: rest =>
    if rest.length < 32 then none
    else
      let idx : BitVec 16 := (hi.zeroExtend 16 <<< 8) ||| lo.zeroExtend 16
      let chunkBytes := rest.take 32
      match deserializeStubChunks fuel (rest.drop 32) with
      | some tail => some ((idx, chunkBytes) :: tail)
      | none => none
  | _ + 1, [_] => none

/-- Deterministic 32-byte chunk `PolyApi` test stub. -/
def stubPolyApi : PolyApi where
  Chunk := Chunk
  PolynomialError := PolynomialError
  EncodingError := EncodingError
  PolyEncoder := StubEncoder
  PolyDecoder := StubDecoder
  mkChunk := Chunk.mk
  chunkIndex := Chunk.index
  chunkData := Chunk.data
  encode_bytes := fun msg =>
    if msg.length % 2 != 0 then
      .ok (.error (.polynomialError .messageLengthEven))
    else
      .ok (.ok { idx := 0#32, msg := msg })
  next_chunk := fun enc =>
    let numChunks := if enc.msg.length / 32 == 0 then 1 else enc.msg.length / 32
    let chunkPos := enc.idx.toNat % numChunks
    let slice := (enc.msg.drop (chunkPos * 32)).take 32
    let padded := slice ++ List.replicate (32 - slice.length) 0#8
    match bytesToVector? 32 padded with
    | some vec =>
      .ok ({ enc with idx := enc.idx + 1#32 },
           { index := BitVec.ofNat 16 chunkPos, data := vec })
    | none => .error (.site "stubPolyApi.next_chunk")
  encoder_into_pb := fun enc =>
    { idx := enc.idx, pts := List.replicate 16 enc.msg, polys := [] }
  encoder_from_pb := fun pb =>
    if pb.pts.length == 16 && pb.polys.isEmpty then
      let msg := pb.pts.headD []
      if msg.length % 2 == 0 then
        .ok (.ok { idx := pb.idx, msg := msg })
      else
        .ok (.error .serializationInvalid)
    else
      .ok (.error .serializationInvalid)
  decoder_new := fun lenBytes =>
    if lenBytes % 2 != 0 then
      .ok (.error (.polynomialError .messageLengthEven))
    else
      .ok (.ok { pts_needed := BitVec.ofNat 32 (lenBytes / 2), chunks := [], is_complete := false })
  add_chunk := fun dec chunk =>
    let existsIdx := (lookupChunk chunk.index dec.chunks).isSome
    let chunks' := if existsIdx then dec.chunks else dec.chunks ++ [(chunk.index, chunk.data.toList)]
    .ok { dec with chunks := chunks' }
  decoded_message := fun dec =>
    if dec.is_complete then
      .ok none
    else
      let totalBytes := dec.pts_needed.toNat * 2
      let numChunks := totalBytes / 32
      .ok (reconstructChunks numChunks dec.chunks)
  decoder_into_pb := fun dec =>
    let serialized := (dec.chunks.map fun (idx, d) =>
      [idx.extractLsb' 8 8, idx.extractLsb' 0 8] ++ d).flatten
    { ptsNeeded := dec.pts_needed, polys := 16#32,
      pts := serialized :: List.replicate 15 [], isComplete := dec.is_complete }
  decoder_from_pb := fun pb =>
    if pb.pts.length != 16 then
      .ok (.error .serializationInvalid)
    else
      let raw := pb.pts.headD []
      match deserializeStubChunks (raw.length / 34 + 1) raw with
      | some chunks =>
        .ok (.ok { pts_needed := pb.ptsNeeded, chunks := chunks, is_complete := pb.isComplete })
      | none => .ok (.error .serializationInvalid)

/-- Deterministic `AuthApi` test stub. -/
def stubAuthApi : AuthApi where
  Authenticator := ProtoAuthenticator
  new := fun rootKey ep =>
    let b := rootKey.headD 0#8 ^^^ ep.truncate 8
    .ok { rootKey := List.replicate 32 b, macKey := List.replicate 32 (b ^^^ 0x5a#8) }
  update := fun auth ep k =>
    let b := auth.rootKey.headD 0#8 ^^^ k.headD 0#8 ^^^ ep.truncate 8
    .ok { rootKey := List.replicate 32 b, macKey := List.replicate 32 (b ^^^ 0xa5#8) }
  mac_hdr := fun auth ep hdr =>
    let tag := auth.macKey.headD 0#8 ^^^ hdr.headD 0#8 ^^^ ep.truncate 8 ^^^ 0x11#8
    .ok (List.replicate 32 tag)
  mac_ct := fun auth ep ct =>
    let tag := auth.macKey.headD 0#8 ^^^ ct.headD 0#8 ^^^ ep.truncate 8 ^^^ 0x22#8
    .ok (List.replicate 32 tag)
  verify_hdr := fun auth ep hdr expectedMac => do
    let cmp ← compare expectedMac (List.replicate 32
      (auth.macKey.headD 0#8 ^^^ hdr.headD 0#8 ^^^ ep.truncate 8 ^^^ 0x11#8))
    if cmp != 0#8 then .ok (.error .macVerifyFailed) else .ok (.ok ())
  verify_ct := fun auth ep ct expectedMac => do
    let cmp ← compare expectedMac (List.replicate 32
      (auth.macKey.headD 0#8 ^^^ ct.headD 0#8 ^^^ ep.truncate 8 ^^^ 0x22#8))
    if cmp != 0#8 then .ok (.error .macVerifyFailed) else .ok (.ok ())
  into_pb := id
  from_pb := id
  hkdf_to_vec := fun salt ikm info okmLen =>
    if okmLen > 255 * 32 then
      .error (.site "src/kdf.rs:17 Hkdf::expand invalid length")
    else
      let b := salt.headD 0#8 ^^^ ikm.headD 0#8 ^^^ info.getLastD 0#8
      .ok (List.replicate okmLen b)

def checkIssue1275 : Bool :=
  let prefix1536 := List.replicate 768 [0x12#8, 0x34#8] |>.flatten
  let error2Bad := [0x00#8, 0x00#8, 0x00#8, 0x01#8] ++ List.replicate 508 0x00#8
  let tail32 := List.replicate 32 0xaa#8
  let esBad := prefix1536 ++ error2Bad ++ tail32
  let fixedRes := potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 esBad
  match fixedRes with
  | .ok (some esFixed) =>
    esFixed.length == 2080 &&
    esFixed.take 2 == [0x34#8, 0x12#8] &&
    (esFixed.drop 1538).take 2 == [0x01#8, 0x00#8] &&
    esFixed.drop 2048 == tail32 &&
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 esFixed == .ok none &&
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 [0x00#8, 0x01#8] ==
      .error (.issue1275BadLen 2) &&
    flip_endianness_of_encapsulation_state [0x00#8, 0x01#8, 0x02#8] ==
      .error (.flipEndiannessBadLen 3)
  | _ => false

theorem guard_issue1275 : checkIssue1275 = true := by decide +kernel

def checkMessageSerialize : Bool :=
  let c : Chunk := { index := 300#16, data := List.Vector.replicate 32 0x42#8 }
  let payloads : List (MessagePayload stubPolyApi) :=
    [.none, .hdr c, .ek c, .ekCt1Ack c, .ct1Ack true, .ct1 c, .ct2 c]
  let roundTripOk := payloads.all fun p =>
    let msg : Message stubPolyApi := { epoch := 300#64, payload := p }
    let wire := msg.serialize 7#32
    match msg_preamble wire with
    | .ok pre =>
      pre.version == 1#8 && pre.epoch == 300#64 && pre.index == 7#32 &&
      Message.deserialize stubPolyApi pre.epoch pre.remaining == .ok msg
    | .error _ => false
  let errCasesOk :=
    Message.deserialize stubPolyApi 1#64 [] == .error .msgDecode &&
    Message.deserialize stubPolyApi 1#64 [7#8] == .error .msgDecode &&
    Message.deserialize stubPolyApi 1#64 ([1#8, 0#8] ++ List.replicate 31 0#8) == .error .msgDecode &&
    Message.deserialize stubPolyApi 1#64 ([1#8, 0x80#8, 0x80#8, 0x04#8] ++ List.replicate 32 0#8) == .error .msgDecode
  roundTripOk && errCasesOk

theorem guard_message_serialize : checkMessageSerialize = true := by decide +kernel

def checkFullBraidAndPbRoundTrip : Bool :=
  let authKey := List.replicate 32 0x29#8
  let tapeA := List.replicate 64 0x07#8
  let tapeB := List.replicate 32 0x13#8
  let rec transferChunks (n : Nat) (sender receiver : States stubPolyApi stubAuthApi)
      (tape : Bytes) : Option (States stubPolyApi stubAuthApi × States stubPolyApi stubAuthApi ×
        Option EpochSecret × Option EpochSecret) :=
    match n with
    | 0 => some (sender, receiver, none, none)
    | n' + 1 =>
      match sender.send stubMlKem tape with
      | .ok (sOut, tape') =>
        match receiver.recv stubMlKem sOut.msg with
        | .ok rOut =>
          match transferChunks n' sOut.state rOut.state tape' with
          | some (sf, rf, skRest, rkRest) =>
            some (sf, rf, sOut.key.or skRest, rOut.key.or rkRest)
          | none => none
        | .error _ => none
      | .error _ => none
  let pbRoundTrip (st : States stubPolyApi stubAuthApi) : Bool :=
    States.from_pb stubPolyApi stubAuthApi st.into_pb == .ok st
  match States.init_a stubPolyApi stubAuthApi authKey,
        States.init_b stubPolyApi stubAuthApi authKey with
  | .ok stA0, .ok stB0 =>
    let ok0 := pbRoundTrip stA0 && pbRoundTrip stB0
    match transferChunks 3 stA0 stB0 tapeA with
    | some (stA1, stB1, none, none) =>
      let ok1 := pbRoundTrip stA1 && pbRoundTrip stB1
      match transferChunks 1 stB1 stA1 tapeB with
      | some (stB2, stA2, some secB1, none) =>
        let ok2 := pbRoundTrip stA2 && pbRoundTrip stB2
        match transferChunks 36 stA2 stB2 [] with
        | some (_stA2', stB_ekRecv, none, none) =>
          let okEkRecv := pbRoundTrip stB_ekRecv
          match transferChunks 29 stB2 stA2 [] with
          | some (stB3, stA3, none, none) =>
            let ok3 := pbRoundTrip stA3 && pbRoundTrip stB3
            match transferChunks 1 stA3 stB3 [] with
            | some (stA4, stB4, none, none) =>
              let ok4 := pbRoundTrip stA4 && pbRoundTrip stB4
              match transferChunks 35 stA4 stB4 [], transferChunks 1 stA4 stB_ekRecv [] with
              | some (stA5, stB5, none, none), some (_, stB5_alt, none, none) =>
                let ok5 := pbRoundTrip stB5 && pbRoundTrip stB5_alt
                match transferChunks 1 stB5 stA5 [] with
                | some (stB6, stA6, none, none) =>
                  let ok6 := pbRoundTrip stA6 && pbRoundTrip stB6
                  match stA6.send stubMlKem [] with
                  | .ok (sAck, []) =>
                    let okAck := sAck.msg == { epoch := 1#64, payload := .ct1Ack true }
                    match transferChunks 4 stB6 stA6 [] with
                    | some (stB7, stA7, none, some secA1) =>
                      let okEpoch1 := secA1 == secB1 && stA7.epoch == 2#64 && stB7.epoch == 1#64
                      match transferChunks 1 stA7 stB7 [] with
                      | some (stA8, stB8, none, none) =>
                        ok0 && ok1 && ok2 && okEkRecv && ok3 && ok4 && ok5 && ok6 &&
                        okAck && okEpoch1 && stA8.epoch == 2#64 && stB8.epoch == 2#64
                      | _ => false
                    | _ => false
                  | _ => false
                | _ => false
              | _, _ => false
            | _ => false
          | _ => false
        | _ => false
      | _ => false
    | _ => false
  | _, _ => false

theorem guard_full_braid_and_pb_roundtrip : checkFullBraidAndPbRoundTrip = true := by
  decide +kernel

def checkPanicsAndErrors : Bool :=
  let authKey := List.replicate 32 0x29#8
  let rngPanicOk :=
    generate stubMlKem [1#8, 2#8] == .error (.rngExhausted 64 2) &&
    encaps1 stubMlKem (List.replicate 64 0#8) [1#8] == .error (.rngExhausted 32 1) &&
    encaps1 stubMlKem [] (List.replicate 32 0#8) == .error .encaps1Failed
  let comparePanicOk :=
    compare (List.replicate 33 0#8) (List.replicate 32 0#8) == .error .compareBounds
  let fromPbErrOk :=
    States.from_pb stubPolyApi stubAuthApi { innerState := none } == .error (.err .stateDecode) &&
    Chunked.SendEk.HeaderSent.from_pb stubPolyApi stubAuthApi
      { uc := none, sendingEk := none, receivingCt1 := some { ptsNeeded := 99#32 } } ==
      .error (.err .msgDecode) &&
    Chunked.SendEk.EkSentCt1Received.from_pb stubPolyApi stubAuthApi
      { uc := none, receivingCt2 := some { ptsNeeded := 99#32 } } ==
      .error (.err .msgDecode) &&
    Chunked.SendCt.NoHeaderReceived.from_pb stubPolyApi stubAuthApi
      { uc := none, receivingHdr := some { ptsNeeded := 99#32 } } ==
      .error (.err .msgDecode) &&
    Chunked.SendCt.HeaderReceived.from_pb stubPolyApi stubAuthApi
      { uc := none, receivingEk := some { ptsNeeded := 99#32 } } ==
      .error (.err .msgDecode) &&
    Chunked.SendCt.Ct1Sampled.from_pb stubPolyApi stubAuthApi
      { uc := none, sendingCt1 := none, receivingEk := some { ptsNeeded := 99#32 } } ==
      .error (.err .msgDecode) &&
    Chunked.SendCt.Ct1Acknowledged.from_pb stubPolyApi stubAuthApi
      { uc := none, receivingEk := some { ptsNeeded := 99#32 } } ==
      .error (.err .msgDecode)
  let epochErrOk :=
    match States.init_a stubPolyApi stubAuthApi authKey with
    | .ok stA =>
      stA.recv stubMlKem { epoch := 2#64, payload := .none } ==
        .error (.err (.epochOutOfRange 2#64))
    | .error _ => false
  let overflowAndValidPkBytesOk :=
    match stubAuthApi.new authKey 1#64 with
    | .ok auth =>
      let ct2Sent : Unchunked.SendCt.Ct2Sent stubAuthApi :=
        { epoch := BitVec.allOnes 64, auth := auth }
      let ct1Sent : Unchunked.SendCt.Ct1Sent stubAuthApi :=
        { epoch := 1#64, auth := auth, hdr := List.replicate 64 0x07#8,
          es := List.replicate 2080 0#8, ct1 := List.replicate 960 0x07#8 }
      ct2Sent.recv_next_epoch 0#64 == .error .unchunkedRecvNextEpochOverflow &&
      ct1Sent.recv_ek stubMlKem 1#64 [0x07#8] == .error (.err .erroneousDataReceived)
    | .error _ => false
  rngPanicOk && comparePanicOk && fromPbErrOk && epochErrOk && overflowAndValidPkBytesOk

theorem guard_panics_and_errors : checkPanicsAndErrors = true := by
  decide +kernel

end Guards

end CryptoVerification.LibsignalSpqrV1
