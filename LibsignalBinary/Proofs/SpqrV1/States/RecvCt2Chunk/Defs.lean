/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.StatesRepr
public import LibsignalBinary.Proofs.SpqrV1.Auth.Update
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.ChainBridge
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk -- shake: keep

/-!
# `<EkSentCt1Received>::recv_ct2_chunk`: Definitions & Specifications

**Checked by Lean.** Binary layout predicates (`ekSentCt1ReceivedRecvChunkResultAt`, `504` B),
`PolyDecoder::decoded_message` contract, and specifications (`recvCt2ChunkSpecX`, `RecvCt2ChunkOkX`)
for `<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk` (`0x5ec2c`, `514` instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.RecvCt2Chunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-- Symbol name of `<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk`
    (`0x5ec2c`, 514 instructions). -/
abbrev recvCt2ChunkName : String :=
  "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk"

@[simp, arm64_norm] theorem recvCt2Chunk_fnOff :
    libsignalSessionCode.fnOff recvCt2ChunkName = 0x59834 :=
  libsignalSessionCode_fnOff_0x59834

gen_decodes libsignalSessionCode_tree recvCt2ChunkBin [0x59834 → 0x5a03c]

/-- Own stack frame of `recv_ct2_chunk`: `0x60 + 0x960 = 0x9c0 = 2496` bytes. -/
abbrev recvCt2ChunkFrameBytes : Nat := 2496

/-- Own stack frame of `<PolyDecoder as Decoder>::decoded_message` (`672`B) + `extHookStack`. -/
abbrev polyDecodedMessageStackX : Nat := 672 + extHookStack

/-- Total stack budget of `recv_ct2_chunk` (`2496 + polyDecodedMessageStackX = 3168 + extHookStack`). -/
abbrev recvCt2ChunkStackX : Nat := recvCt2ChunkFrameBytes + polyDecodedMessageStackX

/-- Representation of `Unchunked.SendEk.EkSentCt1Received` at `a` (`104` bytes = `0x68`, align `8`):
    - `+0..+48`: `auth: Authenticator` (`root_key` at `+0`, `mac_key` at `+24`)
    - `+48..+72`: `dk: Vec<u8>`
    - `+72..+96`: `ct1: Vec<u8>`
    - `+96..+104`: `epoch: u64` -/
def ekSentCt1ReceivedUcAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) : SepProp :=
  authenticatorAt A a st.auth ∗
    vecU8 A (a + 48#64) st.dk ∗
    vecU8 A (a + 72#64) st.ct1 ∗
    ((a + 96#64) ↦₆₄ st.epoch)

/-- Representation of `Chunked.SendEk.EkSentCt1Received` at `a` (`504` bytes = `0x1f8`, align `8`):
    - `+0..+104`: `uc: Unchunked.SendEk.EkSentCt1Received`
    - `+104..+504`: `receiving_ct2: PolyDecoder` -/
def ekSentCt1ReceivedAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) : SepProp :=
  ekSentCt1ReceivedUcAt A a st.uc ∗
    polyDecoderAt A (a + 104#64) st.receiving_ct2

/-- Representation of `EpochSecret` at `a` (`32` bytes = `0x20`, align `8`):
    - `+0..+24`: `secret: Vec<u8>`
    - `+24..+32`: `epoch: u64` -/
def epochSecretAt (A : RustAlloc) (a : BitVec 64) (sec : EpochSecret) : SepProp :=
  vecU8 A a sec.secret ∗
    ((a + 24#64) ↦₆₄ sec.epoch)

/-- Representation of `EkSentCt1ReceivedRecvChunk` at `a` (`504` bytes = `0x1f8`, align `8`):
    - `.stillReceiving s`: niche-encoded at `+0` via `s.uc.auth.rootKey.cap ≠ noneCap ∧ ≠ none2Cap`;
      layout is `ekSentCt1ReceivedAt A a s` (`504`B).
    - `.done (nhr, sec)`: discriminant `noneCap` (`-1`) at `+0`, `chunkedNoHeaderReceivedAt A (a + 8) nhr`
      (`456`B at `+8..+464`), `epochSecretAt A (a + 464) sec` (`32`B at `+464..+496`), and `8`B trailing
      padding at `+496..+504`. -/
def ekSentCt1ReceivedRecvChunkAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64) :
    Chunked.SendEk.EkSentCt1ReceivedRecvChunk spqrPolyApi (spqrAuthApi F) → SepProp
  | .stillReceiving s =>
      ⌜PolyDecoderStrictSorted s.receiving_ct2⌝ ∗
        ekSentCt1ReceivedAt A a s
  | .done (nhr, sec) =>
      ⌜PolyDecoderStrictSorted nhr.receiving_hdr⌝ ∗
        (a ↦₆₄ noneCap) ∗
        chunkedNoHeaderReceivedAt A (a + 8#64) nhr ∗
        epochSecretAt A (a + 464#64) sec ∗
        memRegion (a + 496#64) 8

/-- Discriminant byte of `spqr::Error` (`src/lib.rs:96–130`). -/
def spqrErrorByte : Error → BitVec 8
  | .stateDecode => 0#8
  | .notImplemented => 1#8
  | .msgDecode => 2#8
  | .macVerifyFailed => 3#8
  | .epochOutOfRange _ => 4#8
  | .encodingDecoding => 5#8
  | .serialization => 6#8
  | .versionMismatch => 7#8
  | .minimumVersion => 8#8
  | .keyJump _ _ => 9#8
  | .keyTrimmed _ => 10#8
  | .keyAlreadyRequested _ => 11#8
  | .erroneousDataReceived => 12#8
  | .sendKeyEpochDecreased _ _ => 13#8
  | .invalidParams _ => 14#8
  | .chainNotAvailable => 15#8

/-- Representation of `Result<EkSentCt1ReceivedRecvChunk, Error>` at `a` (`504` bytes = `0x1f8`, align `8`):
    - `.ok res`: `ekSentCt1ReceivedRecvChunkAt A a res`
    - `.error (.err e)`: discriminant `none2Cap` (`-2`) at `+0`, `spqrErrorByte e` at `+8`, and `495`B trailing
      padding at `+9..+504`.
    - `.error (.panic _)`: unreachable in normal return `post` (`False`). -/
def ekSentCt1ReceivedRecvChunkResultAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64) :
    StatesResult (Chunked.SendEk.EkSentCt1ReceivedRecvChunk spqrPolyApi (spqrAuthApi F)) → SepProp
  | .ok res =>
      ekSentCt1ReceivedRecvChunkAt A a res
  | .error (.err e) =>
      (a ↦₆₄ none2Cap) ∗
        ((a + 8#64) ↦₈ spqrErrorByte e) ∗
        memRegion (a + 9#64) 495
  | .error (.panic _) =>
      ⌜False⌝

/-- Ghost arguments for `<PolyDecoder as Decoder>::decoded_message` (`0x6bb80`). -/
structure PolyDecodedMessageCall where
  /-- Sret pointer (`x8`, 24-byte `Option<Vec<u8>>`). -/
  outA : BitVec 64
  /-- Pointer to `self : &PolyDecoder` (`x0`, 400 bytes). -/
  decA : BitVec 64
  dec : PolyDecoder

/-- Callee specification of `<PolyDecoder as Decoder>::decoded_message` (`0x6bb80`, 516 instructions):
    given `PolyDecoderStrictSorted x.dec`, `x.dec.decodedMessage` succeeds with `.ok opt` and writes
    `optKeyBytesAt A x.outA opt` to `x.outA`, or panics on OOM (`allocFailedIn`). -/
def polyDecodedMessageSpec (A : RustAlloc) (b : BitVec 64) : Spec PolyDecodedMessageCall where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧
      s.readReg64 .x0 = x.decA ∧
      PolyDecoderStrictSorted x.dec⌝ ∗
      memRegion x.outA vecHeaderBytes ∗
      polyDecoderAt A x.decA x.dec ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗
      stackAt s.sp polyDecodedMessageStackX
  post := fun x s0 sf =>
    (∃∗ opt : Option Bytes,
      ⌜x.dec.decodedMessage = .ok opt ∧ sf.trace = s0.trace⌝ ∗
        optKeyBytesAt A x.outA opt) ∗
      polyDecoderAt A x.decA x.dec ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗
      stackAt s0.sp polyDecodedMessageStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Symbol name of `<PolyDecoder as Decoder>::decoded_message` (`0x6bb80`). -/
abbrev polyDecodedMessageName : String :=
  "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"

@[simp, arm64_norm] theorem polyDecodedMessage_fnOff :
    libsignalSessionCode.fnOff polyDecodedMessageName = 0x66788 :=
  libsignalSessionCode_fnOff_0x66788

/-- `<PolyDecoder as Decoder>::decoded_message` (`0x6bb80`) meets
    `(polyDecodedMessageSpec A img.base).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def PolyDecodedMessageOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecodedMessageName)
    ((polyDecodedMessageSpec A img.base).inImage img)

/-- Ghost arguments of `<EkSentCt1Received>::recv_ct2_chunk` (`0x5ec2c`). -/
structure RecvCt2ChunkGhost (F : ShaCompress) where
  /-- Sret pointer (`x0`, 504-byte `Result<EkSentCt1ReceivedRecvChunk, Error>`). -/
  outA : BitVec 64
  /-- Pointer to consumed `self : Chunked.SendEk.EkSentCt1Received` (`x1`, 504 bytes). -/
  selfA : BitVec 64
  self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)
  /-- Epoch argument (`x2`). -/
  epoch : Epoch
  /-- Pointer to `chunk : &Chunk` (`x3`, 34 bytes). -/
  chunkA : BitVec 64
  chunk : Chunk

/-- Specification of `<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk`
    (`src/v1/chunked/send_ek.rs:195–227`, image offset `0x5ec2c`, 514 instructions):
    - Consumes `chunkedEkSentCt1ReceivedAt A x.selfA x.self` (leaving `memRegion x.selfA 504`)
      and preserves `chunkAt x.chunkA x.chunk`.
    - When `x.self.recv_ct2_chunk K x.epoch x.chunk` returns `.ok res` or `.error (.err e)`,
      writes `ekSentCt1ReceivedRecvChunkResultAt A x.outA (x.self.recv_ct2_chunk K x.epoch x.chunk)`.
    - When `x.self.recv_ct2_chunk K x.epoch x.chunk` returns `.error (.panic _)` (or on OOM),
      panics via `onPanic`. -/
def recvCt2ChunkSpec (K : MlKem) (F : ShaCompress) (A : RustAlloc) (b : BitVec 64) :
    Spec (RecvCt2ChunkGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.self.receiving_ct2 ∧
      x.self.uc.auth.rootKey.length + 32 < 2 ^ 63⌝ ∗
      memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
      ekSentCt1ReceivedAt A x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗
      stackAt s.sp recvCt2ChunkStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedRecvChunkResultAt A x.outA (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
      memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗
      stackAt s0.sp recvCt2ChunkStackX
  onPanic := fun x s0 sf =>
    ⌜((x.self.recv_ct2_chunk K x.epoch x.chunk).isPanic = true ∨
        allocFailedIn s0 sf) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `<EkSentCt1Received>::recv_ct2_chunk` (`0x5ec2c`) meets
    `(recvCt2ChunkSpec K F A img.base).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def RecvCt2ChunkOkX (img : Obj.Image) (K : MlKem) (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName)
    ((recvCt2ChunkSpec K F A img.base).inImage img)

/-- Total stack budget of `recv_ct2_chunk` under contract-backed KDF/Auth specs:
    `recvCt2ChunkFrameBytes + authUpdateStackExt = 2496 + 17776 = 20272` bytes. -/
abbrev recvCt2ChunkStackExt : Nat := recvCt2ChunkFrameBytes + authUpdateStackExt

/-- Contract-backed specification of `<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk`
    (`0x5ec2c`), identical to `recvCt2ChunkSpec` with stack budget `recvCt2ChunkStackExt` (`20272`B). -/
def recvCt2ChunkSpecExt (K : MlKem) (F : ShaCompress) (A : RustAlloc) (b : BitVec 64) :
    Spec (RecvCt2ChunkGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.self.receiving_ct2 ∧
      x.self.uc.auth.rootKey.length + 32 < 2 ^ 63⌝ ∗
      memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
      ekSentCt1ReceivedAt A x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗
      stackAt s.sp recvCt2ChunkStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedRecvChunkResultAt A x.outA (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
      memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗
      stackAt s0.sp recvCt2ChunkStackExt
  onPanic := fun x s0 sf =>
    ⌜((x.self.recv_ct2_chunk K x.epoch x.chunk).isPanic = true ∨
        allocFailedIn s0 sf) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `<EkSentCt1Received>::recv_ct2_chunk` (`0x5ec2c`) meets
    `(recvCt2ChunkSpecExt K F A img.base).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def RecvCt2ChunkOkExt (img : Obj.Image) (K : MlKem) (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName)
    ((recvCt2ChunkSpecExt K F A img.base).inImage img)

theorem stackAt_recvCt2ChunkExt_eq_X (sp : BitVec 64) :
    stackAt sp recvCt2ChunkStackExt =
      memRegion (sp - 20272#64) 720 ∗ stackAt sp recvCt2ChunkStackX :=
  stackAt_split_bottom sp recvCt2ChunkStackX 720 (by decide)

theorem stackAt_authUpdateExt_eq_hkdfExt (fsp : BitVec 64) :
    stackAt fsp authUpdateStackExt =
      memRegion (fsp - 17776#64) 160 ∗ stackAt fsp hkdfToSliceStackExt :=
  stackAt_split_bottom fsp hkdfToSliceStackExt 160 (by decide)

theorem stackAt_authUpdateExt_eq_poly (fsp : BitVec 64) :
    stackAt fsp authUpdateStackExt =
      memRegion (fsp - 17776#64) 720 ∗ stackAt fsp polyDecodedMessageStackX :=
  stackAt_split_bottom fsp polyDecodedMessageStackX 720 (by decide)

theorem stackAt_authUpdateExt_eq_extHook (fsp : BitVec 64) :
    stackAt fsp authUpdateStackExt =
      memRegion (fsp - 17776#64) 1392 ∗ stackAt fsp extHookStack :=
  stackAt_split_bottom fsp extHookStack 1392 (by decide)

/-- `.rodata` slice at `0x83850` (`33` bytes): `sckaKeyInfoPrefix`
    (`"Signal_PQCKA_V1_MLKEM768:SCKA Key"`). -/
theorem rodata_sckaKeyInfoPrefix {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x59a38 0x59a3c)) ↦ᵣ sckaKeyInfoPrefix) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x59a38 0x59a3c)) (n := 33) (bs := sckaKeyInfoPrefix)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-- `.rodata` slice at `0x83748` (`35` bytes): `Authenticator.ctLabel`
    (`"Signal_PQCKA_V1_MLKEM768:ciphertext"`). -/
theorem rodata_ctLabel {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) (n := 35) (bs := Authenticator.ctLabel)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

@[simp, arm64_norm] theorem mlkemDecaps_fnOff :
    libsignalSessionCode.fnOff mlkemDecapsName =
      ls_off% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key" :=
  ls_stub% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key"

/-- Concrete value of `PolyDecoder.new 96` (`64 + 32 = 96`). -/
def polyDecoderNew96 : PolyDecoder :=
  { pts := List.replicate NUM_POLYS SortedSetPt.new
    ptsNeeded := 48
    isComplete := false }

@[simp]
theorem polyDecoder_new_96 :
    PolyDecoder.new 96 = .ok (.ok polyDecoderNew96) := by
  decide

@[simp]
theorem expectDecoderNew_96 :
    expectDecoderNew spqrPolyApi "v1/chunked/send_ek.rs:218" 96 =
      .ok polyDecoderNew96 := by
  decide

theorem polyDecoderStrictSorted_new96 : PolyDecoderStrictSorted polyDecoderNew96 := by
  intro s hs
  rw [polyDecoderNew96, List.mem_replicate] at hs
  rcases hs with ⟨_, rfl⟩
  exact List.Pairwise.nil

@[simp, arm64_norm, wp_norm]
theorem extractLsb'_0_64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  bv_kernel

@[simp, arm64_norm, wp_norm]
theorem extractLsb'_64_64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  bv_kernel

/-- Saved callee-saved registers at `[s0.sp - 96 .. s0.sp)`. -/
def savedRegsAt (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Unused stack padding regions inside `[fsp .. fsp + 0x960)`:
    `[0x478..0x480)` (`8`B), `[0x4d8..0x4e0)` (`8`B), `[0x920..0x928)` (`8`B), `[0x948..0x960)` (`24`B). -/
def unusedFrameAt (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x478#64) 8 ∗
    memRegion (fsp + 0x4d8#64) 8 ∗
    memRegion (fsp + 0x920#64) 8 ∗
    memRegion (fsp + 0x948#64) 24

theorem stackAt_polyDecodedMessage_eq_addChunk (fsp : BitVec 64) :
    stackAt fsp polyDecodedMessageStackX =
      memRegion (fsp - 17056#64) 576 ∗ stackAt fsp addChunkStackX :=
  stackAt_split_bottom fsp addChunkStackX 576 (by decide)

theorem stackAt_polyDecodedMessage_eq_extHook (fsp : BitVec 64) :
    stackAt fsp polyDecodedMessageStackX =
      memRegion (fsp - 17056#64) 672 ∗ stackAt fsp extHookStack :=
  stackAt_split_bottom fsp extHookStack 672 (by decide)

theorem stackAt_polyDecodedMessage_eq_authUpdate (fsp : BitVec 64) :
    stackAt fsp polyDecodedMessageStackX =
      memRegion (fsp - 17056#64) 512 ∗ stackAt fsp authUpdateStackX :=
  stackAt_split_bottom fsp authUpdateStackX 512 (by decide)

theorem stackAt_polyDecodedMessage_eq_doReserve (fsp : BitVec 64) :
    stackAt fsp polyDecodedMessageStackX =
      memRegion (fsp - 17056#64) 12848 ∗ stackAt fsp doReserveStack :=
  stackAt_split_bottom fsp doReserveStack 12848 (by decide)

theorem stackAt_polyDecodedMessage_eq_allocHook (fsp : BitVec 64) :
    stackAt fsp polyDecodedMessageStackX =
      memRegion (fsp - 17056#64) 12960 ∗ stackAt fsp allocHookStack :=
  stackAt_split_bottom fsp allocHookStack 12960 (by decide)

theorem stackAt_polyDecodedMessage_eq_dropStack32 (fsp : BitVec 64) :
    stackAt fsp polyDecodedMessageStackX =
      memRegion (fsp - 17056#64) 12928 ∗ stackAt fsp dropStack32 :=
  stackAt_split_bottom fsp dropStack32 12928 (by decide)

/-! ## Stack Frame & Representation Helpers -/

/-- Portion of the stack frame only touched in the `Some(ct2Full)` branch. -/
def someBranchFrameAt (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x1f0#64) 144 ∗
    memRegion (fsp + 0x480#64) 16 ∗
    memRegion (fsp + 0x490#64) 48 ∗
    memRegion (fsp + 0x4c0#64) 24 ∗
    memRegion (fsp + 0x4e0#64) 960 ∗
    memRegion (fsp + 0x8a0#64) 128 ∗
    memRegion (fsp + 0x928#64) 32 ∗
    unusedFrameAt fsp

/-- Active stack frame of `recv_ct2_chunk` at `fsp = sp - 2496#64` (`[fsp .. fsp + 0x960)` = `2400` bytes). -/
def activeFrameRegionsAt (fsp : BitVec 64) : SepProp :=
  cells fsp 9 ∗
    memRegion (fsp + 0x48#64) 400 ∗
    memRegion (fsp + 0x1d8#64) 24 ∗
    memRegion (fsp + 0x280#64) 504 ∗
    someBranchFrameAt fsp

theorem memRegion_2400_eq_activeFrameRegionsAt (fsp : BitVec 64) :
    memRegion fsp 2400 = activeFrameRegionsAt fsp := by
  unfold activeFrameRegionsAt someBranchFrameAt unusedFrameAt
  rw [ProofLib.memRegion_split' (b := fsp) (n := 72) (k := 2328)
        (b' := fsp + 0x48#64) rfl rfl (by decide),
      ProofLib.memRegion_cells fsp 9 (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x48#64) (n := 400) (k := 1928)
        (b' := fsp + 0x1d8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1d8#64) (n := 24) (k := 1904)
        (b' := fsp + 0x1f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1f0#64) (n := 144) (k := 1760)
        (b' := fsp + 0x280#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x280#64) (n := 504) (k := 1256)
        (b' := fsp + 0x478#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x478#64) (n := 8) (k := 1248)
        (b' := fsp + 0x480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x480#64) (n := 16) (k := 1232)
        (b' := fsp + 0x490#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x490#64) (n := 48) (k := 1184)
        (b' := fsp + 0x4c0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x4c0#64) (n := 24) (k := 1160)
        (b' := fsp + 0x4d8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x4d8#64) (n := 8) (k := 1152)
        (b' := fsp + 0x4e0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x4e0#64) (n := 960) (k := 192)
        (b' := fsp + 0x8a0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x8a0#64) (n := 128) (k := 64)
        (b' := fsp + 0x920#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x920#64) (n := 8) (k := 56)
        (b' := fsp + 0x928#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x928#64) (n := 32) (k := 24)
        (b' := fsp + 0x948#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem stackAt_recvCt2Chunk_split (sp : BitVec 64) :
    stackAt sp recvCt2ChunkStackX =
      stackAt (sp - 2496#64) polyDecodedMessageStackX ∗
        activeFrameRegionsAt (sp - 2496#64) ∗
        cells (sp - 96#64) 12 := by
  change memRegion (sp - BitVec.ofNat 64 19552) 19552 =
    memRegion ((sp - 2496#64) - BitVec.ofNat 64 17056) 17056 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 19552) (n := 17056) (k := 2496)
        (b' := sp - 2496#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 2496#64) (n := 2400) (k := 96)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      memRegion_2400_eq_activeFrameRegionsAt (sp - 2496#64),
      ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  have hsub : (sp - 2496#64) - BitVec.ofNat 64 17056 = sp - BitVec.ofNat 64 19552 := by bv_kernel
  rw [hsub]

theorem savedRegsAt_entails_cells12 (s0 : State) :
    savedRegsAt s0 ⊢ cells (s0.sp - 96#64) 12 := by
  unfold savedRegsAt
  cells_unfold
  exact Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
      (Entails.sepExists_right (s0.readReg64 .x28)
        (Entails.sepExists_right (s0.readReg64 .x27)
          (Entails.sepExists_right (s0.readReg64 .x26)
            (Entails.sepExists_right (s0.readReg64 .x25)
              (Entails.sepExists_right (s0.readReg64 .x24)
                (Entails.sepExists_right (s0.readReg64 .x23)
                  (Entails.sepExists_right (s0.readReg64 .x22)
                    (Entails.sepExists_right (s0.readReg64 .x21)
                      (Entails.sepExists_right (s0.readReg64 .x20)
                        (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))))))

theorem cells9_fsp_entails (fsp c0 c1 c2 c3 c4 c5 c6 c7 c8 : BitVec 64) :
    (fsp ↦₆₄ c0) ∗ ((fsp + 0x08#64) ↦₆₄ c1) ∗ ((fsp + 0x10#64) ↦₆₄ c2) ∗
      ((fsp + 0x18#64) ↦₆₄ c3) ∗ ((fsp + 0x20#64) ↦₆₄ c4) ∗ ((fsp + 0x28#64) ↦₆₄ c5) ∗
      ((fsp + 0x30#64) ↦₆₄ c6) ∗ ((fsp + 0x38#64) ↦₆₄ c7) ∗ ((fsp + 0x40#64) ↦₆₄ c8) ⊢
    cells fsp 9 := by
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]
  exact Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
    (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
      (Entails.sepExists_right c6 (Entails.sepExists_right c7
        (Entails.sepExists_right c8 (Entails.refl _)))))))))

theorem rejoin_stack_recvCt2Chunk (s0 : State) :
    stackAt (s0.sp - 2496#64) polyDecodedMessageStackX ∗
      activeFrameRegionsAt (s0.sp - 2496#64) ∗
      savedRegsAt s0 ⊢
    stackAt s0.sp recvCt2ChunkStackX := by
  rw [stackAt_recvCt2Chunk_split s0.sp]
  exact sepConj_mono_right (sepConj_mono_right (savedRegsAt_entails_cells12 s0))

/-! ## Byte-Splitting & Relocation Combinators (`SplitBytes`) -/

/-- Decomposition of an address-indexed predicate `P : BitVec 64 → SepProp` into `n` contiguous bytes
    at `a` (`a ↦ₛ bs` with `bs.length = n`) plus an address-independent resource `heap bs`. -/
structure SplitBytes (n : Nat) (P : BitVec 64 → SepProp) where
  heap : List (BitVec 8) → SepProp
  to_bytes : ∀ a : BitVec 64, P a ⊢ ∃∗ bs : List (BitVec 8), ⌜bs.length = n⌝ ∗ (a ↦ₛ bs) ∗ heap bs
  of_bytes : ∀ (a : BitVec 64) (bs : List (BitVec 8)), bs.length = n → (a ↦ₛ bs) ∗ heap bs ⊢ P a

namespace SplitBytes

def congr {n : Nat} {P Q : BitVec 64 → SepProp} (h : ∀ a, P a = Q a) (S : SplitBytes n P) :
    SplitBytes n Q where
  heap := S.heap
  to_bytes a := h a ▸ S.to_bytes a
  of_bytes a bs hlen := h a ▸ S.of_bytes a bs hlen

def pointsToBytesFixed (bs0 : List (BitVec 8)) : SplitBytes bs0.length (fun a => a ↦ₛ bs0) where
  heap bs := ⌜bs = bs0⌝ ∗ emp
  to_bytes a :=
    Entails.sepExists_right bs0
      (Entails.pure_right rfl
        (Entails.trans (Entails.of_eq (sepConj_emp (a ↦ₛ bs0)).symm)
          (sepConj_mono_right (Entails.pure_right rfl (Entails.refl emp)))))
  of_bytes a bs _ := by
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro rfl
    rw [sepConj_emp]
    exact Entails.refl _

def pointsTo64 (v : BitVec 64) : SplitBytes 8 (fun a => a ↦₆₄ v) :=
  let S := pointsToBytesFixed (unpack64 v)
  have hlen : (unpack64 v).length = 8 := unpack64_length v
  congr (fun a => (pointsTo64_eq_pointsToBytes a v).symm) (hlen ▸ S)

def pointsTo8 (b : BitVec 8) : SplitBytes 1 (fun a => a ↦₈ b) :=
  have h1 : ∀ a, (a ↦ₛ [b]) = (a ↦₈ b) := fun a => by
    rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  congr h1 (show SplitBytes 1 (fun a => a ↦ₛ [b]) from pointsToBytesFixed [b])

def empSplit : SplitBytes 0 (fun _ => emp) :=
  have h0 : ∀ a, (a ↦ₛ []) = emp := pointsToBytes_nil
  congr h0 (show SplitBytes 0 (fun a => a ↦ₛ []) from pointsToBytesFixed [])

def region (n : Nat) (hn : n ≤ 2 ^ 64) : SplitBytes n (fun a => memRegion a n) where
  heap _ := emp
  to_bytes a := by
    rw [memRegion_eq_exists_bytes a n hn]
    apply Entails.sepExists_elim; intro bs
    refine Entails.sepExists_right bs ?_
    rw [sepConj_emp]
    exact Entails.refl _
  of_bytes a bs hlen := by
    rw [sepConj_emp, ← hlen]
    exact pointsToBytes_entails_memRegion a bs

def pureConj (P : Prop) {n : Nat} {Q : BitVec 64 → SepProp} (S : SplitBytes n Q) :
    SplitBytes n (fun a => ⌜P⌝ ∗ Q a) where
  heap bs := ⌜P⌝ ∗ S.heap bs
  to_bytes a := by
    apply Entails.pure_left; intro hP
    refine Entails.trans (S.to_bytes a) ?_
    apply Entails.sepExists_elim; intro bs
    refine Entails.sepExists_right bs ?_
    apply Entails.pure_left; intro hlen
    refine Entails.pure_right hlen ?_
    exact sepConj_mono_right (Entails.pure_right hP (Entails.refl _))
  of_bytes a bs hlen := by
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hP
    exact Entails.pure_right hP (S.of_bytes a bs hlen)

open Classical in
noncomputable def pureConjImp {P : Prop} {n : Nat} {Q : BitVec 64 → SepProp}
    (S : P → SplitBytes n Q) :
    SplitBytes n (fun a => ⌜P⌝ ∗ Q a) where
  heap bs := if h : P then (S h).heap bs else ⌜False⌝
  to_bytes a := by
    apply Entails.pure_left; intro hP
    refine Entails.trans ((S hP).to_bytes a) ?_
    apply Entails.sepExists_elim; intro bs
    refine Entails.sepExists_right bs ?_
    simp only [hP, ↓reduceDIte]
    exact Entails.refl _
  of_bytes a bs hlen := by
    by_cases hP : P
    · refine Entails.pure_right hP ?_
      simp only [hP, ↓reduceDIte]
      exact (S hP).of_bytes a bs hlen
    · simp only [hP, ↓reduceDIte]
      rw [sepConj_comm]
      apply Entails.pure_left; exact False.elim

def frameRight (R : SepProp) {n : Nat} {P : BitVec 64 → SepProp} (S : SplitBytes n P) :
    SplitBytes n (fun a => P a ∗ R) where
  heap bs := S.heap bs ∗ R
  to_bytes a := by
    refine Entails.trans (sepConj_mono_left (S.to_bytes a)) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs
    refine Entails.sepExists_right bs ?_
    exact Entails.of_eq (by ac_rfl)
  of_bytes a bs hlen := by
    rw [← sepConj_assoc]
    exact sepConj_mono_left (S.of_bytes a bs hlen)

def existsOf {α : Type} {n : Nat} {P : α → BitVec 64 → SepProp}
    (S : ∀ x : α, SplitBytes n (P x)) :
    SplitBytes n (fun a => ∃∗ x : α, P x a) where
  heap bs := ∃∗ x : α, (S x).heap bs
  to_bytes a := by
    apply Entails.sepExists_elim; intro x
    refine Entails.trans ((S x).to_bytes a) ?_
    apply Entails.sepExists_elim; intro bs
    refine Entails.sepExists_right bs ?_
    exact sepConj_mono_right (sepConj_mono_right (Entails.sepExists_right x (Entails.refl _)))
  of_bytes a bs hlen := by
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro x
    exact Entails.sepExists_right x ((S x).of_bytes a bs hlen)

def seq {n m : Nat} {P Q : BitVec 64 → SepProp}
    (Sn : SplitBytes n P) (Sm : SplitBytes m Q) (hnm : n + m ≤ 2 ^ 64) :
    SplitBytes (n + m) (fun a => P a ∗ Q (a + BitVec.ofNat 64 n)) where
  heap bs := Sn.heap (bs.take n) ∗ Sm.heap (bs.drop n)
  to_bytes a := by
    refine Entails.trans (sepConj_mono (Sn.to_bytes a) (Sm.to_bytes (a + BitVec.ofNat 64 n))) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs1
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs2
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hlen1
    rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; intro hlen2
    refine Entails.sepExists_right (bs1 ++ bs2) ?_
    have hlen : (bs1 ++ bs2).length = n + m := by rw [List.length_append, hlen1, hlen2]
    have htake : (bs1 ++ bs2).take n = bs1 := by
      rw [List.take_append_of_le_length (by omega), ← hlen1, List.take_length]
    have hdrop : (bs1 ++ bs2).drop n = bs2 := by
      rw [List.drop_append_of_le_length (by omega), ← hlen1, List.drop_length, List.nil_append]
    refine Entails.pure_right hlen ?_
    rw [pointsToBytes_append, hlen1, htake, hdrop]
    exact Entails.of_eq (by ac_rfl)
  of_bytes a bs hlen := by
    have h1 : (bs.take n).length = n := by rw [List.length_take]; omega
    have h2 : (bs.drop n).length = m := by rw [List.length_drop]; omega
    have happ : bs.take n ++ bs.drop n = bs := List.take_append_drop n bs
    conv_lhs => arg 1; rw [← happ, pointsToBytes_append, h1]
    have harrange :
        ((a ↦ₛ bs.take n) ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bs.drop n)) ∗
          (Sn.heap (bs.take n) ∗ Sm.heap (bs.drop n)) =
        ((a ↦ₛ bs.take n) ∗ Sn.heap (bs.take n)) ∗
          (((a + BitVec.ofNat 64 n) ↦ₛ bs.drop n) ∗ Sm.heap (bs.drop n)) := by ac_rfl
    rw [harrange]
    exact sepConj_mono (Sn.of_bytes a (bs.take n) h1) (Sm.of_bytes (a + BitVec.ofNat 64 n) (bs.drop n) h2)

def vecHdr (cap ptr len : BitVec 64) : SplitBytes 24 (fun a => vecHeader a cap ptr len) :=
  have h : ∀ a, (a ↦₆₄ cap) ∗ ((a + BitVec.ofNat 64 8) ↦₆₄ ptr) ∗
      (((a + BitVec.ofNat 64 8) + BitVec.ofNat 64 8) ↦₆₄ len) = vecHeader a cap ptr len := by
    intro a; unfold vecHeader
    have h16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
    simp only [BitVec.ofNat_eq_ofNat, h16, sepConj_assoc]
  congr h ((pointsTo64 cap).seq ((pointsTo64 ptr).seq (pointsTo64 len) (by decide)) (by decide))

def vecAtSplit (A : RustAlloc) (sz align : Nat) {α : Type} (elemAt : α → BitVec 64 → SepProp)
    (cap ptr : BitVec 64) (xs : List α) :
    SplitBytes 24 (fun a => vecAt A sz align elemAt a cap ptr xs) :=
  (vecHdr cap ptr (BitVec.ofNat 64 xs.length)).frameRight _

def vecOfSplit (A : RustAlloc) (sz align : Nat) {α : Type} (elemAt : α → BitVec 64 → SepProp)
    (xs : List α) :
    SplitBytes 24 (fun a => vecOf A sz align elemAt a xs) :=
  existsOf fun cap => existsOf fun ptr => vecAtSplit A sz align elemAt cap ptr xs

def vecU8Split (A : RustAlloc) (bs : List (BitVec 8)) :
    SplitBytes 24 (fun a => vecU8 A a bs) :=
  existsOf fun cap => existsOf fun ptr => (vecHdr cap ptr (BitVec.ofNat 64 bs.length)).frameRight _

def arrayAtSplit {α : Type} {stride : Nat} {elemAt : α → BitVec 64 → SepProp}
    (S : ∀ x : α, SplitBytes stride (elemAt x)) :
    (xs : List α) → (h : xs.length * stride ≤ 2 ^ 64) →
    SplitBytes (xs.length * stride) (fun a => arrayAt elemAt stride a xs)
  | [], _ =>
    have h0 : ([].length * stride) = 0 := Nat.zero_mul stride
    h0 ▸ empSplit
  | x :: xs, h =>
    have h_tail : xs.length * stride ≤ 2 ^ 64 := by
      simp only [List.length_cons, Nat.succ_mul] at h; omega
    have h_add : stride + xs.length * stride = (x :: xs).length * stride := by
      simp only [List.length_cons, Nat.succ_mul, Nat.add_comm]
    h_add ▸ (S x).seq (arrayAtSplit S xs h_tail) (by omega)

def sortedSetPtSplit (A : RustAlloc) (s : SortedSetPt) :
    SplitBytes 24 (fun a => sortedSetPtOf A a s) :=
  vecOfSplit A ptStride ptAlign ptAt s.vec

noncomputable def polyDecoderSplit (A : RustAlloc) (dec : PolyDecoder) :
    SplitBytes 400 (fun a => polyDecoderAt A a dec) :=
  have h : ∀ a, (⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗
      (sortedSetPtListOf A a dec.pts ∗
        (((a + BitVec.ofNat 64 384) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          (((a + BitVec.ofNat 64 384) + BitVec.ofNat 64 8) ↦₈ boolByte dec.isComplete) ∗
          memRegion (((a + BitVec.ofNat 64 384) + BitVec.ofNat 64 8) + BitVec.ofNat 64 1) 7))) =
      polyDecoderAt A a dec := by
    intro a
    unfold polyDecoderAt polyDecoderPtsNeededOff polyDecoderIsCompleteOff polyDecoderPadOff polyDecoderPadSize
    have h384 : BitVec.ofNat 64 384 = 0x180#64 := rfl
    have h392 : (a + 0x180#64) + 8#64 = a + 0x188#64 := by bv_omega
    have h393 : (a + 0x188#64) + 1#64 = a + 0x189#64 := by bv_omega
    simp only [h384, BitVec.ofNat_eq_ofNat, h392, h393, sepConj_assoc]
  congr h <| pureConjImp fun ⟨hlen, _⟩ =>
    have hmul : dec.pts.length * Poly.vecHeaderBytes = 384 := by
      rw [hlen]; rfl
    have hbound : dec.pts.length * Poly.vecHeaderBytes ≤ 2 ^ 64 := by omega
    have S_pts : SplitBytes 384 (fun a => sortedSetPtListOf A a dec.pts) :=
      hmul ▸ arrayAtSplit (sortedSetPtSplit A) dec.pts hbound
    S_pts.seq
      ((pointsTo64 (BitVec.ofNat 64 dec.ptsNeeded)).seq
        ((pointsTo8 (boolByte dec.isComplete)).seq (region 7 (by decide)) (by decide))
        (by decide))
      (by decide)

def authenticatorSplit (A : RustAlloc) (auth : Authenticator) :
    SplitBytes 48 (fun a => authenticatorAt A a auth) :=
  (vecU8Split A auth.rootKey).seq (vecU8Split A auth.macKey) (by decide)

def ekSentCt1ReceivedUcSplit (A : RustAlloc) {F : ShaCompress}
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    SplitBytes 104 (fun a => ekSentCt1ReceivedUcAt A a uc) :=
  have h : ∀ a, authenticatorAt A a uc.auth ∗
      (vecU8 A (a + BitVec.ofNat 64 48) uc.dk ∗
        (vecU8 A ((a + BitVec.ofNat 64 48) + BitVec.ofNat 64 24) uc.ct1 ∗
          ((((a + BitVec.ofNat 64 48) + BitVec.ofNat 64 24) + BitVec.ofNat 64 24) ↦₆₄ uc.epoch))) =
      ekSentCt1ReceivedUcAt A a uc := by
    intro a; unfold ekSentCt1ReceivedUcAt
    have h72 : (a + 48#64) + 24#64 = a + 72#64 := by bv_omega
    have h96 : (a + 72#64) + 24#64 = a + 96#64 := by bv_omega
    simp only [BitVec.ofNat_eq_ofNat, h72, h96, sepConj_assoc]
  congr h ((authenticatorSplit A uc.auth).seq
    ((vecU8Split A uc.dk).seq ((vecU8Split A uc.ct1).seq (pointsTo64 uc.epoch) (by decide)) (by decide))
    (by decide))

noncomputable def ekSentCt1ReceivedSplit (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    SplitBytes 504 (fun a => ekSentCt1ReceivedAt A a st) :=
  (ekSentCt1ReceivedUcSplit A st.uc).seq (polyDecoderSplit A st.receiving_ct2) (by decide)

/-- Relocating `P src` to `P dst ∗ memRegion src n` via `memcpy(dst, src, n)`. -/
def memcpySpec {n : Nat} {P : BitVec 64 → SepProp} (_ : SplitBytes n P) :
    Spec (BitVec 64 × BitVec 64) where
  pre := fun (dst, src) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ s0.readReg64 .x2 = BitVec.ofNat 64 n⌝ ∗
      memRegion dst n ∗ P src
  post := fun (dst, src) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = dst⌝ ∗
      P dst ∗ memRegion src n

theorem memcpy_ok {prog : Program} {entry : BitVec 64} {n : Nat} {P : BitVec 64 → SepProp}
    (S : SplitBytes n P) (hn : n < 2 ^ 64)
    (hmc : subroutine_ok prog entry sessionMemcpyRegionSpec) :
    subroutine_ok prog entry (S.memcpySpec) := by
  refine subroutine_ok_outcome_intro fun ⟨dst, src⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [memcpySpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (S.to_bytes src))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  rcases h2 with ⟨bs, h3⟩
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  rcases h3 with ⟨hlen, h4⟩
  have hpre_mc : s0.mem ⊨ sessionMemcpyRegionSpec.pre (dst, src, bs) s0 ∗ (S.heap bs ∗ R) := by
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by rw [hx2, hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]⟩, ?_⟩
    rw [hlen]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h4
  refine (hmc.to_outcome (dst, src, bs) (S.heap bs ∗ R) s0 hpc hrun hpre_mc hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_sf, htr⟩, hpost_mem⟩
    dsimp only [memcpySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hx0_sf⟩, ?_⟩
    have harrange :
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (S.heap bs ∗ R) =
        (((dst ↦ₛ bs) ∗ S.heap bs) ∗ (src ↦ₛ bs)) ∗ R := by ac_rfl
    rw [harrange] at hpost_mem
    have hsrc_mr : (src ↦ₛ bs) ⊢ memRegion src n := hlen ▸ pointsToBytes_entails_memRegion src bs
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono (S.of_bytes dst bs hlen) hsrc_mr)) hpost_mem
  · right; left
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · right; right; left
    refine ⟨code, hex, ?_⟩
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · right; right; right
    refine ⟨hoom, ?_⟩
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

end SplitBytes

/-! ## Pure Model Unfolding Lemmas for `recv_ct2_chunk` -/

theorem recv_ct2_chunk_eq_do {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) :
    self.recv_ct2_chunk K epoch chunk =
      if epoch != self.uc.epoch then
        .error (.panic (.chunkedEpochMismatch "v1/chunked/send_ek.rs:200" epoch self.uc.epoch))
      else (do
        let receivingCt2 ← StatesResult.ofPanic
          ((PolyDecoder.addChunk self.receiving_ct2 chunk).mapError PolyPanic.toSpqrPanic)
        let decoded? ← StatesResult.ofPanic (receivingCt2.decodedMessage.mapError PolyPanic.toSpqrPanic)
        match decoded? with
        | some ct2Full =>
          if ct2Full.length < 128 then
            .error (.panic (.decodedSliceBounds "v1/chunked/send_ek.rs:209" ct2Full.length 128))
          else
            let mac := ct2Full.drop 128
            let ct2 := ct2Full.take 128
            let (uc', sec) ← (do
              let ss ← StatesResult.ofPanic (decaps K self.uc.dk self.uc.ct1 ct2)
              let info := sckaKeyInfoPrefix ++ toBEBytes 8 self.uc.epoch
              let ss ← pure (spqrHkdfWith F (List.replicate 32 0#8) ss info 32)
              let auth ← pure (Authenticator.update F self.uc.auth self.uc.epoch ss)
              let ct1Full := self.uc.ct1 ++ ct2
              let verifyRes ← StatesResult.ofPanic (Authenticator.verifyCtError F auth self.uc.epoch ct1Full mac)
              match verifyRes with
              | .error _ => .error (.err .macVerifyFailed)
              | .ok () =>
                if self.uc.epoch == BitVec.allOnes 64 then
                  .error (.panic .unchunkedRecvCt2EpochOverflow)
                else
                  .ok ({ epoch := self.uc.epoch + 1#64, auth := auth },
                    { epoch := self.uc.epoch, secret := ss }))
            let receivingHdr ← pure polyDecoderNew96
            .ok (.done ({ uc := uc', receiving_hdr := receivingHdr }, sec))
        | none =>
          .ok (.stillReceiving { uc := self.uc, receiving_ct2 := receivingCt2 })) :=
  rfl

theorem recv_ct2_chunk_isPanic_of_epoch_ne {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (hne : epoch ≠ self.uc.epoch) :
    (self.recv_ct2_chunk K epoch chunk).isPanic = true := by
  refine (congrArg StatesResult.isPanic (recv_ct2_chunk_eq_do self epoch chunk)).trans ?_
  have hbeq : (epoch != self.uc.epoch) = true := by
    rw [bne_iff_ne]; exact hne
  simp [hbeq, StatesResult.isPanic, StatesError.isPanic]

theorem recv_ct2_chunk_eq_stillReceiving {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingCt2 : PolyDecoder)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_ct2 chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok none) :
    self.recv_ct2_chunk K epoch chunk =
      .ok (.stillReceiving { uc := self.uc, receiving_ct2 := receivingCt2 }) := by
  refine (recv_ct2_chunk_eq_do self epoch chunk).trans ?_
  subst hepoch
  simp [hadd, hdec, Except.mapError, Bind.bind, Except.bind, StatesResult.ofPanic]

theorem recv_ct2_chunk_isPanic_of_lt_128 {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_ct2 chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hlt : ct2Full.length < 128) :
    (self.recv_ct2_chunk K epoch chunk).isPanic = true := by
  refine (congrArg StatesResult.isPanic (recv_ct2_chunk_eq_do self epoch chunk)).trans ?_
  subst hepoch
  simp [hadd, hdec, hlt, Except.mapError, Bind.bind, Except.bind,
    StatesResult.ofPanic, StatesResult.isPanic, StatesError.isPanic]

theorem decaps_eq_match (K : MlKem) (dk ct1 ct2 : Bytes) :
    decaps K dk ct1 ct2 =
      match (if h1 : ct1.length = CIPHERTEXT1_SIZE then some ⟨ct1, h1⟩ else none),
            (if h2 : ct2.length = CIPHERTEXT2_SIZE then some ⟨ct2, h2⟩ else none),
            (if h3 : dk.length = DECAPSULATION_KEY_SIZE then some ⟨dk, h3⟩ else none) with
      | some ct1Vec, some ct2Vec, some dkVec => .ok (K.decaps dkVec ct1Vec ct2Vec).toList
      | _, _, _ => .error (.decapsBadSize dk.length ct1.length ct2.length) :=
  rfl

theorem decaps_of_ct1_len_ne (K : MlKem) (dk ct1 ct2 : Bytes) (hct1 : ct1.length ≠ 960) :
    decaps K dk ct1 ct2 = .error (.decapsBadSize dk.length ct1.length ct2.length) := by
  rw [decaps_eq_match]
  have h1 : ct1.length ≠ CIPHERTEXT1_SIZE := hct1
  rw [dite_eq_right (by simpa using h1)]

theorem decaps_of_dk_len_ne (K : MlKem) (dk ct1 ct2 : Bytes)
    (hct1 : ct1.length = 960) (hct2 : ct2.length = 128) (hdk : dk.length ≠ 2400) :
    decaps K dk ct1 ct2 = .error (.decapsBadSize dk.length ct1.length ct2.length) := by
  rw [decaps_eq_match]
  have h1 : ct1.length = CIPHERTEXT1_SIZE := hct1
  have h2 : ct2.length = CIPHERTEXT2_SIZE := hct2
  have h3 : dk.length ≠ DECAPSULATION_KEY_SIZE := hdk
  rw [dite_eq_left h1, dite_eq_left h2, dite_eq_right (by simpa using h3)]

theorem decaps_eq_ok (K : MlKem) (dk ct1 ct2 : Bytes)
    (hct1 : ct1.length = 960) (hct2 : ct2.length = 128) (hdk : dk.length = 2400) :
    decaps K dk ct1 ct2 = .ok (K.decaps ⟨dk, hdk⟩ ⟨ct1, hct1⟩ ⟨ct2, hct2⟩).toList := by
  rw [decaps_eq_match]
  have h1 : ct1.length = CIPHERTEXT1_SIZE := hct1
  have h2 : ct2.length = CIPHERTEXT2_SIZE := hct2
  have h3 : dk.length = DECAPSULATION_KEY_SIZE := hdk
  rw [dite_eq_left h1, dite_eq_left h2, dite_eq_left h3]

theorem recv_ct2_chunk_isPanic_of_ct1_len_ne {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_ct2 chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge : ¬ ct2Full.length < 128)
    (hct1 : self.uc.ct1.length ≠ 960) :
    (self.recv_ct2_chunk K epoch chunk).isPanic = true := by
  refine (congrArg StatesResult.isPanic (recv_ct2_chunk_eq_do self epoch chunk)).trans ?_
  subst hepoch
  have hdecaps := decaps_of_ct1_len_ne K self.uc.dk self.uc.ct1 (ct2Full.take 128) hct1
  simp [hadd, hdec, hge, hdecaps, Except.mapError, Bind.bind, Except.bind,
    StatesResult.ofPanic, StatesResult.isPanic, StatesError.isPanic]

theorem recv_ct2_chunk_isPanic_of_dk_len_ne {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_ct2 chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge : ¬ ct2Full.length < 128)
    (hct1 : self.uc.ct1.length = 960)
    (hdk : self.uc.dk.length ≠ 2400) :
    (self.recv_ct2_chunk K epoch chunk).isPanic = true := by
  refine (congrArg StatesResult.isPanic (recv_ct2_chunk_eq_do self epoch chunk)).trans ?_
  subst hepoch
  have hct2' : (ct2Full.take 128).length = 128 := by
    rw [List.length_take]; omega
  have hdecaps := decaps_of_dk_len_ne K self.uc.dk self.uc.ct1 (ct2Full.take 128)
    hct1 hct2' hdk
  simp [hadd, hdec, hge, hdecaps, Except.mapError, Bind.bind, Except.bind,
    StatesResult.ofPanic, StatesResult.isPanic, StatesError.isPanic]

theorem hmacWith_take_macSize (F : ShaCompress) (k m : Bytes) :
    (hmacWith F k m).take Authenticator.macSize = hmacWith F k m := by
  apply List.take_of_length_le
  rw [LibsignalSpqrV1.length_hmacWith]

theorem macCtUnchecked_eq_hmacWith (F : ShaCompress) (auth : Authenticator) (ep : Epoch) (ct : Bytes) :
    auth.macCtUnchecked F ep ct = hmacWith F auth.macKey (Authenticator.ctLabel ++ toBEBytes 8 ep ++ ct) := by
  unfold Authenticator.macCtUnchecked
  exact hmacWith_take_macSize F _ _

theorem auth_update_macKey_length_32 (F : ShaCompress) (auth : Authenticator) (ep : Epoch) (k : Bytes) :
    (auth.update F ep k).macKey.length = 32 := by
  dsimp [Authenticator.update, hkdfToVecUnchecked, hkdfToSliceUnchecked]
  rw [List.length_drop, length_spqrHkdfWith]

theorem auth_update_rootKey_length_32 (F : ShaCompress) (auth : Authenticator) (ep : Epoch) (k : Bytes) :
    (auth.update F ep k).rootKey.length = 32 := by
  dsimp [Authenticator.update, hkdfToVecUnchecked, hkdfToSliceUnchecked]
  rw [List.length_take, length_spqrHkdfWith]
  decide

theorem recv_ct2_chunk_after_decaps {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_ct2 chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge : ¬ ct2Full.length < 128)
    (hct1 : self.uc.ct1.length = 960)
    (hdk : self.uc.dk.length = 2400) :
    let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
    let ss_raw := (K.decaps ⟨self.uc.dk, hdk⟩ ⟨self.uc.ct1, hct1⟩ ⟨ct2Full.take 128, hct2⟩).toList
    let info := sckaKeyInfoPrefix ++ toBEBytes 8 self.uc.epoch
    let ss := spqrHkdfWith F (List.replicate 32 0#8) ss_raw info 32
    let auth' := self.uc.auth.update F self.uc.epoch ss
    let ct1Full := self.uc.ct1 ++ ct2Full.take 128
    let mac := ct2Full.drop 128
    self.recv_ct2_chunk K epoch chunk =
      match auth'.verifyCtError F self.uc.epoch ct1Full mac with
      | .error p => .error (.panic (.spqr p))
      | .ok (.error _) => .error (.err .macVerifyFailed)
      | .ok (.ok ()) =>
        if self.uc.epoch == BitVec.allOnes 64 then
          .error (.panic .unchunkedRecvCt2EpochOverflow)
        else
          .ok (.done ({ uc := { epoch := self.uc.epoch + 1#64, auth := auth' },
                        receiving_hdr := polyDecoderNew96 },
                      { epoch := self.uc.epoch, secret := ss })) := by
  intro hct2 ss_raw info ss auth' ct1Full mac
  refine (recv_ct2_chunk_eq_do self epoch chunk).trans ?_
  subst hepoch
  have hdecaps : decaps K self.uc.dk self.uc.ct1 (ct2Full.take 128) = .ok ss_raw :=
    decaps_eq_ok K self.uc.dk self.uc.ct1 (ct2Full.take 128) hct1 hct2 hdk
  dsimp only [info, ss, auth', ct1Full, mac]
  simp only [hadd, hdec, hge, hdecaps,
    Except.mapError, StatesResult.ofPanic, Bind.bind, Except.bind, Pure.pure, Except.pure,
    ToStatesPanic.toStatesPanic, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  cases Authenticator.verifyCtError F
    (Authenticator.update F self.uc.auth self.uc.epoch
      (spqrHkdfWith F (List.replicate 32 0#8) ss_raw (sckaKeyInfoPrefix ++ toBEBytes 8 self.uc.epoch) 32))
    self.uc.epoch (self.uc.ct1 ++ ct2Full.take 128) (ct2Full.drop 128) with
  | error p => rfl
  | ok v =>
    cases v with
    | error e => rfl
    | ok u =>
      cases u
      cases (self.uc.epoch == BitVec.allOnes 64) <;> rfl

theorem verifyCtError_of_mac_gt_32 (F : ShaCompress) (auth : Authenticator) (ep : Epoch)
    (ct mac : Bytes)
    (hk : auth.macKey.length < 2 ^ 32)
    (hd : (Authenticator.ctLabel ++ toBEBytes 8 ep ++ ct).length < 2 ^ 32)
    (hm : ¬ mac.length ≤ 32) :
    auth.verifyCtError F ep ct mac = .error .compareBounds := by
  simp [Authenticator.verifyCtError, Authenticator.verifyCt,
    Authenticator.macCt_of_lt F auth ep ct hk hd, LibsignalSpqrV1.compare, hm,
    Bind.bind, Except.bind, Except.map]

theorem verifyCtError_of_mac_le_32 (F : ShaCompress) (auth : Authenticator) (ep : Epoch)
    (ct mac : Bytes)
    (hk : auth.macKey.length < 2 ^ 32)
    (hd : (Authenticator.ctLabel ++ toBEBytes 8 ep ++ ct).length < 2 ^ 32)
    (hm : mac.length ≤ 32) :
    auth.verifyCtError F ep ct mac =
      if compare_prefix mac (auth.macCtUnchecked F ep ct) != 0#8 then
        .ok (.error .macVerifyFailed)
      else
        .ok (.ok ()) := by
  unfold Authenticator.verifyCtError
  rw [Authenticator.verifyCt_eq_ok_prefix F auth ep ct mac hk hd hm]
  unfold Authenticator.verifyCt_prefix
  by_cases hc : compare_prefix mac (auth.macCtUnchecked F ep ct) != 0#8 <;>
    simp [hc, Except.map, Except.mapError, AuthError.toError]

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
