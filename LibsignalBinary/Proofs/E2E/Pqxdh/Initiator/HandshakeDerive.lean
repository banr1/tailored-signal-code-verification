/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitiatorCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesDecode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import ProofLib.SepLogic.WPp

/-!
# PQXDH Protocol Model and `<HandshakeKeys>::derive` Verification

Defines the pure PQXDH initiator/responder protocol model (`Primitives`, `HandshakeHdr`,
`PreKeyBundleInput`, `Model.initiateKeys`, `Model.acceptKeys`) and proves `subroutine_ok` for
`<HandshakeKeys>::derive` (`0x1ceb8`, Block `59`) on `tripleRatchetProgAt`,
`tripleRatchetProgAtExt`, and `[LibsignalPlacement]`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
namespace CryptoVerification.E2E.Pqxdh.Initiator
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
abbrev Bytes := List UInt8
abbrev DRKey := SignalPqxdh.DRKey
abbrev DRKey.toBytes96 := @SignalPqxdh.DRKey.toBytes96
abbrev MessageKeys := SignalPqxdh.MessageKeys
def TAG_EC_DJB     : UInt8 := 0x05
def TAG_KYBER_1024 : UInt8 := 0x08
def F_X25519 : Bytes := List.replicate 32 0xFF
abbrev discontinuityBytes : Bytes := F_X25519
def INFO_PQXDH : Bytes := "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8.toList
abbrev hkdfInfoLabel : Bytes := INFO_PQXDH
def INFO_RATCHET : Bytes := "WhisperRatchet".toUTF8.toList
def INFO_MSG_KEYS : Bytes := "WhisperMessageKeys".toUTF8.toList
def encodeEC (pk : Bytes) : Bytes := TAG_EC_DJB :: pk
def encodeKEM (pk : Bytes) : Bytes := TAG_KYBER_1024 :: pk
def decodeEC (b : Bytes) : Option Bytes :=
  match b with
  | tag :: rest => if tag == TAG_EC_DJB && rest.length == 32 then some rest else none
  | [] => none
def decodeKEM (b : Bytes) : Option Bytes :=
  match b with
  | tag :: rest => if tag == TAG_KYBER_1024 && rest.length == 1568 then some rest else none
  | [] => none
theorem encodeEC_ne_encodeKEM (pkDh pkKem : Bytes) :
    encodeEC pkDh ≠ encodeKEM pkKem := by
  intro h
  injection h with htag _
  revert htag
  decide
structure Primitives where
  x25519          : Bytes → Bytes → Bytes
  x25519Base      : Bytes → Bytes
  isCanonical     : Bytes → Bool
  sigPkGen        : Bytes → Bytes
  sigSign         : Bytes → Bytes → Bytes → Bytes
  sigVerify       : Bytes → Bytes → Bytes → Bool
  sha512          : Bytes → Bytes
  scalarMul       : Bytes → Bytes → Bytes
  scalarAdd       : Bytes → Bytes → Bytes
  scalarFromBytesModOrder : Bytes → Bytes
  scalarFromWide  : Bytes → Bytes
  montToEd        : Bytes → UInt8 → Option Bytes
  isTorsionFree   : Bytes → Bool
  edNeg           : Bytes → Bytes
  doubleScalarMulBasepoint : Bytes → Bytes → Bytes → Bytes
  compress        : Bytes → Bytes
  kemKeyGen       : Bytes → (Bytes × Bytes)
  kemEncaps       : Bytes → Bytes → Option (Bytes × Bytes)
  kemDecaps       : Bytes → Bytes → Option Bytes
  hkdfDerive96    : Bytes → DRKey
  rootCreateChain : Bytes → Bytes → (Bytes × Bytes)
  chainKdfSeed    : Bytes → Bytes
  chainKdfNext    : Bytes → Bytes
  spqrInitSend    : Bytes → Bytes → Option (Bytes × Option Bytes × Bytes)
  spqrInitRecv    : Bytes → Bytes → Option (Bytes × Option Bytes)
  deriveMsgKeys   : Bytes → Option Bytes → MessageKeys
  aeadEnc         : MessageKeys → Bytes → Bytes → Bytes
  aeadDec         : MessageKeys → Bytes → Bytes → Option Bytes
  pow8            : Bytes → Bytes
  isValidDhTriple : Bytes → Bytes → Bytes → Bool
  sha256Compress  : Bytes → Bytes → Bytes
  sha512Compress  : Bytes → Bytes → Bytes
  aesEncBlock     : Bytes → Bytes → Bytes
  aesDecBlock     : Bytes → Bytes → Bytes
abbrev HandshakePrimitives := Primitives
abbrev Primitives.isCanonicalEC (P : Primitives) : Bytes → Bool := P.isCanonical
def Primitives.isValidKemPk (_P : Primitives) (pk : Bytes) : Bool := pk.length == 1568
def buildSecrets (dh1 dh2 dh3 : Bytes) (dh4? : Option Bytes) (ss : Bytes) : Bytes :=
  match dh4? with
  | none     => F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ ss
  | some dh4 => F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss
def firstMsgAD (ikA ikB ephAPk pqRatchetMsg : Bytes) : Bytes :=
  SignalPqxdh.firstMsgAD ikA ikB ephAPk pqRatchetMsg
structure PreKeyBundleInput where
  -- 32B Bob wire identity public key (used for both sigVerify and DH2)
  ikB      : Bytes
  spkId    : UInt32
  spkB     : Bytes                  -- 32B signed EC prekey public key
  spkSig   : Bytes                  -- 64B XEdDSA signature over `encodeEC spkB`
  opkB?    : Option (UInt32 × Bytes) -- optional (opkId, 32B one-time EC prekey public key)
  pqspkId  : UInt32
  pqspkB   : Bytes                  -- 1568B Kyber1024 public key
  pqspkSig : Bytes                  -- 64B XEdDSA signature over `encodeKEM pqspkB`
  deriving DecidableEq, Repr, Inhabited
structure HandshakeHdr where
  ikAPk   : Bytes        -- 32B Alice wire identity public key
  ekAPk   : Bytes        -- 32B Alice ephemeral `base_key`
  spkId   : UInt32
  opkId?  : Option UInt32
  pqspkId : UInt32
  kemCt   : Bytes        -- 1568B `kyber_ciphertext`
  deriving DecidableEq, Repr, Inhabited
structure PreKeyMsg where
  hdr          : HandshakeHdr
  ephAPk       : Bytes -- 32B Alice Epoch-1 sending ratchet public key (`SignalMessage.ratchet_key`)
  pqRatchetMsg : Bytes -- SPQR initial token (`SignalMessage.pq_ratchet`)
  aeadCt       : Bytes -- encrypted inner `SignalMessage` body + 8-byte MAC tag
  deriving DecidableEq, Repr, Inhabited
structure InitiateKeysInput where
  ikASk       : Bytes -- 32B Alice identity secret scalar
  ikAPk       : Bytes -- 32B Alice wire identity public key
  ekASk       : Bytes -- 32B freshly sampled PQXDH ephemeral scalar (`base_key`)
  kemCoins    : Bytes -- 32B freshly sampled Kyber1024 encapsulation randomness
  trustedPeer : Bool  -- result of `is_trusted_identity` store hook
  bundle      : PreKeyBundleInput
  deriving DecidableEq, Repr, Inhabited
structure InitiateInput extends InitiateKeysInput where
  ephASk    : Bytes -- 32B freshly sampled Epoch-1 sending ratchet scalar (`ratchet.rs:77`)
  spqrCoins : Bytes -- 32B freshly sampled SPQR send randomness (`triple_ratchet.rs:97`)
  plaintext : Bytes -- initial message payload
  deriving DecidableEq, Repr, Inhabited
structure AcceptKeysInput where
  ikBSk       : Bytes        -- 32B Bob identity secret scalar
  ikBPk       : Bytes        -- 32B Bob wire identity public key
  spkBSk      : Bytes        -- 32B Bob signed EC prekey secret scalar
  spkBPk      : Bytes        -- 32B Bob signed EC prekey public key
  opkBSk?     : Option Bytes -- 32B Bob one-time EC prekey secret scalar (if `hdr.opkId? = some id`)
  pqspkBSk    : Bytes        -- 3168B Bob Kyber1024 secret key
  pqspkBPk    : Bytes        -- 1568B Bob Kyber1024 public key
  trustedPeer : Bool         -- result of `is_trusted_identity` store hook
  replayOk    : Bool         -- result of `mark_kyber_pre_key_used(pqspkId, spkId, ekAPk)`
  hdr         : HandshakeHdr
  deriving DecidableEq, Repr, Inhabited
structure AcceptInput where
  keysInp : AcceptKeysInput
  msg     : PreKeyMsg
  deriving DecidableEq, Repr, Inhabited
def dhOptNonZero (dh? : Option Bytes) : Bool :=
  match dh? with
  | none => true
  | some dh => dh != List.replicate 32 0
def Model.initiateKeys (P : Primitives) (inp : InitiateKeysInput) :
    Option (DRKey × HandshakeHdr) := do
  «guard» inp.trustedPeer
  «guard» (P.sigVerify inp.bundle.ikB (encodeEC inp.bundle.spkB) inp.bundle.spkSig)
  «guard» (P.sigVerify inp.bundle.ikB (encodeKEM inp.bundle.pqspkB) inp.bundle.pqspkSig)
  let (ss, kemCt) ← P.kemEncaps inp.bundle.pqspkB inp.kemCoins
  let ekAPk := P.x25519Base inp.ekASk
  let dh1   := P.x25519 inp.ikASk inp.bundle.spkB
  «guard» (dh1 != List.replicate 32 0)
  let dh2   := P.x25519 inp.ekASk inp.bundle.ikB
  «guard» (dh2 != List.replicate 32 0)
  let dh3   := P.x25519 inp.ekASk inp.bundle.spkB
  «guard» (dh3 != List.replicate 32 0)
  let dh4?  := inp.bundle.opkB?.map (fun (_, opkPk) => P.x25519 inp.ekASk opkPk)
  «guard» (dhOptNonZero dh4?)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let drKey   := P.hkdfDerive96 secrets
  let hdr : HandshakeHdr := {
    ikAPk   := inp.ikAPk
    ekAPk   := ekAPk
    spkId   := inp.bundle.spkId
    opkId?  := inp.bundle.opkB?.map Prod.fst
    pqspkId := inp.bundle.pqspkId
    kemCt   := kemCt
  }
  some (drKey, hdr)
def Model.acceptKeys (P : Primitives) (inp : AcceptKeysInput) : Option DRKey := do
  «guard» inp.trustedPeer
  «guard» inp.replayOk
  «guard» (inp.hdr.ikAPk.length == 32)
  «guard» (inp.hdr.ekAPk.length == 32)
  «guard» (P.isCanonical inp.hdr.ekAPk)
  let dh1  := P.x25519 inp.spkBSk inp.hdr.ikAPk
  «guard» (dh1 != List.replicate 32 0)
  let dh2  := P.x25519 inp.ikBSk  inp.hdr.ekAPk
  «guard» (dh2 != List.replicate 32 0)
  let dh3  := P.x25519 inp.spkBSk inp.hdr.ekAPk
  «guard» (dh3 != List.replicate 32 0)
  let dh4? ← match inp.hdr.opkId?, inp.opkBSk? with
    | none,   none       => some none
    | some _, some opkSk => some (some (P.x25519 opkSk inp.hdr.ekAPk))
    | _,      _          => none
  «guard» (dhOptNonZero dh4?)
  let ss ← P.kemDecaps inp.pqspkBSk inp.hdr.kemCt
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  some (P.hkdfDerive96 secrets)
def Model.initiate (P : Primitives) (inp : InitiateInput) :
    Option (DRKey × Bytes × Bytes × PreKeyMsg) := do
  let (drKey, hdr) ← Model.initiateKeys P inp.toInitiateKeysInput
  let ephAPk    := P.x25519Base inp.ephASk
  let dhRatchet := P.x25519 inp.ephASk inp.bundle.spkB
  «guard» (dhRatchet != List.replicate 32 0)
  let (rk1, ck1_0) := P.rootCreateChain drKey.rootKey dhRatchet
  let mkSeed := P.chainKdfSeed ck1_0
  let ck1_1  := P.chainKdfNext ck1_0
  let (_pqrStA, spqrSalt?, pqRatchetMsg) ← P.spqrInitSend drKey.pqrKey inp.spqrCoins
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  let ad     := firstMsgAD inp.ikAPk inp.bundle.ikB ephAPk pqRatchetMsg
  let aeadCt := P.aeadEnc deriveMessageKeys ad inp.plaintext
  let msg : PreKeyMsg := {
    hdr          := hdr
    ephAPk       := ephAPk
    pqRatchetMsg := pqRatchetMsg
    aeadCt       := aeadCt
  }
  some (drKey, rk1, ck1_1, msg)
def Model.accept (P : Primitives) (inp : AcceptInput) :
    Option (DRKey × Bytes × Bytes × Bytes) := do
  «guard» (inp.keysInp.hdr == inp.msg.hdr)
  let drKey ← Model.acceptKeys P inp.keysInp
  «guard» (inp.msg.ephAPk.length == 32)
  let dhRatchet := P.x25519 inp.keysInp.spkBSk inp.msg.ephAPk
  «guard» (dhRatchet != List.replicate 32 0)
  let (rk1, ck1_0) := P.rootCreateChain drKey.rootKey dhRatchet
  let mkSeed := P.chainKdfSeed ck1_0
  let ck1_1  := P.chainKdfNext ck1_0
  let (_pqrStB, spqrSalt?) ← P.spqrInitRecv drKey.pqrKey inp.msg.pqRatchetMsg
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  let ad := firstMsgAD inp.msg.hdr.ikAPk inp.keysInp.ikBPk inp.msg.ephAPk inp.msg.pqRatchetMsg
  let pt ← P.aeadDec deriveMessageKeys ad inp.msg.aeadCt
  some (drKey, rk1, ck1_1, pt)
def xeddsaVerifyRef (P : Primitives) (pk m sig : Bytes) : Bool :=
  if pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0) then
    let signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
    match P.montToEd pk signBit with
    | none => false
    | some edPk =>
      let capA := P.compress edPk
      let minusCapA := P.edNeg edPk
      let capR := sig.take 32
      let sRaw := sig.drop 32
      let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
      let h := P.scalarFromWide (P.sha512 (capR ++ capA ++ m))
      let sScalar := P.scalarFromBytesModOrder sClamped
      let capRCheck := P.compress (P.doubleScalarMulBasepoint h minusCapA sScalar)
      capRCheck == capR
  else
    false
def scalarIsInRange (pk : Bytes) : Bool :=
  ((pk.getD 31 0 &&& 0x80) == 0) &&
    !(pk.getD 0 0 >= 0xED &&
      (pk.drop 1).take 30 == List.replicate 30 0xFF &&
      (pk.getD 31 0 &&& 0x7F) == 0x7F)
def isCanonicalRef (P : Primitives) (pk : Bytes) : Bool :=
  if pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && scalarIsInRange pk then
    match P.montToEd pk 0 with
    | some edPt => P.isTorsionFree edPt
    | none => false
  else
    false
abbrev xeddsaCanonRef := isCanonicalRef
def fitBytesRef (n : Nat) (bs : Bytes) : Bytes := bs.take n ++ List.replicate (n - bs.length) 0
@[simp]
theorem fitBytesRef_length (n : Nat) (bs : Bytes) : (fitBytesRef n bs).length = n := by
  simp [fitBytesRef]
  omega
theorem fitBytesRef_of_length_eq {n : Nat} {bs : Bytes} (h : bs.length = n) :
    fitBytesRef n bs = bs := by
  subst h
  simp [fitBytesRef]
def clampScalar25519 (sk : Bytes) : Bytes :=
  let s := fitBytesRef 32 sk
  (s.take 1).map (fun b => b &&& 0xF8) ++ (s.drop 1).take 30 ++
    ((s.drop 31).take 1).map (fun b => (b &&& 0x7F) ||| 0x40)
theorem clampScalar25519_length (sk : Bytes) :
    (clampScalar25519 sk).length = 32 := by
  have hFit : (fitBytesRef 32 sk).length = 32 := fitBytesRef_length 32 sk
  simp [clampScalar25519, hFit]
def sha256InitState : Bytes :=
  [ 0x6a, 0x09, 0xe6, 0x67, 0xbb, 0x67, 0xae, 0x85, 0x3c, 0x6e, 0xf3, 0x72, 0xa5, 0x4f, 0xf5, 0x3a,
    0x51, 0x0e, 0x52, 0x7f, 0x9b, 0x05, 0x68, 0x8c, 0x1f, 0x83, 0xd9, 0xab, 0x5b, 0xe0, 0xcd, 0x19 ]
def sha512InitState : Bytes :=
  [ 0x6a, 0x09, 0xe6, 0x67, 0xf3, 0xbc, 0xc9, 0x08, 0xbb, 0x67, 0xae, 0x85, 0x84, 0xca, 0xa7, 0x3b,
    0x3c, 0x6e, 0xf3, 0x72, 0xfe, 0x94, 0xf8, 0x2b, 0xa5, 0x4f, 0xf5, 0x3a, 0x5f, 0x1d, 0x36, 0xf1,
    0x51, 0x0e, 0x52, 0x7f, 0xad, 0xe6, 0x82, 0xd1, 0x9b, 0x05, 0x68, 0x8c, 0x2b, 0x3e, 0x6c, 0x1f,
    0x1f, 0x83, 0xd9, 0xab, 0xfb, 0x41, 0xbd, 0x6b, 0x5b, 0xe0, 0xcd, 0x19, 0x13, 0x7e, 0x21, 0x79 ]
def encodeBitLen64BE (byteLen : Nat) : Bytes :=
  let bitLen : UInt64 := byteLen.toUInt64 * 8
  [ ((bitLen >>> 56) &&& 0xFF).toUInt8, ((bitLen >>> 48) &&& 0xFF).toUInt8,
    ((bitLen >>> 40) &&& 0xFF).toUInt8,
    ((bitLen >>> 32) &&& 0xFF).toUInt8, ((bitLen >>> 24) &&& 0xFF).toUInt8,
      ((bitLen >>> 16) &&& 0xFF).toUInt8,
    ((bitLen >>>  8) &&& 0xFF).toUInt8, ( bitLen         &&& 0xFF).toUInt8 ]
def encodeBitLen128BE (byteLen : Nat) : Bytes := List.replicate 8 0 ++ encodeBitLen64BE byteLen
def sha256Pad (msg : Bytes) : Bytes :=
  let rem := (msg.length + 9) % 64
  let zeroPadLen := if rem == 0 then 0 else 64 - rem
  msg ++ [0x80] ++ List.replicate zeroPadLen 0 ++ encodeBitLen64BE msg.length
def sha512Pad (msg : Bytes) : Bytes :=
  let rem := (msg.length + 17) % 128
  let zeroPadLen := if rem == 0 then 0 else 128 - rem
  msg ++ [0x80] ++ List.replicate zeroPadLen 0 ++ encodeBitLen128BE msg.length
def chunkBlocks (blockSize : Nat) (bs : Bytes) : List Bytes :=
  let numBlocks := bs.length / blockSize
  (List.range numBlocks).map (fun i => (bs.drop (i * blockSize)).take blockSize)
def sha256Step (P : Primitives) (state32 block64 : Bytes) : Bytes :=
  fitBytesRef 32 (P.sha256Compress (fitBytesRef 32 state32) block64)
def sha512Step (P : Primitives) (state64 block128 : Bytes) : Bytes :=
  fitBytesRef 64 (P.sha512Compress (fitBytesRef 64 state64) block128)
def sha256Ref (P : Primitives) (msg : Bytes) : Bytes :=
  let blocks := chunkBlocks 64 (sha256Pad msg)
  fitBytesRef 32 (blocks.foldl (sha256Step P) sha256InitState)
def sha512Ref (P : Primitives) (msg : Bytes) : Bytes :=
  let blocks := chunkBlocks 128 (sha512Pad msg)
  fitBytesRef 64 (blocks.foldl (sha512Step P) sha512InitState)
theorem sha256Ref_length (P : Primitives) (msg : Bytes) :
    (sha256Ref P msg).length = 32 := by
  simp [sha256Ref, fitBytesRef_length]
theorem sha512Ref_length (P : Primitives) (msg : Bytes) :
    (sha512Ref P msg).length = 64 := by
  simp [sha512Ref, fitBytesRef_length]
def xorBytes (a b : Bytes) : Bytes := List.zipWith (· ^^^ ·) a b
@[simp]
theorem xorBytes_length (a b : Bytes) :
    (xorBytes a b).length = min a.length b.length := by
  simp [xorBytes]
def hmacSha256Ref (P : Primitives) (key msg : Bytes) : Bytes :=
  let key' := if key.length > 64 then sha256Ref P key else key
  let kPad := fitBytesRef 64 key'
  let ipad := xorBytes kPad (List.replicate 64 0x36)
  let opad := xorBytes kPad (List.replicate 64 0x5c)
  sha256Ref P (opad ++ sha256Ref P (ipad ++ msg))
theorem hmacSha256Ref_length (P : Primitives) (key msg : Bytes) :
    (hmacSha256Ref P key msg).length = 32 := by
  simp [hmacSha256Ref, sha256Ref_length]
def hkdfExtractRef (P : Primitives) (salt? : Option Bytes) (ikm : Bytes) : Bytes :=
  let salt := match salt? with
    | some s => s
    | none   => List.replicate 32 0
  hmacSha256Ref P salt ikm
def hkdfExpand96Ref (P : Primitives) (prk info : Bytes) : DRKey :=
  let t1 := hmacSha256Ref P prk (info ++ [0x01])
  let t2 := hmacSha256Ref P prk (t1 ++ info ++ [0x02])
  let t3 := hmacSha256Ref P prk (t2 ++ info ++ [0x03])
  { rootKey := t1, chainKey := t2, pqrKey := t3 }
def hkdfDerive96Ref (P : Primitives) (secrets : Bytes) : DRKey :=
  hkdfExpand96Ref P (hkdfExtractRef P none secrets) INFO_PQXDH
def rootCreateChainRef (P : Primitives) (rk dhRatchet : Bytes) : (Bytes × Bytes) :=
  let prk := hkdfExtractRef P (some rk) dhRatchet
  let t1  := hmacSha256Ref P prk (INFO_RATCHET ++ [0x01])
  let t2  := hmacSha256Ref P prk (t1 ++ INFO_RATCHET ++ [0x02])
  (t1, t2)
def chainKdfSeedRef (P : Primitives) (ck : Bytes) : Bytes := hmacSha256Ref P ck [0x01]
def chainKdfNextRef (P : Primitives) (ck : Bytes) : Bytes := hmacSha256Ref P ck [0x02]
def deriveMsgKeysRef (P : Primitives) (mkSeed : Bytes) (spqrSalt? : Option Bytes) : MessageKeys :=
  let prk := hkdfExtractRef P spqrSalt? mkSeed
  let t1  := hmacSha256Ref P prk (INFO_MSG_KEYS ++ [0x01])
  let t2  := hmacSha256Ref P prk (t1 ++ INFO_MSG_KEYS ++ [0x02])
  let t3  := hmacSha256Ref P prk (t2 ++ INFO_MSG_KEYS ++ [0x03])
  { cipherKey := t1, macKey := t2, iv := t3.take 16 }
def pkcs7Pad16 (pt : Bytes) : Bytes :=
  let padM1 := 15 - (pt.length % 16)
  let padLen := padM1 + 1
  pt ++ List.replicate padLen padLen.toUInt8
def pkcs7Unpad16 (padded : Bytes) : Option Bytes :=
  match padded.reverse with
  | [] => none
  | padByte :: revRest =>
    let padLen := padByte.toNat
    if padLen >= 1 && padLen <= 16 && padded.length % 16 == 0 &&
       revRest.take (padLen - 1) == List.replicate (padLen - 1) padByte then
      some (revRest.drop (padLen - 1)).reverse
    else
      none
def toBlocks16 (bs : Bytes) : List Bytes :=
  if bs.length >= 16 then
    bs.take 16 :: toBlocks16 (bs.drop 16)
  else
    []
termination_by bs.length
decreasing_by
  simp_wf
  omega
def fromBlocks16 (blks : List Bytes) : Bytes := blks.foldr (· ++ ·) []
def cbcEncBlocksWith (aesEnc : Bytes → Bytes → Bytes) (key iv : Bytes) : List Bytes → List Bytes
  | [] => []
  | blk :: rest =>
    let ctBlk :=
      fitBytesRef 16 (aesEnc (fitBytesRef 32 key) (xorBytes (fitBytesRef 16 blk) (fitBytesRef 16
      iv)))
    ctBlk :: cbcEncBlocksWith aesEnc key ctBlk rest
def cbcDecBlocksWith (aesDec : Bytes → Bytes → Bytes) (key iv : Bytes) : List Bytes → List Bytes
  | [] => []
  | ctBlk :: rest =>
    let ptBlk :=
      xorBytes (fitBytesRef 16 (aesDec (fitBytesRef 32 key) (fitBytesRef 16 ctBlk))) (fitBytesRef 16
      iv)
    ptBlk :: cbcDecBlocksWith aesDec key (fitBytesRef 16 ctBlk) rest
abbrev cbcEncBlocks (P : Primitives) (key iv : Bytes) (blks : List Bytes) : List Bytes :=
  cbcEncBlocksWith P.aesEncBlock key iv blks
abbrev cbcDecBlocks (P : Primitives) (key iv : Bytes) (blks : List Bytes) : List Bytes :=
  cbcDecBlocksWith P.aesDecBlock key iv blks
def aes256CbcEncRef (P : Primitives) (key iv pt : Bytes) : Bytes :=
  fromBlocks16 (cbcEncBlocks P key iv (toBlocks16 (pkcs7Pad16 pt)))
def aes256CbcDecRef (P : Primitives) (key iv ct : Bytes) : Option Bytes :=
  if ct.length >= 16 && ct.length % 16 == 0 then
    pkcs7Unpad16 (fromBlocks16 (cbcDecBlocks P key iv (toBlocks16 ct)))
  else
    none
def aes256CbcHmacEncRef (P : Primitives) (mk : MessageKeys) (ad pt : Bytes) : Bytes :=
  let ct  := aes256CbcEncRef P mk.cipherKey mk.iv pt
  let mac := (hmacSha256Ref P mk.macKey (SignalPqxdh.aeadMacInput ad ct)).take 8
  ct ++ mac
def aes256CbcHmacDecRef (P : Primitives) (mk : MessageKeys) (ad ctAndTag : Bytes) : Option Bytes :=
  if ctAndTag.length >= 24 then
    let ctLen := ctAndTag.length - 8
    let ct    := ctAndTag.take ctLen
    let tag   := ctAndTag.drop ctLen
    let expectedTag := (hmacSha256Ref P mk.macKey (SignalPqxdh.aeadMacInput ad ct)).take 8
    if tag == expectedTag then
      aes256CbcDecRef P mk.cipherKey mk.iv ct
    else
      none
  else
    none
private theorem xorByte_self_right (x y : UInt8) : (x ^^^ y) ^^^ y = x := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      apply congrArg UInt8.ofBitVec
      change (bx ^^^ by_) ^^^ by_ = bx
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
theorem xorBytes_self_right (a b : Bytes) (h : a.length = b.length) :
    xorBytes (xorBytes a b) b = a := by
  induction a generalizing b with
  | nil => simp [xorBytes]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [xorBytes, List.zipWith_cons_cons, xorByte_self_right]
      congr 1
      exact ih ys h
theorem toBlocks16_append_of_len16 {b : Bytes} (hb : b.length = 16) (rest : Bytes) :
    toBlocks16 (b ++ rest) = b :: toBlocks16 rest := by
  rw [toBlocks16]
  simp [hb, List.take_left' hb, List.drop_left' hb]
theorem toBlocks16_fromBlocks16 (blks : List Bytes) (h : ∀ b ∈ blks, b.length = 16) :
    toBlocks16 (fromBlocks16 blks) = blks := by
  induction blks with
  | nil =>
    rw [fromBlocks16, List.foldr, toBlocks16]
    rfl
  | cons b rest ih =>
    simp only [fromBlocks16, List.foldr]
    rw [toBlocks16_append_of_len16 (h b (by simp)), ← fromBlocks16, ih (fun x hx =>
      h x (by simp [hx]))]
abbrev Primitives.toSignalPqxdh (P : Primitives) : SignalPqxdh.Primitives where
  x25519 := P.x25519
  x25519Base := P.x25519Base
  isCanonical := P.isCanonical
  sigPkGen := P.sigPkGen
  sigSign := P.sigSign
  sigVerify := P.sigVerify
  sha512 := P.sha512
  scalarMul := P.scalarMul
  scalarAdd := P.scalarAdd
  scalarFromBytesModOrder := P.scalarFromBytesModOrder
  scalarFromWide := P.scalarFromWide
  montToEd := P.montToEd
  isTorsionFree := P.isTorsionFree
  edNeg := P.edNeg
  doubleScalarMulBasepoint := P.doubleScalarMulBasepoint
  compress := P.compress
  kemKeyGen := P.kemKeyGen
  kemEncaps := P.kemEncaps
  kemDecaps := P.kemDecaps
  hkdfDerive96 := P.hkdfDerive96
  rootCreateChain := P.rootCreateChain
  chainKdfSeed := P.chainKdfSeed
  chainKdfNext := P.chainKdfNext
  spqrInitSend := P.spqrInitSend
  spqrInitRecv := P.spqrInitRecv
  deriveMsgKeys := P.deriveMsgKeys
  aeadEnc := P.aeadEnc
  aeadDec := P.aeadDec
  pow8 := P.pow8
  isValidDhTriple := P.isValidDhTriple
  sha256Compress := P.sha256Compress
  sha512Compress := P.sha512Compress
  aesEncBlock := P.aesEncBlock
  aesDecBlock := P.aesDecBlock
def StructuralPrims (P : Primitives) : Prop := Shared.StructuralPrims P.toSignalPqxdh
namespace StructuralPrims
variable {P : Primitives}
theorem sha256Compress_len (h : StructuralPrims P) :
    ∀ st blk, (P.sha256Compress st blk).length = 32 :=
  Shared.StructuralPrims.sha256Compress_len h
theorem sha512Compress_len (h : StructuralPrims P) :
    ∀ st blk, (P.sha512Compress st blk).length = 64 :=
  Shared.StructuralPrims.sha512Compress_len h
theorem aesEncBlock_len (h : StructuralPrims P) :
    ∀ k blk, (P.aesEncBlock k blk).length = 16 :=
  Shared.StructuralPrims.aesEncBlock_len h
theorem aesDecBlock_len (h : StructuralPrims P) :
    ∀ k blk, (P.aesDecBlock k blk).length = 16 :=
  Shared.StructuralPrims.aesDecBlock_len h
theorem sha512_eq_ref (h : StructuralPrims P) :
    ∀ m, P.sha512 m = sha512Ref P m :=
  Shared.StructuralPrims.sha512_eq_ref h
theorem hkdfDerive96_eq_ref (h : StructuralPrims P) :
    ∀ secrets, P.hkdfDerive96 secrets = hkdfDerive96Ref P secrets :=
  Shared.StructuralPrims.hkdfDerive96_eq_ref h
theorem rootCreateChain_eq_ref (h : StructuralPrims P) :
    ∀ rk dh, P.rootCreateChain rk dh = rootCreateChainRef P rk dh :=
  Shared.StructuralPrims.rootCreateChain_eq_ref h
theorem chainKdfSeed_eq_ref (h : StructuralPrims P) :
    ∀ ck, P.chainKdfSeed ck = chainKdfSeedRef P ck :=
  Shared.StructuralPrims.chainKdfSeed_eq_ref h
theorem chainKdfNext_eq_ref (h : StructuralPrims P) :
    ∀ ck, P.chainKdfNext ck = chainKdfNextRef P ck :=
  Shared.StructuralPrims.chainKdfNext_eq_ref h
theorem deriveMsgKeys_eq_ref (h : StructuralPrims P) :
    ∀ mkSeed salt?, P.deriveMsgKeys mkSeed salt? = deriveMsgKeysRef P mkSeed salt? :=
  Shared.StructuralPrims.deriveMsgKeys_eq_ref h
theorem sigVerify_eq_xeddsaVerifyRef (h : StructuralPrims P) :
    ∀ pk m sig, P.sigVerify pk m sig = xeddsaVerifyRef P pk m sig :=
  Shared.StructuralPrims.sigVerify_eq_xeddsaVerifyRef h
theorem isCanonical_eq_isCanonicalRef (h : StructuralPrims P) :
    ∀ pk, P.isCanonical pk = isCanonicalRef P pk :=
  Shared.StructuralPrims.isCanonical_eq_isCanonicalRef h
theorem x25519_len (h : StructuralPrims P) :
    ∀ k p, (P.x25519 k p).length = 32 :=
  Shared.StructuralPrims.x25519_len h
theorem x25519Base_len (h : StructuralPrims P) :
    ∀ k, (P.x25519Base k).length = 32 :=
  Shared.StructuralPrims.x25519Base_len h
theorem sha512_len (h : StructuralPrims P) :
    ∀ m, (P.sha512 m).length = 64 :=
  Shared.StructuralPrims.sha512_len h
theorem scalarFromBytesModOrder_len (h : StructuralPrims P) :
    ∀ b, (P.scalarFromBytesModOrder b).length = 32 :=
  Shared.StructuralPrims.scalarFromBytesModOrder_len h
theorem scalarFromWide_len (h : StructuralPrims P) :
    ∀ b, (P.scalarFromWide b).length = 32 :=
  Shared.StructuralPrims.scalarFromWide_len h
theorem montToEd_len (h : StructuralPrims P) :
    ∀ u s pt, P.montToEd u s = some pt → pt.length = 160 :=
  Shared.StructuralPrims.montToEd_len h
theorem edNeg_len (h : StructuralPrims P) :
    ∀ pt, (P.edNeg pt).length = 160 :=
  Shared.StructuralPrims.edNeg_len h
theorem doubleScalarMulBasepoint_len (h : StructuralPrims P) :
    ∀ h1 a s, (P.doubleScalarMulBasepoint h1 a s).length = 160 :=
  Shared.StructuralPrims.doubleScalarMulBasepoint_len h
theorem compress_len (h : StructuralPrims P) :
    ∀ pt, (P.compress pt).length = 32 :=
  Shared.StructuralPrims.compress_len h
theorem kemEncaps_isSome (h : StructuralPrims P) :
    ∀ pk r, pk.length = 1568 → r.length = 32 → (P.kemEncaps pk r).isSome = true :=
  Shared.StructuralPrims.kemEncaps_isSome h
theorem kemEncaps_len (h : StructuralPrims P) :
    ∀ pk r ss ct, P.kemEncaps pk r = some (ss, ct) → ss.length = 32 ∧ ct.length = 1568 :=
  Shared.StructuralPrims.kemEncaps_len h
theorem kemDecaps_isSome (h : StructuralPrims P) :
    ∀ sk ct, sk.length = 3168 → ct.length = 1568 → (P.kemDecaps sk ct).isSome = true :=
  Shared.StructuralPrims.kemDecaps_isSome h
theorem kemDecaps_len (h : StructuralPrims P) :
    ∀ sk ct ss, P.kemDecaps sk ct = some ss → ss.length = 32 :=
  Shared.StructuralPrims.kemDecaps_len h
theorem spqrInitSend_some (h : StructuralPrims P) :
    ∀ k r, (P.spqrInitSend k r).isSome = true :=
  Shared.StructuralPrims.spqrInitSend_some h
end StructuralPrims
def fitBytes (n : Nat) (bs : Bytes) : Bytes := bs.take n ++ List.replicate (n - bs.length) 0
abbrev pqxdhAcceptSym : String :=
  "<libsignal_protocol::pqxdh::Pqxdh as libsignal_protocol::handshake::Handshake>::accept"
abbrev initializeBobSessionSym : String := "libsignal_protocol::ratchet::initialize_bob_session"
abbrev withSenderChainSym : String :=
  "<libsignal_protocol::state::session::SessionState>::with_sender_chain"
abbrev vecAppendElementsSym : String := "<alloc::vec::Vec<u8>>::append_elements [local#1]"
abbrev ecPubKeyIsCanonicalSym : String := "<libsignal_core::curve::PublicKey>::is_canonical"
abbrev hkdfExtractSym : String := "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract"
abbrev hkdfExpandMultiInfoSym : String :=
  "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info"
abbrev calculateAgreementSym : String := "<libsignal_core::curve::PrivateKey>::calculate_agreement"
abbrev ecPubKeySerializeSym : String := "<libsignal_core::curve::PublicKey>::serialize"
abbrev privKeySerializeSym : String := "<libsignal_core::curve::PrivateKey>::serialize"
abbrev kyberDecapsStub : String := "libsignal_protocol::kem::kyber1024::decapsulate"
abbrev dalekMontToEdStub : String := "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards"
abbrev dalekTorsionFreeStub : String :=
  "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free"
@[simp] theorem fitBytes_length (n : Nat) (bs : Bytes) : (fitBytes n bs).length = n := by
  simp [fitBytes]
  omega
theorem fitBytes_of_length_eq {n : Nat} {bs : Bytes} (h : bs.length = n) : fitBytes n bs = bs := by
  subst h
  simp [fitBytes]
def bytesToBv8 (bs : Bytes) : List (BitVec 8) :=
  bs.map (fun b => BitVec.ofNat 8 b.toNat)
def fitBv8 (n : Nat) (bs : Bytes) : List (BitVec 8) :=
  (bytesToBv8 bs).take n ++ List.replicate (n - (bytesToBv8 bs).length) 0#8
def readBytesU8 (m : Memory) (ptr : BitVec 64) (n : Nat) : Bytes :=
  (m.readBytes ptr n).map (fun b => UInt8.ofNat b.toNat)
theorem fitBv8_length (n : Nat) (bs : Bytes) : (fitBv8 n bs).length = n := by
  simp [fitBv8]
  omega
theorem fitBv8_eq_bytesToBv8 {n : Nat} {bs : Bytes} (h : bs.length = n) :
    fitBv8 n bs = bytesToBv8 bs := by
  subst h
  have hlen : (bytesToBv8 bs).length = bs.length := by simp [bytesToBv8]
  simp [fitBv8, ← hlen]
def u64le (w : BitVec 64) : List (BitVec 8) :=
  List.ofFn (fun (i : Fin 8) => BitVec.ofNat 8 ((w.toNat >>> (8 * i.val)) % 256))
abbrev pqxdhHookStack : Nat := 4096
abbrev pqxdhEntryStack : Nat := 16384
abbrev pqxdhCompositeStack : Nat := 32768
abbrev _root_.CryptoVerification.RustHeap.RustAlloc.allocated
    (A : RustAlloc) (ptr : BitVec 64) (size : Nat) : SepProp :=
  A.live ptr size 1
def boxSliceU8 (A : RustAlloc) (boxPtr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ dataPtr : BitVec 64, ⌜dataPtr ≠ 0⌝ ∗ (boxPtr ↦₆₄ dataPtr) ∗ ((boxPtr +
    8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (dataPtr ↦ₛ bs) ∗
    A.live dataPtr bs.length 1
def vecU8 (A : RustAlloc) (vecPtr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ dataPtr : BitVec 64, ⌜dataPtr ≠ 0⌝ ∗ (vecPtr ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((vecPtr +
    8#64) ↦₆₄ dataPtr) ∗
    ((vecPtr + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (dataPtr ↦ₛ bs) ∗ A.live dataPtr bs.length 1
def vecU8View (vecPtr dataPtr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (vecPtr ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((vecPtr + 8#64) ↦₆₄ dataPtr) ∗ ((vecPtr +
    16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
  (dataPtr ↦ₛ bs)
def encodeU32LE (w : UInt32) : Bytes :=
  [ UInt8.ofNat (w.toNat % 256)
  , UInt8.ofNat ((w.toNat >>> 8) % 256)
  , UInt8.ofNat ((w.toNat >>> 16) % 256)
  , UInt8.ofNat ((w.toNat >>> 24) % 256) ]
def encodeU64LE (w : BitVec 64) : Bytes :=
  List.ofFn (fun (i : Fin 8) => UInt8.ofNat ((w.toNat >>> (8 * i.val)) % 256))
def storedSessionCommitBytes (peerIk rk rcvCk spqrState sndCk : Bytes) (sndIdx : UInt32 :=
    0) : Bytes :=
  fitBytes 32 peerIk ++ fitBytes 32 rk ++ fitBytes 32 rcvCk ++
    fitBytes 32 spqrState ++ fitBytes 32 sndCk ++ encodeU32LE sndIdx
structure KyberDecapsCall where
  skPtr  : BitVec 64
  sk3168 : Bytes
  ctPtr  : BitVec 64
  ct1568 : Bytes
  outPtr : BitVec 64
def kyberDecapsOutBytes (P : Primitives) (sk ct : Bytes) : Bytes :=
  (P.kemDecaps sk ct).getD []
theorem fitBv8_kyberDecapsOutBytes_eq {P : Primitives} {sk ct ss : Bytes}
    (h : P.kemDecaps sk ct = some ss) (hlen : ss.length = 32) :
    fitBv8 32 (kyberDecapsOutBytes P sk ct) = bytesToBv8 ss := by
  simp [kyberDecapsOutBytes, h, fitBv8_eq_bytesToBv8 hlen]
def kyberDecapsStubSpec (P : Primitives) : Spec KyberDecapsCall where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.skPtr ∧ s.readReg64 .x1 = g.ctPtr ∧ s.readReg64 .x8 = g.outPtr ∧
      g.sk3168.length = 3168 ∧ g.ct1568.length = 1568 ∧
      (P.kemDecaps g.sk3168 g.ct1568).isSome⌝ ∗ (g.skPtr ↦ₛ bytesToBv8 g.sk3168) ∗
        (g.ctPtr ↦ₛ bytesToBv8 g.ct1568) ∗
      memRegion g.outPtr 32 ∗ stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (g.skPtr ↦ₛ bytesToBv8 g.sk3168) ∗ (g.ctPtr ↦ₛ bytesToBv8 g.ct1568) ∗
      (g.outPtr ↦ₛ fitBv8 32 (kyberDecapsOutBytes P g.sk3168 g.ct1568)) ∗
        stackAt s0.sp pqxdhHookStack
def vecHeaderBv8 (cap dataPtr len : BitVec 64) : List (BitVec 8) :=
  unpack64 cap ++ (unpack64 dataPtr ++ unpack64 len)
@[simp]
theorem vecHeaderBv8_length (cap dataPtr len : BitVec 64) :
    (vecHeaderBv8 cap dataPtr len).length = 24 := rfl
structure CryptoUnaryGhost where
  inPtr   : BitVec 64
  inBytes : Bytes
def cryptoBoolRegStubSpec (pred : Bytes → Bool) (inLen : Nat) (_img : Obj.Image := default) :
    Spec CryptoUnaryGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧ g.inBytes.length = inLen⌝ ∗ (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧ (sf.readReg64 .x0).setWidth 32 =
      (if pred g.inBytes then 1#32 else 0#32)⌝ ∗ (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      stackAt s0.sp pqxdhHookStack
def cryptoInPlaceStubSpec (fn : Bytes → Bytes) (len : Nat) (_img : Obj.Image := default) :
    Spec CryptoUnaryGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧ g.inBytes.length = len⌝ ∗ (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ fitBv8 len (fn g.inBytes)) ∗ stackAt s0.sp pqxdhHookStack
def revWords32 (bs : Bytes) : Bytes :=
  ((bs.take 4).reverse ++
   ((bs.drop 4).take 4).reverse ++
   ((bs.drop 8).take 4).reverse ++
   ((bs.drop 12).take 4).reverse ++
   ((bs.drop 16).take 4).reverse ++
   ((bs.drop 20).take 4).reverse ++
   ((bs.drop 24).take 4).reverse ++
   ((bs.drop 28).take 4).reverse)
def dalekMontToEdOutBv8 (P : Primitives) (inBytes : Bytes) (signBit : UInt8) : List (BitVec 8) :=
  match P.montToEd inBytes signBit with
  | some edPt => u64le 1#64 ++ fitBv8 160 edPt
  | none      => u64le 0#64 ++ List.replicate 160 0#8
structure DalekMontToEdGhost where
  inBytes : Bytes
  signBit : UInt8
  inPtr   : BitVec 64
  outPtr  : BitVec 64
def dalekMontToEdStubSpec (P : Primitives) (_img : Obj.Image :=
    default) : Spec DalekMontToEdGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧ (s.readReg64 .x1).setWidth 8 = BitVec.ofNat 8 g.signBit.toNat ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inBytes.length = 32⌝ ∗ (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ memRegion g.outPtr 168 ∗
        stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      (g.outPtr ↦ₛ dalekMontToEdOutBv8 P g.inBytes g.signBit) ∗
      stackAt s0.sp pqxdhHookStack
def rustPanicOnOom {α : Type} (_img : Obj.Image) : α → State → State → SepProp :=
  fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap
def u32be (w : UInt32) : Bytes :=
  [ UInt8.ofNat ((w.toNat >>> 24) % 256)
  , UInt8.ofNat ((w.toNat >>> 16) % 256)
  , UInt8.ofNat ((w.toNat >>> 8) % 256)
  , UInt8.ofNat (w.toNat % 256) ]
def encBytes (bs : Bytes) : Bytes :=
  encodeU32LE (UInt32.ofNat bs.length) ++ bs
def encOptBytes (o : Option Bytes) : Bytes :=
  match o with
  | none => [0]
  | some bs => (1 : UInt8) :: encBytes bs
abbrev DRKey.ck0 (dk : DRKey) : Bytes := dk.chainKey
abbrev DRKey.rk0 (dk : DRKey) : Bytes := dk.rootKey
abbrev Model.deriveDRKeys (P : Primitives) (secrets : Bytes) : DRKey := P.hkdfDerive96 secrets
abbrev AcceptInput.toAcceptKeysInput (inp : AcceptInput) : AcceptKeysInput := inp.keysInp
abbrev AcceptInput.ephAPk (inp : AcceptInput) : Bytes := inp.msg.ephAPk
def handshakeKeysBytes100 (dk : DRKey) : Bytes :=
  dk.rootKey ++ dk.pqrKey ++ dk.ck0 ++ [0, 0, 0, 0]
def handshakeKeysResultOk104 (dk : DRKey) : Bytes :=
  [0, 0, 0, 0] ++ handshakeKeysBytes100 dk
def MessageKeys.toBytes80 (mk : MessageKeys) : Bytes :=
  mk.cipherKey ++ mk.macKey ++ mk.iv
def WellSizedAcceptKeysInput (inp : AcceptKeysInput) : Prop :=
  inp.ikBSk.length = 32 ∧ inp.ikBPk.length = 32 ∧ inp.spkBSk.length = 32 ∧ inp.spkBPk.length = 32 ∧
  (∀ sk, inp.opkBSk? = some sk → sk.length = 32) ∧ inp.pqspkBSk.length = 3168 ∧
    inp.pqspkBPk.length = 1568 ∧ inp.hdr.ikAPk.length = 32 ∧
  inp.hdr.ekAPk.length = 32 ∧ inp.hdr.kemCt.length = 1568
def WellSizedInitiateInput (inp : InitiateInput) : Prop :=
  inp.ikASk.length = 32 ∧ inp.ikAPk.length = 32 ∧ inp.ekASk.length = 32 ∧ inp.kemCoins.length = 32 ∧
    inp.ephASk.length = 32 ∧
  inp.spqrCoins.length = 32 ∧ inp.bundle.ikB.length = 32 ∧ inp.bundle.spkB.length = 32 ∧
    inp.bundle.spkSig.length = 64 ∧
  (∀ id pk, inp.bundle.opkB? = some (id, pk) → pk.length = 32) ∧ inp.bundle.pqspkB.length = 1568 ∧
    inp.bundle.pqspkSig.length = 64
def WellSizedAcceptInput (inp : AcceptInput) : Prop :=
  WellSizedAcceptKeysInput inp.toAcceptKeysInput ∧ inp.keysInp.hdr.opkId?.isSome =
    inp.keysInp.opkBSk?.isSome ∧
  inp.msg.hdr = inp.keysInp.hdr ∧ inp.msg.ephAPk.length = 32 ∧ inp.msg.pqRatchetMsg.length = 32 ∧
    8 ≤ inp.msg.aeadCt.length
def serializeAcceptKeysInputAt (basePtr : BitVec 64) (inp : AcceptKeysInput) : Bytes :=
  let opkPubGhost32 :=
    fitBytes 32
      (encodeU32LE inp.hdr.spkId ++
       encodeU32LE inp.hdr.pqspkId ++
       [if inp.hdr.opkId?.isSome then 1 else 0] ++
       encodeU32LE (inp.hdr.opkId?.getD 0))
  let struct304 :=
    fitBytes 32 inp.ikBPk ++
    fitBytes 32 inp.ikBSk ++
    fitBytes 32 inp.spkBPk ++
    fitBytes 32 inp.spkBSk ++
    fitBytes 32 inp.hdr.ikAPk ++
    fitBytes 32 inp.hdr.ekAPk ++
    encodeU64LE (basePtr + 304#64) ++ encodeU64LE 1568#64 ++
    encodeU64LE (basePtr + 1872#64) ++ encodeU64LE 3168#64 ++
    encodeU64LE (basePtr + 5040#64) ++
    [if inp.opkBSk?.isSome then 1 else 0] ++
    opkPubGhost32 ++
    fitBytes 32 (inp.opkBSk?.getD (List.replicate 32 0)) ++
    [0, if inp.trustedPeer then 1 else 0, if inp.replayOk then 1 else 0, 0, 0, 0, 0]
  let arena6321 :=
    fitBytes 1568 inp.pqspkBPk ++
    fitBytes 3168 inp.pqspkBSk ++
    encodeU64LE (basePtr + 5056#64) ++ encodeU64LE 1569#64 ++
    fitBytes 1569 (encodeKEM inp.hdr.kemCt)
  let witnessTail :=
    encBytes inp.ikBSk ++ encBytes inp.ikBPk ++
    encodeU32LE inp.hdr.spkId ++ encBytes inp.spkBSk ++ encBytes inp.spkBPk ++
    encOptBytes inp.opkBSk? ++
    encodeU32LE inp.hdr.pqspkId ++ encBytes inp.pqspkBSk ++ encBytes inp.pqspkBPk ++
    [if inp.trustedPeer then 1 else 0, if inp.replayOk then 1 else 0] ++
    encBytes inp.hdr.ikAPk ++ encBytes inp.hdr.ekAPk ++
    encodeU32LE inp.hdr.spkId ++
    (match inp.hdr.opkId? with
     | some id => (1 : UInt8) :: encodeU32LE id
     | none    => [0]) ++
    encodeU32LE inp.hdr.pqspkId ++ encBytes inp.hdr.kemCt
  struct304 ++ arena6321 ++ witnessTail
abbrev serializeAcceptKeysInput (inp : AcceptKeysInput) : Bytes :=
  serializeAcceptKeysInputAt 0#64 inp
def pollReadyOkWord : BitVec 64 := 0xfffffffffffffffe#64
def pollResultUnitOk48 (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₆₄ pollReadyOkWord) ∗ memRegion (outPtr + 8#64) 40
def pollResultErr48 (outPtr : BitVec 64) : SepProp :=
  (∃∗ tag : BitVec 64, ⌜tag ≠ pollReadyOkWord⌝ ∗ (outPtr ↦₆₄ tag)) ∗ memRegion (outPtr + 8#64) 40 ∗
    anyHeap
theorem ent_anyHeap (R : SepProp) : R ⊢ anyHeap := entails_anyHeap R
structure KeyCanonicalGhost where
  keyPtr   : BitVec 64
  keyBytes : Bytes
def ecPubKeyIsCanonicalSpec (P : Primitives) (img : Obj.Image) :
    Spec KeyCanonicalGhost :=
  Spec.inImage {
    pre := fun g s =>
      ⌜s.readReg64 .x0 = g.keyPtr ∧ g.keyBytes.length = 32⌝ ∗ (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗
        stackAt s.sp pqxdhEntryStack
    post := fun g s0 sf =>
      ⌜sf.trace = s0.trace ∧ (sf.readReg64 .x0).setWidth 8 =
        (if P.isCanonicalEC g.keyBytes then 1#8 else 0#8)⌝ ∗
      (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗ stackAt s0.sp pqxdhEntryStack
  } img
structure AcceptKeysCallGhost where
  inp    : AcceptKeysInput
  argPtr : BitVec 64
  outPtr : BitVec 64
def pqxdhAcceptSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec AcceptKeysCallGhost :=
  Spec.inImage {
    pre := fun g s =>
      ⌜s.readReg64 .x0 = g.argPtr ∧ s.readReg64 .x8 = g.outPtr ∧ g.inp.trustedPeer = true ∧
        g.inp.replayOk = true ∧
        g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧ WellSizedAcceptKeysInput g.inp⌝ ∗
      (g.argPtr ↦ₛ bytesToBv8 (serializeAcceptKeysInputAt g.argPtr g.inp)) ∗
        memRegion g.outPtr 104 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
      stackAt s.sp pqxdhEntryStack ∗ A.pool
    post := fun g s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗ (g.argPtr ↦ₛ bytesToBv8 (serializeAcceptKeysInputAt g.argPtr g.inp)) ∗
        (match Model.acceptKeys P g.inp with
       | some drKey =>
         g.outPtr ↦ₛ bytesToBv8 (handshakeKeysResultOk104 drKey)
       | none =>
         (∃∗ tag : BitVec 8, ⌜tag ≠ 0#8⌝ ∗ (g.outPtr ↦₈ tag)) ∗ memRegion (g.outPtr + 1#64) 103 ∗
         anyHeap) ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
      stackAt s0.sp pqxdhEntryStack ∗ A.pool
    onPanic := rustPanicOnOom img
  } img
structure PqxdhHookContracts (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) : Prop where
  alloc            : AllocHooks A absHooks
  kyberDecaps      : HookSat absHooks kyberDecapsStub (kyberDecapsStubSpec P)
  dalekMontToEd    : HookSat absHooks dalekMontToEdStub (dalekMontToEdStubSpec P img)
  dalekTorsionFree : HookSat absHooks dalekTorsionFreeStub
                       (cryptoBoolRegStubSpec P.isTorsionFree 160 img)
noncomputable abbrev PP (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (absHooks : String → Option (State → State)) : Program :=
  tripleRatchetProgAt b C ctl absHooks
theorem hookSat_tripleRatchetExterns' {α : Type} (C : Crypto) (ctl : BitVec 64)
    (absHooks : String → Option (State → State)) {sym : String} {spec : Spec α}
    (heq : tripleRatchetExterns C ctl absHooks sym = absHooks sym)
    (h : HookSat absHooks sym spec) :
    HookSat (tripleRatchetExterns C ctl absHooks) sym spec := by
  unfold HookSat at *; rwa [heq]
def sha256IVBytesLE : List (BitVec 8) :=
  [ 0x67#8, 0xe6#8, 0x09#8, 0x6a#8, 0x85#8, 0xae#8, 0x67#8, 0xbb#8, 0x72#8, 0xf3#8, 0x6e#8, 0x3c#8,
    0x3a#8, 0xf5#8, 0x4f#8, 0xa5#8,
    0x7f#8, 0x52#8, 0x0e#8, 0x51#8, 0x8c#8, 0x68#8, 0x05#8, 0x9b#8, 0xab#8, 0xd9#8, 0x83#8, 0x1f#8,
      0x19#8, 0xcd#8, 0xe0#8, 0x5b ]
@[irreducible] def roStop (pc : BitVec 64) : BitVec 64 := pc
theorem reaches_pc_keepsFrozen {prog : Program} {target_pc : BitVec 64} {s : State}
    {Q oom : State → Prop} (h : reaches_pc prog target_pc s Q oom) :
    reaches_pc prog target_pc s (fun sf => s.mem.KeepsFrozen sf.mem ∧ Q sf) oom := by
  intro hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, hQ⟩ | hoom⟩ := h hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hsteps.keepsFrozen, hQ⟩⟩
  · exact ⟨sf, hsteps, Or.inr hoom⟩
theorem SepWP.done_ro {prog : Program} {mid : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mid)
    (hrun : s.status = .Running)
    (hpost : post s P) :
    SepWP prog (roStop mid) s P post := by
  unfold roStop
  exact SepWP.done hpc hrun hpost
theorem subroutine_ok_inImage {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (img : Obj.Image) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp fun _ hout => hout
def pqxdhShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝
theorem pqxdhShim_hookOk : HookOk hookNoop pqxdhShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [pqxdhShimSpec, hookNoop, retHook, id_eq, State.trace_setPC, satisfies_pure_sepConj,
    true_and, emp_sepConj] at hpre ⊢
  exact hpre
def pqxdhMemcpyRegionSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := memcpyRegionSpec.pre
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs)
theorem hookMemcpy_region_trace_ok : HookOk hookMemcpy pqxdhMemcpyRegionSpec := by
  intro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hookMemcpy_region_ok (dst, src, bs) R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_st, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [memcpyRegionSpec, pqxdhMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj]
      at hpost ⊢
    exact ⟨⟨hpost.1, rfl⟩, hpost.2⟩
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom_st, hpost⟩
theorem memRegion_zero (a : BitVec 64) : memRegion a 0 = emp := by
  have hb := IsBlock.pointsToBytes a []
  rw [pointsToBytes_nil] at hb
  exact IsBlock.eq (IsBlock.memRegion a 0) hb
    fun _ => ⟨fun _ => ⟨by simp, by simp⟩, fun _ => trivial⟩
theorem memRegion_eight (a : BitVec 64) : memRegion a 8 = ∃∗ v, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩
theorem memRegion_cells (a : BitVec 64) (k : Nat) (h : 8 * k ≤ 2 ^ 64) :
    memRegion a (8 * k) = cells a k := by
  induction k generalizing a with
  | zero => exact memRegion_zero a
  | succ k ih =>
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, memRegion_split a 8 (8 * k) (by omega),
      memRegion_eight, ih _ (by omega), cells_succ, sepExists_sepConj_left]
theorem stackAt_split_cells (sp : BitVec 64) (n k : Nat) (h : n + 8 * k ≤ 2 ^ 64) :
    stackAt sp (n + 8 * k) =
      stackAt (sp - BitVec.ofNat 64 (8 * k)) n ∗ cells (sp - BitVec.ofNat 64 (8 * k)) k := by
  simp only [stackAt]
  rw [memRegion_split _ n (8 * k) h, memRegion_cells _ k (by omega)]
  generalize hj : 8 * k = j at *
  have e1 : sp - BitVec.ofNat 64 (n + j) = sp - BitVec.ofNat 64 j - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + j) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 j := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]
theorem stackAt_split_top (sp : BitVec 64) (m n : Nat) (h : m + n ≤ 2 ^ 64) :
    stackAt sp (m + n) =
      memRegion (sp - BitVec.ofNat 64 (m + n)) m ∗ stackAt sp n := by
  simp only [stackAt]
  rw [memRegion_split _ m n h]
  have e : sp - BitVec.ofNat 64 (m + n) + BitVec.ofNat 64 m = sp - BitVec.ofNat 64 n := by
    rw [Nat.add_comm, BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [e]
theorem allocFailedIn_of_eq {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]
theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h
theorem bytesToBv8_append (xs ys : Bytes) :
    bytesToBv8 (xs ++ ys) = bytesToBv8 xs ++ bytesToBv8 ys := by
  unfold bytesToBv8
  exact List.map_append
def hkdfExpandRef (P : Primitives) (prk info : Bytes) (okmLen : Nat) : Bytes :=
  let t1 := hmacSha256Ref P prk (info ++ [0x01])
  let t2 := hmacSha256Ref P prk (t1 ++ info ++ [0x02])
  let t3 := hmacSha256Ref P prk (t2 ++ info ++ [0x03])
  (t1 ++ t2 ++ t3).take okmLen
theorem hkdfExpandRef_length (P : Primitives) (prk info : Bytes) (okmLen : Nat)
    (h : okmLen ≤ 96) :
    (hkdfExpandRef P prk info okmLen).length = okmLen := by
  unfold hkdfExpandRef
  simp only [List.length_take, List.length_append, hmacSha256Ref_length]
  omega
theorem hkdfExtractRef_length (P : Primitives) (salt? : Option Bytes) (ikm : Bytes) :
    (hkdfExtractRef P salt? ikm).length = 32 := by
  unfold hkdfExtractRef
  exact hmacSha256Ref_length P _ ikm
def pqxdhHmacKeyBlock (P : Primitives) (key : Bytes) : Bytes :=
  fitBytesRef 64 (if key.length > 64 then sha256Ref P key else key)
def pqxdhHmacInnerInit (P : Primitives) (key : Bytes) : Bytes :=
  sha256Step P sha256InitState (xorBytes (pqxdhHmacKeyBlock P key) (List.replicate 64 0x36))
def pqxdhHmacOuterInit (P : Primitives) (key : Bytes) : Bytes :=
  sha256Step P sha256InitState (xorBytes (pqxdhHmacKeyBlock P key) (List.replicate 64 0x5c))
theorem revWords32_length {bs : Bytes} (h : bs.length = 32) :
    (revWords32 bs).length = 32 := by
  simp [revWords32, h]
theorem pqxdhHmacInnerInit_length (P : Primitives) (key : Bytes) :
    (pqxdhHmacInnerInit P key).length = 32 := by
  simp [pqxdhHmacInnerInit, sha256Step, fitBytesRef_length]
theorem pqxdhHmacOuterInit_length (P : Primitives) (key : Bytes) :
    (pqxdhHmacOuterInit P key).length = 32 := by
  simp [pqxdhHmacOuterInit, sha256Step, fitBytesRef_length]
def pqxdhHmacStateFullAt (a : BitVec 64) (innerSt : Bytes) (nBlocks : Nat) (outerSt : Bytes)
    (tail : List (BitVec 8)) : SepProp :=
  ⌜tail.length < 64⌝ ∗ (a ↦ₛ tail) ∗ memRegion (a + BitVec.ofNat 64 tail.length) (63 -
    tail.length) ∗
    ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 tail.length) ∗ ((a +
      0x40#64) ↦ₛ bytesToBv8 (revWords32 innerSt)) ∗
    ((a + 0x60#64) ↦₆₄ BitVec.ofNat 64 nBlocks) ∗ ((a +
      0x68#64) ↦ₛ bytesToBv8 (revWords32 outerSt)) ∗ ((a + 0x88#64) ↦₆₄ 1#64)
abbrev pqxdhHmacCoreAt (P : Primitives) (a : BitVec 64) (key : Bytes) (msg : List (BitVec 8)) :
    SepProp :=
  pqxdhHmacStateFullAt a (pqxdhHmacInnerInit P key) 1 (pqxdhHmacOuterInit P key) msg
def pqxdhHmacStateAt (P : Primitives) (p : BitVec 64) (prk : Bytes) : SepProp :=
  pqxdhHmacCoreAt P p prk []
def pqxdhHmacCoreBytes (P : Primitives) (key : Bytes) : List (BitVec 8) :=
  bytesToBv8 (revWords32 (pqxdhHmacInnerInit P key)) ++ unpack64 1#64 ++
    bytesToBv8 (revWords32 (pqxdhHmacOuterInit P key)) ++ unpack64 1#64
theorem pqxdhHmacCoreBytes_length (P : Primitives) (key : Bytes) :
    (pqxdhHmacCoreBytes P key).length = 80 := by
  have hi : (bytesToBv8 (revWords32 (pqxdhHmacInnerInit P key))).length = 32 := by
    simp [bytesToBv8, revWords32_length (pqxdhHmacInnerInit_length P key)]
  have ho : (bytesToBv8 (revWords32 (pqxdhHmacOuterInit P key))).length = 32 := by
    simp [bytesToBv8, revWords32_length (pqxdhHmacOuterInit_length P key)]
  simp [pqxdhHmacCoreBytes, hi, ho]
def pqxdhHmacRest (P : Primitives) (p : BitVec 64) (key : Bytes) : SepProp :=
  ((p + 0x3f#64) ↦₈ 0#8) ∗ ((p + 0x40#64) ↦ₛ bytesToBv8 (revWords32 (pqxdhHmacInnerInit P key))) ∗
    ((p + 0x60#64) ↦₆₄ 1#64) ∗
    ((p + 0x68#64) ↦ₛ bytesToBv8 (revWords32 (pqxdhHmacOuterInit P key))) ∗ ((p + 0x88#64) ↦₆₄ 1#64)
theorem pqxdhHmacStateAt_eq_nil (P : Primitives) (p : BitVec 64) (key : Bytes) :
    pqxdhHmacStateAt P p key = (memRegion p 63 ∗ pqxdhHmacRest P p key) := by
  dsimp only [pqxdhHmacStateAt, pqxdhHmacCoreAt, pqxdhHmacStateFullAt, pqxdhHmacRest,
    List.length_nil, Nat.sub_zero, BitVec.ofNat_eq_ofNat]
  rw [eq_true (by decide : 0 < 64), pure_true, emp_sepConj, pointsToBytes_nil, emp_sepConj,
    BitVec.add_zero]
theorem pqxdhHmacRest_bytes (P : Primitives) (p : BitVec 64) (key : Bytes) (junk : List (BitVec 8))
    (hj : junk.length = 63) :
    (p ↦ₛ (junk ++ [0#8] ++ pqxdhHmacCoreBytes P key)) = ((p ↦ₛ junk) ∗ pqxdhHmacRest P p key) := by
  have hi : (bytesToBv8 (revWords32 (pqxdhHmacInnerInit P key))).length = 32 := by
    simp [bytesToBv8, revWords32_length (pqxdhHmacInnerInit_length P key)]
  have ho : (bytesToBv8 (revWords32 (pqxdhHmacOuterInit P key))).length = 32 := by
    simp [bytesToBv8, revWords32_length (pqxdhHmacOuterInit_length P key)]
  simp only [pqxdhHmacRest, pqxdhHmacCoreBytes, List.append_assoc, pointsToBytes_append, hj,
    List.singleton_append, pointsToBytes_cons, hi, ho, unpack64_length, ←
      pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]
theorem pqxdhHmacGood_length (P : Primitives) (key : Bytes) (junk : List (BitVec 8))
    (hj : junk.length = 63) :
    (junk ++ [0#8] ++ pqxdhHmacCoreBytes P key).length = 144 := by
  simp [hj, pqxdhHmacCoreBytes_length]
theorem pqxdhHmacStateAt_entails_cells (P : Primitives) (p : BitVec 64) (prk : Bytes) :
    pqxdhHmacStateAt P p prk ⊢ cells p 8 ∗ memRegion (p + 64#64) 80 := by
  rw [pqxdhHmacStateAt_eq_nil, memRegion_eq_exists_bytes p 63 (by decide)]
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun junk => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hj => ?_
  rw [← pqxdhHmacRest_bytes P p prk junk hj]
  have hlen : (junk ++ [0#8] ++ pqxdhHmacCoreBytes P prk).length = 144 :=
    pqxdhHmacGood_length P prk junk hj
  refine Entails.trans (pointsToBytes_entails_memRegion p _) ?_
  rw [hlen, show (144 : Nat) = 64 + 80 from
    rfl, memRegion_split p 64 80 (by decide), memRegion_cells p 8 (by decide)]
  exact Entails.refl _
structure FrozenRo (img : Obj.Image) (m : Memory) : Prop where
  roData : img.RoDataLoaded m
theorem FrozenRo.of_keepsFrozen {img : Obj.Image} {m m' : Memory}
    (h : FrozenRo img m) (hk : m.KeepsFrozen m') : FrozenRo img m' := by
  refine ⟨fun i hi hro_i => ?_⟩
  obtain ⟨hb, hp, hlf⟩ := h.roData i hi hro_i
  have hf : m.Frozen (img.dataAddr + BitVec.ofNat 64 i) := by
    unfold Memory.Frozen; rw [hp]; rfl
  obtain ⟨hb', hp', hlf', _⟩ := hk _ hf
  exact ⟨hb'.trans hb, hp'.trans hp, hlf'.trans hlf⟩
theorem SepWP.of_sepWP_frozen {prog : Program} {mid target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {img : Obj.Image} (hF : FrozenRo img s.mem)
    (h : SepWP prog (roStop mid) s P
      (fun sm Pm => FrozenRo img sm.mem → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold roStop at h
  with_unfolding_all intro R hm
  refine reaches_pc_seq (reaches_pc_keepsFrozen (h.elim hm)) ?_
  intro sm _ _ ⟨hkf, Pm, hmm, hnext⟩
  exact (hnext (hF.of_keepsFrozen hkf)).elim hmm
theorem SepWP.done_frozen {prog : Program} {mid : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mid)
    (hrun : s.status = .Running)
    (hpost : post s P) :
    SepWP prog (roStop mid) s P post :=
  SepWP.done_ro hpc hrun hpost
theorem SepWP.checkpoint_frozen {prog : Program} {mid mid' target_pc : BitVec 64} {img : Obj.Image}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mid)
    (hrun : s.status = .Running)
    (hnext : FrozenRo img s.mem → SepWP prog (roStop mid') s P
        (fun sm Pm => FrozenRo img sm.mem → SepWP prog target_pc sm Pm post)) :
    SepWP prog (roStop mid) s P
      (fun sm Pm => FrozenRo img sm.mem → SepWP prog target_pc sm Pm post) := by
  refine SepWP.done_frozen hpc hrun fun hF => ?_
  exact SepWP.of_sepWP_frozen hF (hnext hF)
theorem SepWPp.of_sepWP_frozen {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {img : Obj.Image} (hF : FrozenRo img s.mem)
    (h : SepWP prog mid s P (fun sm Pm => FrozenRo img sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := h.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ :=
    hnext (hF.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩
theorem SepWPp.call_keepsFrozen {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗
      R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp =
      s.sp → CalleeSavedPreserved s sf → s.mem.KeepsFrozen sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      first | (intro sf; dsimp only [Spec.inImage]; rfl) | (intro sf; rfl)) :
    SepWPp prog ret s P Q Qp := by
  have hmid : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = spec.post x s sm ∗ F) Qp :=
    ProofLib.SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr hpre hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sm R' _ hoom_post => by
        rw [hoom sm] at hoom_post
        exact (not_satisfies_false_sepConj hoom_post).elim)
  intro R hm hL
  rcases hmid R hm hL with
    ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out⟩
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hsteps.keepsFrozen R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩
theorem SepWPp.call_frame_keepsFrozen {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗
      R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp =
      s.sp → CalleeSavedPreserved s sf → s.mem.KeepsFrozen sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      first | (intro sf; dsimp only [Spec.inImage]; rfl) | (intro sf; rfl)) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_keepsFrozen (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩
def pqxdhHkdfExtractNoneSpec (P : Primitives) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × Bytes × BitVec 64) where
  pre := fun (ret, ikmA, ikm, sp) s =>
    ⌜FrozenRo img s.mem ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = 0#64 ∧
      s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = BitVec.ofNat 64 ikm.length ∧
      s.sp = sp ∧ (ikm.length = 160 ∨ ikm.length = 192 ∨ ikm.length = 224)⌝ ∗ memRegion ret 0xb0 ∗
        (ikmA ↦ₛ bytesToBv8 ikm) ∗
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack ∗
      ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE)
  post := fun (ret, ikmA, ikm, sp) s0 sf =>
    let prk := hkdfExtractRef P none ikm
    ⌜sf.trace = s0.trace⌝ ∗ (ret ↦ₛ bytesToBv8 prk) ∗ pqxdhHmacStateAt P (ret + 0x20#64) prk ∗
      (ikmA ↦ₛ bytesToBv8 ikm) ∗
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack ∗
      ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE)
def pqxdhHkdfExtractSomeSpec (P : Primitives) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64) where
  pre := fun (ret, saltA, salt, ikmA, ikm, sp) s =>
    ⌜FrozenRo img s.mem ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = saltA ∧ s.readReg64 .x2 =
      32#64 ∧ s.readReg64 .x3 = ikmA ∧
      s.readReg64 .x4 = 32#64 ∧ s.sp = sp ∧ saltA ≠ 0#64 ∧ salt.length = 32 ∧ ikm.length = 32⌝ ∗
    memRegion ret 0xb0 ∗ (saltA ↦ₛ bytesToBv8 salt) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack ∗
      ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE)
  post := fun (ret, saltA, salt, ikmA, ikm, sp) s0 sf =>
    let prk := hkdfExtractRef P (some salt) ikm
    ⌜sf.trace = s0.trace⌝ ∗ (ret ↦ₛ bytesToBv8 prk) ∗ pqxdhHmacStateAt P (ret + 0x20#64) prk ∗
    (saltA ↦ₛ bytesToBv8 salt) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗ memRegion (sp - 8192#64) 3936 ∗
      memRegion (sp - 4256#64) 160 ∗
    stackAt sp allocHookStack ∗ ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE)
def PqxdhHkdfExtractOk (P : Primitives) (img : Obj.Image)
    (C : Crypto) (ctl : BitVec 64)
    (absHooks : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
    ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr hkdfExtractSym)
    (pqxdhHkdfExtractNoneSpec P img) ∧ subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
    ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr hkdfExtractSym)
    (pqxdhHkdfExtractSomeSpec P img)
def pqxdhHkdfExpandCellsSpec (P : Primitives) (img : Obj.Image) (k : Nat) :
    Spec (BitVec 64 × Bytes × BitVec 64 × BitVec 64 × Bytes × BitVec 64 × BitVec 64) where
  pre := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s =>
    ⌜FrozenRo img s.mem ∧ s.readReg64 .x0 = hkdfA ∧ s.readReg64 .x1 = infoHdrA ∧
      s.readReg64 .x2 = okmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 (8 * k) ∧ s.sp = sp ∧ prk.length =
        32 ∧
      ((infoA = img.base + bv% (ls_xref% 0x14dac 0x14db0) ∧ info = INFO_RATCHET ∧ k = 8) ∨ (infoA = img.base +
        bv% (ls_str% "WhisperMessageKeys") ∧ info = INFO_MSG_KEYS ∧ k = 10) ∨
       (infoA = img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") ∧ info = INFO_PQXDH ∧ k = 12))⌝ ∗
       pqxdhHmacStateAt P hkdfA prk ∗
    (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ bytesToBv8 info) ∗ cells okmA k ∗
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack
  post := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ cells hkdfA 8 ∗ memRegion (hkdfA + 64#64) 80 ∗
    (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ bytesToBv8 info) ∗
    (okmA ↦ₛ bytesToBv8 (hkdfExpandRef P prk info (8 * k))) ∗ memRegion (sp - 8192#64) 3936 ∗
      memRegion (sp - 4256#64) 160 ∗
    stackAt sp allocHookStack
def PqxdhHkdfExpandMultiInfoOk (P : Primitives) (img : Obj.Image)
    (C : Crypto) (ctl : BitVec 64)
    (absHooks : String → Option (State → State)) : Prop :=
  ∀ k : Nat, subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpec P img k)
theorem bv_sub_sub_lit (x : BitVec 64) (a b : Nat) (_h : a + b < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]
theorem bv_add_neg64 (x : BitVec 64) :
    x + 18446744073709551552#64 = x - 64#64 := by
  rw [BitVec.sub_eq_add_neg]; rfl
theorem bv_sub_add_lit' (x a b : BitVec 64) :
    x - a + b = x - (a - b) := by bv_omega
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
theorem bytesToBv8_encodeU32LE (w : UInt32) :
    bytesToBv8 (encodeU32LE w) = unpack32 w.toBitVec := by
  simp only [bytesToBv8, encodeU32LE, unpack32, List.map]
  have h0 : BitVec.ofNat 8 (UInt8.ofNat (w.toNat % 256)).toNat = w.toBitVec.extractLsb' 0 8 := by
    apply BitVec.eq_of_toNat_eq
    simp [UInt8.ofNat, BitVec.toNat_ofNat]
  have h1 : BitVec.ofNat 8 (UInt8.ofNat ((w.toNat >>> 8) % 256)).toNat =
    w.toBitVec.extractLsb' 8 8 := by
    apply BitVec.eq_of_toNat_eq
    simp [UInt8.ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h2 : BitVec.ofNat 8 (UInt8.ofNat ((w.toNat >>> 16) % 256)).toNat =
    w.toBitVec.extractLsb' 16 8 := by
    apply BitVec.eq_of_toNat_eq
    simp [UInt8.ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h3 : BitVec.ofNat 8 (UInt8.ofNat ((w.toNat >>> 24) % 256)).toNat =
    w.toBitVec.extractLsb' 24 8 := by
    apply BitVec.eq_of_toNat_eq
    simp [UInt8.ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [h0, h1, h2, h3]
theorem pointsToBytes_encodeU32LE (a : BitVec 64) (w : UInt32) :
    (a ↦ₛ bytesToBv8 (encodeU32LE w)) = (a ↦₃₂ w.toBitVec) := by
  rw [bytesToBv8_encodeU32LE, ← pointsTo32_eq_pointsToBytes]
theorem exists_unpack64_of_length_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
            ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a +
            56#64) ↦₆₄ w7)) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : (bs.drop 32).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, fun a => ?_⟩
  have hsplit : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0, hp1]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem exists_unpack64_of_length_80 {bs : List (BitVec 8)} (h : bs.length = 80) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
            ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
            ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9)) := by
  have h0 : (bs.take 64).length = 64 := by simp [h]
  have h1 : (bs.drop 64).length = 16 := by simp [h]
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hp0⟩ := exists_unpack64_of_length_64 h0
  obtain ⟨w8, w9, _, hp1⟩ := exists_unpack64_of_length_16 h1
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, fun a => ?_⟩
  have hsplit : bs = bs.take 64 ++ bs.drop 64 := (List.take_append_drop 64 bs).symm
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0, hp1]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem exists_unpack64_of_length_96 {bs : List (BitVec 8)} (h : bs.length = 96) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
            ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
            ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a +
            80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11)) := by
  have h0 : (bs.take 64).length = 64 := by simp [h]
  have h1 : (bs.drop 64).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hp0⟩ := exists_unpack64_of_length_64 h0
  obtain ⟨w8, w9, w10, w11, _, hp1⟩ := exists_unpack64_of_length_32 h1
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, fun a => ?_⟩
  have hsplit : bs = bs.take 64 ++ bs.drop 64 := (List.take_append_drop 64 bs).symm
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0, hp1]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem exists_unpack64_of_length_144 {bs : List (BitVec 8)} (h : bs.length = 144) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64, ∀ a : BitVec 64,
      (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
            ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
            ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗
            ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗ ((a + 96#64) ↦₆₄ w12) ∗
            ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15) ∗
            ((a + 128#64) ↦₆₄ w16) ∗ ((a + 136#64) ↦₆₄ w17)) := by
  have h0 : (bs.take 64).length = 64 := by simp [h]
  have h1 : (bs.drop 64).length = 80 := by simp [h]
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hp0⟩ := exists_unpack64_of_length_64 h0
  obtain ⟨w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, hp1⟩ := exists_unpack64_of_length_80 h1
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, fun a =>
    ?_⟩
  have hsplit : bs = bs.take 64 ++ bs.drop 64 := (List.take_append_drop 64 bs).symm
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0, hp1]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
def PqxdhHmacGood (P : Primitives) (key : Bytes)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64) : Prop :=
  ∃ junk : List (BitVec 8), junk.length = 63 ∧ ∀ a : BitVec 64, (a ↦ₛ (junk ++ [0#8] ++
    pqxdhHmacCoreBytes P key)) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
          ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗
          ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗ ((a + 96#64) ↦₆₄ w12) ∗
          ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15) ∗ ((a +
          128#64) ↦₆₄ w16) ∗ ((a + 136#64) ↦₆₄ w17))
theorem hmacCore_split (P : Primitives) (p : BitVec 64) (key : Bytes) :
    pqxdhHmacStateAt P p key ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗
        w16 : BitVec 64, ∃∗ w17 : BitVec 64,
        ⌜PqxdhHmacGood P key w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17⌝ ∗
        ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ∗
          ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5) ∗ ((p + 48#64) ↦₆₄ w6) ∗
          ((p + 56#64) ↦₆₄ w7) ∗ ((p + 64#64) ↦₆₄ w8) ∗ ((p + 72#64) ↦₆₄ w9) ∗
          ((p + 80#64) ↦₆₄ w10) ∗ ((p + 88#64) ↦₆₄ w11) ∗ ((p + 96#64) ↦₆₄ w12) ∗
          ((p + 104#64) ↦₆₄ w13) ∗ ((p + 112#64) ↦₆₄ w14) ∗ ((p + 120#64) ↦₆₄ w15) ∗ ((p +
          128#64) ↦₆₄ w16) ∗ ((p + 136#64) ↦₆₄ w17)) := by
  rw [pqxdhHmacStateAt_eq_nil, memRegion_eq_exists_bytes p 63 (by decide)]
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun junk => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hj => ?_
  rw [← pqxdhHmacRest_bytes P p key junk hj]
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, hws⟩ :=
    exists_unpack64_of_length_144 (pqxdhHmacGood_length P key junk hj)
  rw [hws p]
  refine Entails.sepExists_right w0 <| Entails.sepExists_right w1 <|
    Entails.sepExists_right w2 <| Entails.sepExists_right w3 <| Entails.sepExists_right w4 <|
    Entails.sepExists_right w5 <| Entails.sepExists_right w6 <| Entails.sepExists_right w7 <|
    Entails.sepExists_right w8 <| Entails.sepExists_right w9 <| Entails.sepExists_right w10 <|
    Entails.sepExists_right w11 <| Entails.sepExists_right w12 <| Entails.sepExists_right w13 <|
    Entails.sepExists_right w14 <| Entails.sepExists_right w15 <| Entails.sepExists_right w16 <|
    Entails.sepExists_right w17 <| Entails.pure_right ⟨junk, hj, hws⟩ (Entails.refl _)
theorem hmacCore_merge (P : Primitives) (p : BitVec 64) (key : Bytes)
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64}
    (hg : PqxdhHmacGood P key w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) :
    ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ∗
        ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5) ∗ ((p + 48#64) ↦₆₄ w6) ∗
        ((p + 56#64) ↦₆₄ w7) ∗ ((p + 64#64) ↦₆₄ w8) ∗ ((p + 72#64) ↦₆₄ w9) ∗
        ((p + 80#64) ↦₆₄ w10) ∗ ((p + 88#64) ↦₆₄ w11) ∗ ((p + 96#64) ↦₆₄ w12) ∗
        ((p + 104#64) ↦₆₄ w13) ∗ ((p + 112#64) ↦₆₄ w14) ∗ ((p + 120#64) ↦₆₄ w15) ∗ ((p +
        128#64) ↦₆₄ w16) ∗ ((p + 136#64) ↦₆₄ w17)) ⊢
      pqxdhHmacStateAt P p key := by
  obtain ⟨junk, hj, hws⟩ := hg
  rw [← hws p, pqxdhHmacRest_bytes P p key junk hj, pqxdhHmacStateAt_eq_nil]
  refine sepConj_mono_left ?_
  have h := pointsToBytes_entails_memRegion p junk
  rwa [hj] at h
theorem SepWP.replace_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P Q F G : SepProp} {post : State → SepProp → Prop}
    (hG : G = P ∗ F) (hPQ : P ⊢ Q)
    (h : SepWP prog target_pc s (Q ∗ F) post) :
    SepWP prog target_pc s G post := by
  subst hG; exact SepWP.weaken_pre (sepConj_mono_left hPQ) h
@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg)
    :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl
macro "cells_pre_unfold_fast" : tactic =>
  `(tactic| (
    conv => arg 4; simp (config := { maxSteps := 1000000 }) only [
      cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.reduceSub]))
macro "wp_simp_pre_fast " "[" rules:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (conv => arg 4; simp only [$rules,*]))
macro "wp_extract_exists" : tactic =>
  `(tactic| (
    (conv =>
      arg 4
      simp (config := { maxSteps := 1000000 }) only [
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    repeat' (apply SepWP.exists_elim; intro _)
    try (apply SepWP.pure_elim; intro _)))
theorem cells_3_merge (a v0 v1 v2 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ⊢ cells a 3 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.refl _
theorem cells_4_merge (a v0 v1 v2 v3 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢
      cells a 4 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <| Entails.refl _
theorem cells_8_merge (a v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a +
        56#64) ↦₆₄ v7) ⊢ cells a 8 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <| Entails.refl _
theorem cells_10_merge (a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ⊢ cells a 10 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <| Entails.refl _
theorem cells_12_merge (a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗
        ((a + 88#64) ↦₆₄ v11) ⊢ cells a 12 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <|
    Entails.sepExists_right v10 <| Entails.sepExists_right v11 <| Entails.refl _
theorem cells_14_merge (a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗
      ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ∗ ((a + 96#64) ↦₆₄ v12) ∗ ((a +
        104#64) ↦₆₄ v13) ⊢ cells a 14 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <|
    Entails.sepExists_right v10 <| Entails.sepExists_right v11 <|
    Entails.sepExists_right v12 <| Entails.sepExists_right v13 <| Entails.refl _
theorem subroutine_ok_rel_pqxdh {α : Type} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    {spec : Spec α} {callee name : String} {offc off k : Nat}
    (h : subroutine_ok (tripleRatchetProgAt b C ctl absHooks) ((tripleRatchetProgAt b C ctl
      absHooks).fnAddr callee) spec)
    (hc : libsignalSessionCode.fnOff callee = offc) (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = offc) :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks)
      ((tripleRatchetProgAt b C ctl absHooks).fnAddr name + BitVec.ofNat 64 k) spec := by
  have hrel : (tripleRatchetProgAt b C ctl absHooks).fnAddr callee =
      (tripleRatchetProgAt b C ctl absHooks).fnAddr name + BitVec.ofNat 64 k := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hc, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, hk, ← hk, Nat.mod_mod]
  rwa [← hrel]
theorem hkdfExpandRef_96_eq (P : Primitives) (prk info : Bytes) :
    hkdfExpandRef P prk info 96 =
      let t1 := hmacSha256Ref P prk (info ++ [0x01])
      let t2 := hmacSha256Ref P prk (t1 ++ info ++ [0x02])
      let t3 := hmacSha256Ref P prk (t2 ++ info ++ [0x03])
      t1 ++ t2 ++ t3 := by
  unfold hkdfExpandRef
  exact List.take_of_length_le (by simp [hmacSha256Ref_length])
theorem handshakeKeysBytes100_derive_eq (P : Primitives) (hWF : StructuralPrims P)
    (secrets : Bytes) :
    handshakeKeysBytes100 (Model.deriveDRKeys P secrets) =
      let prk := hkdfExtractRef P none secrets
      let t1 := hmacSha256Ref P prk (INFO_PQXDH ++ [0x01])
      let t2 := hmacSha256Ref P prk (t1 ++ INFO_PQXDH ++ [0x02])
      let t3 := hmacSha256Ref P prk (t2 ++ INFO_PQXDH ++ [0x03])
      t1 ++ t3 ++ t2 ++ encodeU32LE 0 := by
  unfold Model.deriveDRKeys handshakeKeysBytes100 DRKey.ck0
  rw [hWF.hkdfDerive96_eq_ref secrets]
  rfl
theorem pointsToBytes_96_3blocks (a : BitVec 64) (t1 t2 t3 : Bytes)
    (h1 : t1.length = 32) (h2 : t2.length = 32) :
    (a ↦ₛ bytesToBv8 (t1 ++ t2 ++ t3)) =
      (a ↦ₛ bytesToBv8 t1) ∗ ((a + 32#64) ↦ₛ bytesToBv8 t2) ∗ ((a + 64#64) ↦ₛ bytesToBv8 t3) := by
  have hb1 : (bytesToBv8 t1).length = 32 := by simp [bytesToBv8, h1]
  have hb2 : (bytesToBv8 t2).length = 32 := by simp [bytesToBv8, h2]
  rw [List.append_assoc, bytesToBv8_append, bytesToBv8_append, pointsToBytes_append,
    pointsToBytes_append, hb1, hb2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem pointsToBytes_100_3blocks_zero (a : BitVec 64) (t1 t3 t2 : Bytes)
    (h1 : t1.length = 32) (h3 : t3.length = 32) (h2 : t2.length = 32) :
    (a ↦ₛ bytesToBv8 (t1 ++ t3 ++ t2 ++ encodeU32LE 0)) =
      (a ↦ₛ bytesToBv8 t1) ∗ ((a + 32#64) ↦ₛ bytesToBv8 t3) ∗ ((a + 64#64) ↦ₛ bytesToBv8 t2) ∗ ((a +
        96#64) ↦₃₂ 0#32) := by
  have hb1 : (bytesToBv8 t1).length = 32 := by simp [bytesToBv8, h1]
  have hb3 : (bytesToBv8 t3).length = 32 := by simp [bytesToBv8, h3]
  have hb2 : (bytesToBv8 t2).length = 32 := by simp [bytesToBv8, h2]
  have hu32_0 : (0 : UInt32).toBitVec = 0#32 := rfl
  rw [List.append_assoc, List.append_assoc, bytesToBv8_append, bytesToBv8_append,
    bytesToBv8_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
    hb1, hb3, hb2, pointsToBytes_encodeU32LE _ 0, hu32_0]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem exists_unpack64_hkdfDerive96 (P : Primitives) (hWF : StructuralPrims P)
    (secrets : Bytes) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64), (∀ a : BitVec 64,
        (a ↦ₛ bytesToBv8 (hkdfExpandRef P (hkdfExtractRef P none secrets) INFO_PQXDH 96)) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
          ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a +
          80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11)) ∧
      (∀ a : BitVec 64, (a ↦ₛ bytesToBv8 (handshakeKeysBytes100 (Model.deriveDRKeys P secrets))) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w8) ∗ ((a + 40#64) ↦₆₄ w9) ∗ ((a + 48#64) ↦₆₄ w10) ∗
          ((a + 56#64) ↦₆₄ w11) ∗ ((a + 64#64) ↦₆₄ w4) ∗ ((a + 72#64) ↦₆₄ w5) ∗
          ((a + 80#64) ↦₆₄ w6) ∗ ((a + 88#64) ↦₆₄ w7) ∗ ((a + 96#64) ↦₃₂ 0#32)) := by
  let prk := hkdfExtractRef P none secrets
  let t1 := hmacSha256Ref P prk (INFO_PQXDH ++ [0x01])
  let t2 := hmacSha256Ref P prk (t1 ++ INFO_PQXDH ++ [0x02])
  let t3 := hmacSha256Ref P prk (t2 ++ INFO_PQXDH ++ [0x03])
  have ht1_len : t1.length = 32 := hmacSha256Ref_length P prk (INFO_PQXDH ++ [0x01])
  have ht2_len : t2.length = 32 := hmacSha256Ref_length P prk (t1 ++ INFO_PQXDH ++ [0x02])
  have ht3_len : t3.length = 32 := hmacSha256Ref_length P prk (t2 ++ INFO_PQXDH ++ [0x03])
  obtain ⟨w0, w1, w2, w3, -, ht1⟩ :=
    exists_unpack64_of_length_32 (by simp [bytesToBv8, ht1_len] : (bytesToBv8 t1).length = 32)
  obtain ⟨w4, w5, w6, w7, -, ht2⟩ :=
    exists_unpack64_of_length_32 (by simp [bytesToBv8, ht2_len] : (bytesToBv8 t2).length = 32)
  obtain ⟨w8, w9, w10, w11, -, ht3⟩ :=
    exists_unpack64_of_length_32 (by simp [bytesToBv8, ht3_len] : (bytesToBv8 t3).length = 32)
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, ?_, ?_⟩
  · intro a
    rw [hkdfExpandRef_96_eq P prk INFO_PQXDH, pointsToBytes_96_3blocks a t1 t2 t3 ht1_len ht2_len,
      ht1 a, ht2 (a + 32#64), ht3 (a + 64#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · intro a
    rw [handshakeKeysBytes100_derive_eq P hWF secrets,
      pointsToBytes_100_3blocks_zero a t1 t3 t2 ht1_len ht3_len ht2_len,
      ht1 a, ht3 (a + 32#64), ht2 (a + 64#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
def incomingBaseKeyInvalidBytes : List (BitVec 8) :=
  bytesToBv8 "incoming base key is invalid".toUTF8.data.toList
theorem incomingBaseKeyInvalidBytes_length :
    incomingBaseKeyInvalidBytes.length = 28 := by decide
theorem rodata_bytes_incomingBaseKeyInvalid :
    (libsignalSessionImage.data.drop (num% (ls_str% "incoming base key is invalid") - num% (ls_xref% 0x2440 0x2444))).take 28 = incomingBaseKeyInvalidBytes :=
      by
  rfl_kernel
theorem rodata_0x7c604 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} (hro : img.RoDataLoaded m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_str% "incoming base key is invalid")) ↦ᵣ incomingBaseKeyInvalidBytes) ∗ P := by
  have hsec : (num% (ls_str% "incoming base key is invalid"), 28) ∈ libsignalSessionImage.roData :=
    List.mem_of_elem_eq_true (by rfl_kernel)
  have ⟨h1, h2⟩ := rodata_readBytes_disjoint himg (dataOff := num% (ls_xref% 0x2440 0x2444)) rfl hsec
    (by decide) (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) m hro
  rw [rodata_bytes_incomingBaseKeyInvalid] at h2
  exact Satisfies.rodata_intro h1 h2 (by decide) hP
def infoPqxdh : Bytes :=
  "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8.data.toList
theorem rodata_bytes_infoPqxdh :
    (libsignalSessionImage.data.drop (num% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") - num% (ls_xref% 0x2440 0x2444))).take 46 = bytesToBv8 infoPqxdh := by
  rfl_kernel
theorem rodata_0x7c267 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} (hro : img.RoDataLoaded m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024")) ↦ᵣ bytesToBv8 infoPqxdh) ∗ P := by
  have hsec : (num% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"), 46) ∈ libsignalSessionImage.roData :=
    List.mem_of_elem_eq_true (by rfl_kernel)
  have ⟨h1, h2⟩ := rodata_readBytes_disjoint himg (dataOff := num% (ls_xref% 0x2440 0x2444)) rfl hsec
    (by decide) (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) m hro
  rw [rodata_bytes_infoPqxdh] at h2
  exact Satisfies.rodata_intro h1 h2 (by decide) hP
theorem rodata_bytes_sha256IV_len :
    ((libsignalSessionImage.data.drop (num% (ls_str% "kyber_pre_key_pu") - num% (ls_xref% 0x2440 0x2444))).take 288).length = 288 := by
  rfl_kernel
theorem rodata_bytes_sha256IV :
    (((libsignalSessionImage.data.drop (num% (ls_str% "kyber_pre_key_pu") - num% (ls_xref% 0x2440 0x2444))).take 288).drop 256).take 32 = sha256IVBytesLE := by
  rfl_kernel
theorem rodata_0x81028 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} (hro : img.RoDataLoaded m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE) ∗ P := by
  have hsec : (num% (ls_str% "kyber_pre_key_pu"), 288) ∈ libsignalSessionImage.roData :=
    List.mem_of_elem_eq_true (by rfl_kernel)
  have ⟨h1, h2⟩ := rodata_readBytes_disjoint himg (dataOff := num% (ls_xref% 0x2440 0x2444)) rfl hsec
    (by decide) (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) m hro
  have hfull : m ⊨ ((img.base + bv% (ls_str% "kyber_pre_key_pu")) ↦ᵣ
      (libsignalSessionImage.data.drop (num% (ls_str% "kyber_pre_key_pu") - num% (ls_xref% 0x2440 0x2444))).take 288) ∗ P :=
    Satisfies.rodata_intro (by rwa [rodata_bytes_sha256IV_len]) (by rwa [rodata_bytes_sha256IV_len])
      (by rw [rodata_bytes_sha256IV_len]; decide) hP
  rw [pointsToBytesRO_split3 _ _ 256 32 (by rw [rodata_bytes_sha256IV_len]),
      rodata_bytes_sha256IV,
      show img.base + bv% (ls_str% "kyber_pre_key_pu") + BitVec.ofNat 64 256 =
        img.base + bv% (ls_str% "kyber_pre_key_pu" + 256) by clear * -; bv_omega,
      sepConj_comm ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE),
      sepConj_assoc] at hfull
  exact Satisfies.of_sep_right hfull
abbrev rodata_0x55604 := @rodata_0x7c604
abbrev rodata_0x55267 := @rodata_0x7c267
abbrev rodata_0x5a028 := @rodata_0x81028
abbrev handshakeKeysDeriveSym : String :=
  "<libsignal_protocol::pqxdh::HandshakeKeys>::derive"
structure HandshakeKeysDeriveGhost where
  secretsPtr : BitVec 64
  secrets    : Bytes
  outPtr     : BitVec 64
def handshakeKeysDeriveSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec HandshakeKeysDeriveGhost :=
  Spec.inImage {
    pre := fun g s =>
      ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.secretsPtr ∧ (s.readReg64 .x1).toNat =
        g.secrets.length ∧
        (g.secrets.length = 160 ∨ g.secrets.length = 192) ∧ g.secrets.take 32 =
        discontinuityBytes⌝ ∗
      (g.secretsPtr ↦ₛ bytesToBv8 g.secrets) ∗ memRegion g.outPtr 100 ∗
        stackAt s.sp pqxdhEntryStack ∗ A.pool
    post := fun g s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗ (g.secretsPtr ↦ₛ bytesToBv8 g.secrets) ∗
      (g.outPtr ↦ₛ bytesToBv8 (handshakeKeysBytes100 (Model.deriveDRKeys P g.secrets))) ∗
        stackAt s0.sp pqxdhEntryStack ∗ A.pool
    onPanic := rustPanicOnOom img
  } img
theorem subroutine_ok_inImage_rodata_lr {α : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {roAddr1 roAddr2 : BitVec 64} {roBytes1 roBytes2 : List (BitVec 8)} {spec :
      Spec α}
    (hro1 : ∀ {m : Memory} (_ : img.RoDataLoaded m) {P : SepProp},
      (m ⊨ P) → (m ⊨ (roAddr1 ↦ᵣ roBytes1) ∗ P))
    (hro2 : ∀ {m : Memory} (_ : img.RoDataLoaded m) {P : SepProp},
      (m ⊨ P) → (m ⊨ (roAddr2 ↦ᵣ roBytes2) ∗ P))
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => ⌜FrozenRo img s.mem⌝ ∗ ((roAddr1 ↦ᵣ roBytes1) ∗ (spec.pre x s ∗
        (roAddr2 ↦ᵣ roBytes2)))
        post := fun x s0 sf =>
        (roAddr1 ↦ᵣ roBytes1) ∗ (spec.post x s0 sf ∗ (roAddr2 ↦ᵣ roBytes2)) }) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hL, hpre⟩
  have hpre2 : s0.mem ⊨ (roAddr2 ↦ᵣ roBytes2) ∗ (spec.pre x s0 ∗ R) := hro2 hL.1.roData hpre
  have hpre2' : s0.mem ⊨ (spec.pre x s0 ∗ (roAddr2 ↦ᵣ roBytes2)) ∗ R := by ac_nf at hpre2 ⊢
  have hpre1 : s0.mem ⊨ ((roAddr1 ↦ᵣ roBytes1) ∗ (spec.pre x s0 ∗ (roAddr2 ↦ᵣ roBytes2))) ∗ R := by
    rw [sepConj_assoc]
    exact hro1 hL.1.roData hpre2'
  have hpre' : s0.mem ⊨ (⌜FrozenRo img s0.mem⌝ ∗ ((roAddr1 ↦ᵣ roBytes1) ∗ (spec.pre x s0 ∗
    (roAddr2 ↦ᵣ roBytes2)))) ∗ R := by
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hL.1.roData⟩, hpre1⟩
  refine h.mono_outcome x R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom_st, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only at hq
    rw [sepConj_assoc] at hq
    have hq1 := Satisfies.of_sep_right hq
    have hq2 : sf.mem ⊨ (roAddr2 ↦ᵣ roBytes2) ∗ (spec.post x s0 sf ∗ R) := by ac_nf at hq1 ⊢
    exact Satisfies.of_sep_right hq2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hq⟩))
theorem subroutine_ok_of_sepWP_rodata2 {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {img : Obj.Image} {roAddr1 roAddr2 : BitVec 64} {roBytes1 roBytes2 : List (BitVec 8)} {spec :
      Spec α}
    (hro1 : ∀ {m : Memory} (_ : img.RoDataLoaded m) {P : SepProp},
      (m ⊨ P) → (m ⊨ (roAddr1 ↦ᵣ roBytes1) ∗ P))
    (hro2 : ∀ {m : Memory} (_ : img.RoDataLoaded m) {P : SepProp},
      (m ⊨ P) → (m ⊨ (roAddr2 ↦ᵣ roBytes2) ∗ P))
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry_pc → s0.status =
      .Running → s0.spAligned = true → FrozenRo img s0.mem →
      SepWP prog (s0.readReg64 Reg.lr) s0
        ((roAddr1 ↦ᵣ roBytes1) ∗ (spec.pre x s0 ∗ (roAddr2 ↦ᵣ roBytes2)))
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ((roAddr1 ↦ᵣ roBytes1) ∗ (spec.post x s0 sf ∗
          (roAddr2 ↦ᵣ roBytes2))) ∗ R) ∧ sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf)) :
    subroutine_ok prog entry_pc (spec.inImage img) := by
  refine subroutine_ok_inImage_rodata_lr hro1 hro2 ?_
  apply subroutine_ok_of_sepWP
  intro x R s0 hpc hrun hpre hsp_align
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hF, hpre⟩
  exact ⟨(roAddr1 ↦ᵣ roBytes1) ∗ (spec.pre x s0 ∗ (roAddr2 ↦ᵣ roBytes2)), R, hpre,
    h x R s0 hpc hrun hsp_align hF⟩
abbrev deriveStack : Nat := 464 + allocHookStack
theorem fnFrame_split_derive_pre (sp : BitVec 64) :
    stackAt sp deriveStack =
      stackAt (sp - 464#64) allocHookStack ∗ cells (sp - 464#64) 12 ∗ cells (sp - 368#64) 18 ∗
        memRegion (sp - 224#64) 176 ∗ cells (sp - 48#64) 6 := by
  simp only [stackAt, deriveStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 4560) (n := 4096) (k := 464)
      (b' := sp - 464#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 464#64) (n := 96) (k := 368) (b' := sp - 368#64) rfl
      (by bv_omega) (by decide), ProofLib.memRegion_split' (b := sp - 368#64) (n := 144) (k :=
        224) (b' := sp - 224#64) rfl
      (by bv_omega) (by decide), ProofLib.memRegion_split' (b := sp - 224#64) (n := 176) (k :=
        48) (b' := sp - 48#64) rfl
      (by bv_omega) (by decide), (memRegion_cells (sp - 464#64) 12 (by decide) :
      memRegion (sp - 464#64) 96 = cells (sp - 464#64) 12), (memRegion_cells (sp - 368#64) 18
        (by decide) :
      memRegion (sp - 368#64) 144 = cells (sp - 368#64) 18), (memRegion_cells (sp -
        48#64) 6 (by decide) :
      memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]
  have hsub : sp - 464#64 - BitVec.ofNat 64 4096 = sp - BitVec.ofNat 64 4560 := by bv_omega
  rw [hsub]
theorem fnFrame_split_derive_post (sp : BitVec 64) :
    stackAt sp deriveStack =
      stackAt (sp - 464#64) allocHookStack ∗ cells (sp - 464#64) 12 ∗ cells (sp - 368#64) 8 ∗
        memRegion (sp - 304#64) 80 ∗ cells (sp - 224#64) 4 ∗ cells (sp - 192#64) 4 ∗ cells (sp -
        160#64) 14 ∗ cells (sp - 48#64) 6 := by
  simp only [stackAt, deriveStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 4560) (n := 4096) (k := 464)
      (b' := sp - 464#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 464#64) (n := 96) (k := 368) (b' := sp - 368#64) rfl
      (by bv_omega) (by decide), ProofLib.memRegion_split' (b := sp - 368#64) (n := 64) (k :=
        304) (b' := sp - 304#64) rfl
      (by bv_omega) (by decide), ProofLib.memRegion_split' (b := sp - 304#64) (n := 80) (k :=
        224) (b' := sp - 224#64) rfl
      (by bv_omega) (by decide), ProofLib.memRegion_split' (b := sp - 224#64) (n := 32) (k :=
        192) (b' := sp - 192#64) rfl
      (by bv_omega) (by decide), ProofLib.memRegion_split' (b := sp - 192#64) (n := 32) (k :=
        160) (b' := sp - 160#64) rfl
      (by bv_omega) (by decide), ProofLib.memRegion_split' (b := sp - 160#64) (n := 112) (k :=
        48) (b' := sp - 48#64) rfl
      (by bv_omega) (by decide), (memRegion_cells (sp - 464#64) 12 (by decide) :
      memRegion (sp - 464#64) 96 = cells (sp - 464#64) 12), (memRegion_cells (sp - 368#64) 8
        (by decide) :
      memRegion (sp - 368#64) 64 = cells (sp - 368#64) 8), (memRegion_cells (sp - 224#64) 4
        (by decide) :
      memRegion (sp - 224#64) 32 = cells (sp - 224#64) 4), (memRegion_cells (sp - 192#64) 4
        (by decide) :
      memRegion (sp - 192#64) 32 = cells (sp - 192#64) 4), (memRegion_cells (sp - 160#64) 14
        (by decide) :
      memRegion (sp - 160#64) 112 = cells (sp - 160#64) 14), (memRegion_cells (sp -
        48#64) 6 (by decide) :
      memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]
  have hsub : sp - 464#64 - BitVec.ofNat 64 4096 = sp - BitVec.ofNat 64 4560 := by bv_omega
  rw [hsub]
theorem stackAt_pqxdh_derive (sp : BitVec 64) :
    stackAt sp pqxdhEntryStack =
      memRegion (sp - 16384#64) 7728 ∗ memRegion (sp - 8656#64) 3936 ∗ memRegion (sp -
        4720#64) 160 ∗ stackAt sp deriveStack := by
  have htop := stackAt_split_top sp 11824 deriveStack (by decide)
  have h0 : (pqxdhEntryStack : Nat) = 11824 + deriveStack := by decide
  have hb0 : BitVec.ofNat 64 (11824 + deriveStack) = 16384#64 := rfl
  rw [hb0] at htop
  have h1 : memRegion (sp - 16384#64) 11824 =
      memRegion (sp - 16384#64) 7728 ∗ memRegion (sp - 8656#64) 4096 :=
    ProofLib.memRegion_split' (b := sp - 16384#64) (n := 7728) (k := 4096)
      (b' := sp - 8656#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 8656#64) 4096 =
      memRegion (sp - 8656#64) 3936 ∗ memRegion (sp - 4720#64) 160 :=
    ProofLib.memRegion_split' (b := sp - 8656#64) (n := 3936) (k := 160)
      (b' := sp - 4720#64) rfl (by bv_omega) (by decide)
  rw [h0, htop, h1, h2]
  ac_rfl
theorem stackAt_pqxdh_derive_pre (sp : BitVec 64) :
    stackAt sp pqxdhEntryStack =
      memRegion (sp - 16384#64) 7728 ∗ memRegion (sp - 8656#64) 3936 ∗ memRegion (sp -
        4720#64) 160 ∗ stackAt (sp - 464#64) allocHookStack ∗
        cells (sp - 464#64) 12 ∗ cells (sp - 368#64) 18 ∗ memRegion (sp - 224#64) 176 ∗ cells (sp -
        48#64) 6 := by
  rw [stackAt_pqxdh_derive sp, fnFrame_split_derive_pre sp]
theorem memRegion_out_derive (out : BitVec 64) :
    memRegion out 100 = cells out 12 ∗ (∃∗ v, (out + 96#64) ↦₃₂ v) := by
  rw [show (100 : Nat) = 96 + 4 from rfl, memRegion_split out 96 4 (by decide),
    (memRegion_cells out 12 (by decide) : memRegion out 96 = cells out 12), memRegion_four (out +
      96#64)]
private theorem derive_adrp1 {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    ((b + 0x1ceb8#64 + 64#64 &&& 0xfffffffffffff000#64) + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024" - 0x1c000)) =
      b + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
  revert hb; bv_bits
private theorem derive_adrp2 {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    ((b + 0x1ceb8#64 + 64#64 &&& 0xfffffffffffff000#64) + bv% (page% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") - 0x1c000) + bv% ((ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") % 4096)) =
      b + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
  revert hb; bv_bits
theorem hmacState_merge_sub368 (P : Primitives) (sp : BitVec 64) (prk : Bytes)
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64}
    (hhmac : PqxdhHmacGood P prk w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) :
    (((sp - 368#64) ↦₆₄ w0) ∗ ((sp - 360#64) ↦₆₄ w1) ∗ ((sp - 352#64) ↦₆₄ w2) ∗
      ((sp - 344#64) ↦₆₄ w3) ∗ ((sp - 336#64) ↦₆₄ w4) ∗ ((sp - 328#64) ↦₆₄ w5) ∗
      ((sp - 320#64) ↦₆₄ w6) ∗ ((sp - 312#64) ↦₆₄ w7) ∗ ((sp - 304#64) ↦₆₄ w8) ∗
      ((sp - 296#64) ↦₆₄ w9) ∗ ((sp - 288#64) ↦₆₄ w10) ∗ ((sp - 280#64) ↦₆₄ w11) ∗
      ((sp - 272#64) ↦₆₄ w12) ∗ ((sp - 264#64) ↦₆₄ w13) ∗ ((sp - 256#64) ↦₆₄ w14) ∗
      ((sp - 248#64) ↦₆₄ w15) ∗ ((sp - 240#64) ↦₆₄ w16) ∗ ((sp - 232#64) ↦₆₄ w17)) ⊢
      pqxdhHmacStateAt P (sp - 368#64) prk := by
  have hmrg := hmacCore_merge P (sp - 368#64) prk hhmac
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hmrg
  exact hmrg
theorem cells_6_merge (a v0 v1 v2 v3 v4 v5 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ⊢ cells a 6 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <| Entails.refl _
theorem cells_sub464_12_merge (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    ((sp - 464#64) ↦₆₄ v0) ∗ ((sp - 456#64) ↦₆₄ v1) ∗ ((sp - 448#64) ↦₆₄ v2) ∗
      ((sp - 440#64) ↦₆₄ v3) ∗ ((sp - 432#64) ↦₆₄ v4) ∗ ((sp - 424#64) ↦₆₄ v5) ∗
      ((sp - 416#64) ↦₆₄ v6) ∗ ((sp - 408#64) ↦₆₄ v7) ∗ ((sp - 400#64) ↦₆₄ v8) ∗
      ((sp - 392#64) ↦₆₄ v9) ∗ ((sp - 384#64) ↦₆₄ v10) ∗ ((sp - 376#64) ↦₆₄ v11) ⊢
      cells (sp - 464#64) 12 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using
    cells_12_merge (sp - 464#64) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
theorem cells_sub368_8_merge (sp v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) :
    ((sp - 368#64) ↦₆₄ v0) ∗ ((sp - 360#64) ↦₆₄ v1) ∗ ((sp - 352#64) ↦₆₄ v2) ∗
      ((sp - 344#64) ↦₆₄ v3) ∗ ((sp - 336#64) ↦₆₄ v4) ∗ ((sp - 328#64) ↦₆₄ v5) ∗
      ((sp - 320#64) ↦₆₄ v6) ∗ ((sp - 312#64) ↦₆₄ v7) ⊢ cells (sp - 368#64) 8 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using
    cells_8_merge (sp - 368#64) v0 v1 v2 v3 v4 v5 v6 v7
theorem cells_sub224_4_merge (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 224#64) ↦₆₄ v0) ∗ ((sp - 216#64) ↦₆₄ v1) ∗ ((sp - 208#64) ↦₆₄ v2) ∗ ((sp -
      200#64) ↦₆₄ v3) ⊢ cells (sp - 224#64) 4 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using
    cells_4_merge (sp - 224#64) v0 v1 v2 v3
theorem cells_sub192_4_merge (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 192#64) ↦₆₄ v0) ∗ ((sp - 184#64) ↦₆₄ v1) ∗ ((sp - 176#64) ↦₆₄ v2) ∗ ((sp -
      168#64) ↦₆₄ v3) ⊢ cells (sp - 192#64) 4 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using
    cells_4_merge (sp - 192#64) v0 v1 v2 v3
theorem cells_sub160_14_merge (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : BitVec 64) :
    ((sp - 160#64) ↦₆₄ v0) ∗ ((sp - 152#64) ↦₆₄ v1) ∗ ((sp - 144#64) ↦₆₄ v2) ∗
      ((sp - 136#64) ↦₆₄ v3) ∗ ((sp - 128#64) ↦₆₄ v4) ∗ ((sp - 120#64) ↦₆₄ v5) ∗
      ((sp - 112#64) ↦₆₄ v6) ∗ ((sp - 104#64) ↦₆₄ v7) ∗ ((sp - 96#64) ↦₆₄ v8) ∗
      ((sp - 88#64) ↦₆₄ v9) ∗ ((sp - 80#64) ↦₆₄ v10) ∗ ((sp - 72#64) ↦₆₄ v11) ∗
      ((sp - 64#64) ↦₆₄ v12) ∗ ((sp - 56#64) ↦₆₄ v13) ⊢ cells (sp - 160#64) 14 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using
    cells_14_merge (sp - 160#64) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
theorem cells_sub48_6_merge (sp v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
      ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5) ⊢
      cells (sp - 48#64) 6 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using
    cells_6_merge (sp - 48#64) v0 v1 v2 v3 v4 v5
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x1ceb8
  CryptoVerification.libsignalSessionCode_fnOff_0x1ad38
  CryptoVerification.libsignalSessionCode_fnOff_0x1a874
set_option maxHeartbeats 6000000 in
theorem handshakeKeysDerive_base_ok {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hext : PqxdhHkdfExtractOk P img C ctl absHooks)
    (hexp : PqxdhHkdfExpandMultiInfoOk P img C ctl absHooks) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr handshakeKeysDeriveSym)
      (handshakeKeysDeriveSpec P A img) := by
  have hb := base_aligned_of_loads himg
  refine subroutine_ok_of_sepWP_rodata2 (rodata_0x7c267 himg) (rodata_0x81028 himg) ?_
  intro x R s0 hpc hrun hsp_align hF0
  have hfn : libsignalSessionCode.fnOff handshakeKeysDeriveSym = 0x1ceb8 :=
    libsignalSessionCode_fnOff_0x1ceb8
  have hext_none := subroutine_ok_rel_pqxdh hext.1 libsignalSessionCode_fnOff_0x1ad38 hfn
    (k := 18446744073709543040) (by decide)
  have hexp' := subroutine_ok_rel_pqxdh (hexp 12) libsignalSessionCode_fnOff_0x1a874 hfn
    (k := 18446744073709541820) (by decide)
  simp only [pqxdhHkdfExpandCellsSpec, cells, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  have hadrp : (((tripleRatchetProgAt img.base C ctl absHooks).fnAddr handshakeKeysDeriveSym +
    64#64 &&&
      0xfffffffffffff000#64) + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024" - 0x1c000)) = img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
    dsimp only [tripleRatchetProgAt]
    rw [Program.fnAddr_rebase, hfn]
    exact derive_adrp1 hb
  have hadrp' : (((tripleRatchetProgAt img.base C ctl absHooks).fnAddr handshakeKeysDeriveSym +
    64#64 &&&
      0xfffffffffffff000#64) + bv% (page% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") - 0x1c000) + bv% ((ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") % 4096)) = img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
    dsimp only [tripleRatchetProgAt]
    rw [Program.fnAddr_rebase, hfn]
    exact derive_adrp2 hb
  code_fetches CryptoVerification.libsignalSessionCode handshakeKeysDerive img.base
    (Rust.withPanics (tripleRatchetExterns C ctl absHooks)) hfn 0x1ceb8 264
  clear himg hext hexp hfn hb
  dsimp only [tripleRatchetProgAt] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl absHooks))).fnAddr handshakeKeysDeriveSym = entry
  examples_hide_fetches
  obtain ⟨secretsPtr, secrets, outPtr⟩ := x
  dsimp only [handshakeKeysDeriveSpec] at *
  rw [sepConj_comm ((img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024")) ↦ᵣ bytesToBv8 infoPqxdh)]
  wp_simp_pre_fast [sepConj_assoc]
  refine SepWP.pure_elim fun ⟨hx8, hx0, hx1_nat, hlen_or, _hdisc⟩ => ?_
  have hx1_bv : s0.readReg64 (.gpr 1#5) = BitVec.ofNat 64 secrets.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_nat, BitVec.toNat_ofNat]
    rcases hlen_or with h160 | h192 <;> omega
  subst hx8 hx0
  have hro_eq : infoPqxdh = INFO_PQXDH := by rfl_kernel
  have hinfo_len : BitVec.ofNat 64 INFO_PQXDH.length = 46#64 := by rfl_kernel
  have hprk_len : (bytesToBv8 (hkdfExtractRef P none secrets)).length = 32 := by
    simp [bytesToBv8, hkdfExtractRef_length]
  have hprk_len32 : (hkdfExtractRef P none secrets).length = 32 :=
    hkdfExtractRef_length P none secrets
  obtain ⟨p0, p1, p2, p3, -, hprk⟩ := exists_unpack64_of_length_32 hprk_len
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm, hout⟩ :=
    exists_unpack64_hkdfDerive96 P hWF secrets
  rw [hro_eq, memRegion_out_derive (s0.readReg64 (.gpr 8#5))]
  rw (occs := .pos [1]) [stackAt_pqxdh_derive_pre s0.sp]
  wp_simp_pre_fast [sepConj_assoc]
  cells_pre_unfold_fast
  wp_extract_exists
  apply SepWP.of_sepWP_frozen hF0
  wp_steps
  apply SepWP.checkpoint_frozen (by wp_norm_lhs) (by wp_norm_lhs); intro hF1;
    try simp only [arm64_norm] at hF1
  wp_simp_pre_fast [hx1_bv]
  wp_call hext_none (s0.sp - 224#64, s0.readReg64 (.gpr 0#5), secrets, s0.sp - 464#64)
  wp_extract_exists
  rw [hprk (s0.sp - 224#64)]
  apply SepWP.replace_pre (by sep_focus) (hmacCore_split P (s0.sp - 192#64) _)
  wp_extract_exists
  rename_i hhmac
  wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_steps
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs); intro hF2; try simp only [arm64_norm]
    at hF2
  apply SepWP.replace_pre (by sep_focus)
    (hmacState_merge_sub368 P s0.sp (hkdfExtractRef P none secrets) hhmac)
  wp_simp_pre_fast [hadrp, hadrp', ← hinfo_len]
  wp_call hexp' (s0.sp - 368#64, hkdfExtractRef P none secrets, s0.sp - 224#64,
    img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"), INFO_PQXDH, s0.sp - 464#64, s0.sp - 464#64)
  wp_extract_exists
  wp_simp_pre_fast [hokm (s0.sp - 464#64), bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_steps
  apply SepWP.replace_pre (by sep_focus) (cells_sub464_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub368_8_merge s0.sp _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub224_4_merge s0.sp _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub192_4_merge s0.sp _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub160_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub48_6_merge s0.sp _ _ _ _ _ _)
  rw [stackAt_pqxdh_derive s0.sp, fnFrame_split_derive_post s0.sp, hout (s0.readReg64 (.gpr 8#5))]
  clear hext_none hexp' hprk hhmac hokm hout hro_eq hinfo_len hx1_bv
  simp only [sepConj_assoc, *]
  wp_done

noncomputable abbrev PP_trap (b : BitVec 64) (C : Crypto)
    (absHooks : String → Option (State → State)) : Program :=
  trTrapProgAt b C absHooks

theorem hookSat_tripleRatchetExterns'_trap {α : Type} (C : Crypto)
    (absHooks : String → Option (State → State)) {sym : String} {spec : Spec α}
    (heq : trTrapExterns C absHooks sym = absHooks sym)
    (h : HookSat absHooks sym spec) :
    HookSat (trTrapExterns C absHooks) sym spec := by
  unfold HookSat at *; rwa [heq]

def PqxdhHkdfExtractOk_trap (P : Primitives) (img : Obj.Image)
    (C : Crypto) (absHooks : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C absHooks)
    ((trTrapProgAt img.base C absHooks).fnAddr hkdfExtractSym)
    (pqxdhHkdfExtractNoneSpec P img) ∧ subroutine_ok (trTrapProgAt img.base C absHooks)
    ((trTrapProgAt img.base C absHooks).fnAddr hkdfExtractSym)
    (pqxdhHkdfExtractSomeSpec P img)

def PqxdhHkdfExpandMultiInfoOk_trap (P : Primitives) (img : Obj.Image)
    (C : Crypto) (absHooks : String → Option (State → State)) : Prop :=
  ∀ k : Nat, subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpec P img k)

theorem subroutine_ok_rel_pqxdh_trap {α : Type} {b : BitVec 64}
    {C : Crypto} {absHooks : String → Option (State → State)}
    {spec : Spec α} {callee name : String} {offc off k : Nat}
    (h : subroutine_ok (trTrapProgAt b C absHooks) ((trTrapProgAt b C
      absHooks).fnAddr callee) spec)
    (hc : libsignalSessionCode.fnOff callee = offc) (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = offc) :
    subroutine_ok (trTrapProgAt b C absHooks)
      ((trTrapProgAt b C absHooks).fnAddr name + BitVec.ofNat 64 k) spec := by
  have hrel : (trTrapProgAt b C absHooks).fnAddr callee =
      (trTrapProgAt b C absHooks).fnAddr name + BitVec.ofNat 64 k := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hc, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, hk, ← hk, Nat.mod_mod]
  rwa [← hrel]

set_option maxHeartbeats 6000000 in
theorem handshakeKeysDerive_base_ok_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hext : PqxdhHkdfExtractOk_trap P img C absHooks)
    (hexp : PqxdhHkdfExpandMultiInfoOk_trap P img C absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr handshakeKeysDeriveSym)
      (handshakeKeysDeriveSpec P A img) := by
  have hb := base_aligned_of_loads himg
  refine subroutine_ok_of_sepWP_rodata2 (rodata_0x7c267 himg) (rodata_0x81028 himg) ?_
  intro x R s0 hpc hrun hsp_align hF0
  have hfn : libsignalSessionCode.fnOff handshakeKeysDeriveSym = 0x1ceb8 :=
    libsignalSessionCode_fnOff_0x1ceb8
  have hext_none := subroutine_ok_rel_pqxdh_trap hext.1 libsignalSessionCode_fnOff_0x1ad38 hfn
    (k := 18446744073709543040) (by decide)
  have hexp' := subroutine_ok_rel_pqxdh_trap (hexp 12) libsignalSessionCode_fnOff_0x1a874 hfn
    (k := 18446744073709541820) (by decide)
  simp only [pqxdhHkdfExpandCellsSpec, cells, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  have hadrp : (((trTrapProgAt img.base C absHooks).fnAddr handshakeKeysDeriveSym +
    64#64 &&&
      0xfffffffffffff000#64) + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024" - 0x1c000)) = img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
    dsimp only [trTrapProgAt]
    rw [Program.fnAddr_rebase, hfn]
    exact derive_adrp1 hb
  have hadrp' : (((trTrapProgAt img.base C absHooks).fnAddr handshakeKeysDeriveSym +
    64#64 &&&
      0xfffffffffffff000#64) + bv% (page% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") - 0x1c000) + bv% ((ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") % 4096)) = img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
    dsimp only [trTrapProgAt]
    rw [Program.fnAddr_rebase, hfn]
    exact derive_adrp2 hb
  code_fetches CryptoVerification.libsignalSessionCode handshakeKeysDerive img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x1ceb8 264
  clear himg hext hexp hfn hb
  dsimp only [trTrapProgAt] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr handshakeKeysDeriveSym = entry
  examples_hide_fetches
  obtain ⟨secretsPtr, secrets, outPtr⟩ := x
  dsimp only [handshakeKeysDeriveSpec] at *
  rw [sepConj_comm ((img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024")) ↦ᵣ bytesToBv8 infoPqxdh)]
  wp_simp_pre_fast [sepConj_assoc]
  refine SepWP.pure_elim fun ⟨hx8, hx0, hx1_nat, hlen_or, _hdisc⟩ => ?_
  have hx1_bv : s0.readReg64 (.gpr 1#5) = BitVec.ofNat 64 secrets.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_nat, BitVec.toNat_ofNat]
    rcases hlen_or with h160 | h192 <;> omega
  subst hx8 hx0
  have hro_eq : infoPqxdh = INFO_PQXDH := by rfl_kernel
  have hinfo_len : BitVec.ofNat 64 INFO_PQXDH.length = 46#64 := by rfl_kernel
  have hprk_len : (bytesToBv8 (hkdfExtractRef P none secrets)).length = 32 := by
    simp [bytesToBv8, hkdfExtractRef_length]
  have hprk_len32 : (hkdfExtractRef P none secrets).length = 32 :=
    hkdfExtractRef_length P none secrets
  obtain ⟨p0, p1, p2, p3, -, hprk⟩ := exists_unpack64_of_length_32 hprk_len
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm, hout⟩ :=
    exists_unpack64_hkdfDerive96 P hWF secrets
  rw [hro_eq, memRegion_out_derive (s0.readReg64 (.gpr 8#5))]
  rw (occs := .pos [1]) [stackAt_pqxdh_derive_pre s0.sp]
  wp_simp_pre_fast [sepConj_assoc]
  cells_pre_unfold_fast
  wp_extract_exists
  apply SepWP.of_sepWP_frozen hF0
  wp_steps
  apply SepWP.checkpoint_frozen (by wp_norm_lhs) (by wp_norm_lhs); intro hF1;
    try simp only [arm64_norm] at hF1
  wp_simp_pre_fast [hx1_bv]
  wp_call hext_none (s0.sp - 224#64, s0.readReg64 (.gpr 0#5), secrets, s0.sp - 464#64)
  wp_extract_exists
  rw [hprk (s0.sp - 224#64)]
  apply SepWP.replace_pre (by sep_focus) (hmacCore_split P (s0.sp - 192#64) _)
  wp_extract_exists
  rename_i hhmac
  wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_steps
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs); intro hF2; try simp only [arm64_norm]
    at hF2
  apply SepWP.replace_pre (by sep_focus)
    (hmacState_merge_sub368 P s0.sp (hkdfExtractRef P none secrets) hhmac)
  wp_simp_pre_fast [hadrp, hadrp', ← hinfo_len]
  wp_call hexp' (s0.sp - 368#64, hkdfExtractRef P none secrets, s0.sp - 224#64,
    img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"), INFO_PQXDH, s0.sp - 464#64, s0.sp - 464#64)
  wp_extract_exists
  wp_simp_pre_fast [hokm (s0.sp - 464#64), bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_steps
  apply SepWP.replace_pre (by sep_focus) (cells_sub464_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub368_8_merge s0.sp _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub224_4_merge s0.sp _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub192_4_merge s0.sp _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub160_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub48_6_merge s0.sp _ _ _ _ _ _)
  rw [stackAt_pqxdh_derive s0.sp, fnFrame_split_derive_post s0.sp, hout (s0.readReg64 (.gpr 8#5))]
  clear hext_none hexp' hprk hhmac hokm hout hro_eq hinfo_len hx1_bv
  simp only [sepConj_assoc, *]
  wp_done

/-! ## `tripleRatchetProgAtExt` Generalized Specs & Proofs -/

abbrev pqxdhHookStackExt : Nat := 16384
abbrev pqxdhEntryStackExt : Nat := 32768
abbrev pqxdhHkdfStackExt : Nat := 24576

def pqxdhHkdfExtractNoneSpecAt (hkdfStk : Nat) (P : Primitives) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × Bytes × BitVec 64) where
  pre := fun (ret, ikmA, ikm, sp) s =>
    ⌜FrozenRo img s.mem ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = 0#64 ∧
      s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = BitVec.ofNat 64 ikm.length ∧
      s.sp = sp ∧ (ikm.length = 160 ∨ ikm.length = 192 ∨ ikm.length = 224)⌝ ∗
    memRegion ret 0xb0 ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗ stackAt sp hkdfStk ∗
      ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE)
  post := fun (ret, ikmA, ikm, sp) s0 sf =>
    let prk := hkdfExtractRef P none ikm
    ⌜sf.trace = s0.trace⌝ ∗ (ret ↦ₛ bytesToBv8 prk) ∗ pqxdhHmacStateAt P (ret + 0x20#64) prk ∗
      (ikmA ↦ₛ bytesToBv8 ikm) ∗ stackAt sp hkdfStk ∗
      ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE)

abbrev pqxdhHkdfExtractNoneSpecExt (P : Primitives) (img : Obj.Image) :=
  pqxdhHkdfExtractNoneSpecAt pqxdhHkdfStackExt P img

def pqxdhHkdfExtractSomeSpecAt (hkdfStk : Nat) (P : Primitives) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64) where
  pre := fun (ret, saltA, salt, ikmA, ikm, sp) s =>
    ⌜FrozenRo img s.mem ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = saltA ∧ s.readReg64 .x2 =
      32#64 ∧ s.readReg64 .x3 = ikmA ∧
      s.readReg64 .x4 = 32#64 ∧ s.sp = sp ∧ saltA ≠ 0#64 ∧ salt.length = 32 ∧ ikm.length = 32⌝ ∗
    memRegion ret 0xb0 ∗ (saltA ↦ₛ bytesToBv8 salt) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
      stackAt sp hkdfStk ∗
      ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE)
  post := fun (ret, saltA, salt, ikmA, ikm, sp) s0 sf =>
    let prk := hkdfExtractRef P (some salt) ikm
    ⌜sf.trace = s0.trace⌝ ∗ (ret ↦ₛ bytesToBv8 prk) ∗ pqxdhHmacStateAt P (ret + 0x20#64) prk ∗
      (saltA ↦ₛ bytesToBv8 salt) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗ stackAt sp hkdfStk ∗
      ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE)

abbrev pqxdhHkdfExtractSomeSpecExt (P : Primitives) (img : Obj.Image) :=
  pqxdhHkdfExtractSomeSpecAt pqxdhHkdfStackExt P img

def PqxdhHkdfExtractOk_at_ext (hkdfStk : Nat) (P : Primitives) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExtractSym)
    (pqxdhHkdfExtractNoneSpecAt hkdfStk P img) ∧
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExtractSym)
    (pqxdhHkdfExtractSomeSpecAt hkdfStk P img)

abbrev PqxdhHkdfExtractOk_ext (P : Primitives) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  PqxdhHkdfExtractOk_at_ext pqxdhHkdfStackExt P img ext

def pqxdhHkdfExpandCellsSpecAt (hkdfStk : Nat) (P : Primitives) (img : Obj.Image) (k : Nat) :
    Spec (BitVec 64 × Bytes × BitVec 64 × BitVec 64 × Bytes × BitVec 64 × BitVec 64) where
  pre := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s =>
    ⌜FrozenRo img s.mem ∧ s.readReg64 .x0 = hkdfA ∧ s.readReg64 .x1 = infoHdrA ∧
      s.readReg64 .x2 = okmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 (8 * k) ∧ s.sp = sp ∧ prk.length =
        32 ∧
      ((infoA = img.base + bv% (ls_xref% 0x14dac 0x14db0) ∧ info = INFO_RATCHET ∧ k = 8) ∨
       (infoA = img.base + bv% (ls_str% "WhisperMessageKeys") ∧ info = INFO_MSG_KEYS ∧ k = 10) ∨
       (infoA = img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") ∧
         info = INFO_PQXDH ∧ k = 12))⌝ ∗
    pqxdhHmacStateAt P hkdfA prk ∗
    (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ bytesToBv8 info) ∗ cells okmA k ∗ stackAt sp hkdfStk
  post := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ cells hkdfA 8 ∗ memRegion (hkdfA + 64#64) 80 ∗
    (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ bytesToBv8 info) ∗
    (okmA ↦ₛ bytesToBv8 (hkdfExpandRef P prk info (8 * k))) ∗ stackAt sp hkdfStk

abbrev pqxdhHkdfExpandCellsSpecExt (P : Primitives) (img : Obj.Image) (k : Nat) :=
  pqxdhHkdfExpandCellsSpecAt pqxdhHkdfStackExt P img k

def PqxdhHkdfExpandMultiInfoOk_at_ext (hkdfStk : Nat) (P : Primitives) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  ∀ k : Nat, subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
    (pqxdhHkdfExpandCellsSpecAt hkdfStk P img k)

abbrev PqxdhHkdfExpandMultiInfoOk_ext (P : Primitives) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  PqxdhHkdfExpandMultiInfoOk_at_ext pqxdhHkdfStackExt P img ext

def handshakeKeysDeriveSpecAt (entryStk : Nat) (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec HandshakeKeysDeriveGhost :=
  Spec.inImage {
    pre := fun g s =>
      ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.secretsPtr ∧ (s.readReg64 .x1).toNat =
        g.secrets.length ∧
        (g.secrets.length = 160 ∨ g.secrets.length = 192) ∧ g.secrets.take 32 =
        discontinuityBytes⌝ ∗
      (g.secretsPtr ↦ₛ bytesToBv8 g.secrets) ∗ memRegion g.outPtr 100 ∗
        stackAt s.sp entryStk ∗ A.pool
    post := fun g s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗ (g.secretsPtr ↦ₛ bytesToBv8 g.secrets) ∗
      (g.outPtr ↦ₛ bytesToBv8 (handshakeKeysBytes100 (Model.deriveDRKeys P g.secrets))) ∗
        stackAt s0.sp entryStk ∗ A.pool
    onPanic := rustPanicOnOom img
  } img

abbrev handshakeKeysDeriveSpecExt (P : Primitives) (A : RustAlloc) (img : Obj.Image) :=
  handshakeKeysDeriveSpecAt pqxdhEntryStackExt P A img

theorem subroutine_ok_rel_pqxdh_ext {α : Type} {b : BitVec 64}
    {ext : String → Option (State → State)}
    {spec : Spec α} {callee name : String} {offc off k : Nat}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr callee) spec)
    (hc : libsignalSessionCode.fnOff callee = offc)
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = offc) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) spec := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr callee =
      (tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hc, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, hk, ← hk, Nat.mod_mod]
  rwa [← hrel]

private theorem stackAt_split_derive_464 (sp : BitVec 64) {hkdfStk : Nat}
    (h : hkdfStk + 464 ≤ 2 ^ 64) :
    stackAt sp (hkdfStk + 464) =
      stackAt (sp - 464#64) hkdfStk ∗ memRegion (sp - 464#64) 464 := by
  simp only [stackAt]
  have hsub : sp - BitVec.ofNat 64 (hkdfStk + 464) =
      sp - 464#64 - BitVec.ofNat 64 hkdfStk := by
    rw [BitVec.ofNat_add, BitVec.add_comm, ← BitVec.sub_sub]
  have hadd : sp - 464#64 - BitVec.ofNat 64 hkdfStk + BitVec.ofNat 64 hkdfStk =
      sp - 464#64 := BitVec.sub_add_cancel _ _
  rw [hsub, memRegion_split _ hkdfStk 464 h, hadd]

private theorem memRegion_464_derive_pre (sp : BitVec 64) :
    memRegion (sp - 464#64) 464 =
      cells (sp - 464#64) 12 ∗ cells (sp - 368#64) 18 ∗
        memRegion (sp - 224#64) 176 ∗ cells (sp - 48#64) 6 := by
  rw [ProofLib.memRegion_split' (b := sp - 464#64) (n := 96) (k := 368) (b' := sp - 368#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 368#64) (n := 144) (k := 224) (b' := sp - 224#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 224#64) (n := 176) (k := 48) (b' := sp - 48#64) rfl
      (by bv_omega) (by decide),
    (memRegion_cells (sp - 464#64) 12 (by decide) :
      memRegion (sp - 464#64) 96 = cells (sp - 464#64) 12),
    (memRegion_cells (sp - 368#64) 18 (by decide) :
      memRegion (sp - 368#64) 144 = cells (sp - 368#64) 18),
    (memRegion_cells (sp - 48#64) 6 (by decide) :
      memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]

private theorem memRegion_464_derive_post (sp : BitVec 64) :
    memRegion (sp - 464#64) 464 =
      cells (sp - 464#64) 12 ∗ cells (sp - 368#64) 8 ∗
        memRegion (sp - 304#64) 80 ∗ cells (sp - 224#64) 4 ∗ cells (sp - 192#64) 4 ∗
        cells (sp - 160#64) 14 ∗ cells (sp - 48#64) 6 := by
  rw [ProofLib.memRegion_split' (b := sp - 464#64) (n := 96) (k := 368) (b' := sp - 368#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 368#64) (n := 64) (k := 304) (b' := sp - 304#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 304#64) (n := 80) (k := 224) (b' := sp - 224#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 224#64) (n := 32) (k := 192) (b' := sp - 192#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 192#64) (n := 32) (k := 160) (b' := sp - 160#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 160#64) (n := 112) (k := 48) (b' := sp - 48#64) rfl
      (by bv_omega) (by decide),
    (memRegion_cells (sp - 464#64) 12 (by decide) :
      memRegion (sp - 464#64) 96 = cells (sp - 464#64) 12),
    (memRegion_cells (sp - 368#64) 8 (by decide) :
      memRegion (sp - 368#64) 64 = cells (sp - 368#64) 8),
    (memRegion_cells (sp - 224#64) 4 (by decide) :
      memRegion (sp - 224#64) 32 = cells (sp - 224#64) 4),
    (memRegion_cells (sp - 192#64) 4 (by decide) :
      memRegion (sp - 192#64) 32 = cells (sp - 192#64) 4),
    (memRegion_cells (sp - 160#64) 14 (by decide) :
      memRegion (sp - 160#64) 112 = cells (sp - 160#64) 14),
    (memRegion_cells (sp - 48#64) 6 (by decide) :
      memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]

theorem pqxdhHkdfExtractNone_mono_stack {prog : Program} {entry : BitVec 64}
    {P : Primitives} {img : Obj.Image} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (pqxdhHkdfExtractNoneSpecAt s1 P img)) :
    subroutine_ok prog entry (pqxdhHkdfExtractNoneSpecAt s2 P img) := by
  refine subroutine_ok_outcome_intro fun ⟨ret, ikmA, ikm, sp⟩ R s0 hpc hrun hpre hsp => ?_
  have hsplit : stackAt sp s2 = memRegion (sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt sp s1 := by
    have heq : s2 - s1 + s1 = s2 := Nat.sub_add_cancel hle
    simpa [heq] using stackAt_split_top sp (s2 - s1) s1 (by omega)
  dsimp only [pqxdhHkdfExtractNoneSpecAt] at hpre
  rw [hsplit] at hpre
  have hpre' : s0.mem ⊨ (pqxdhHkdfExtractNoneSpecAt s1 P img).pre (ret, ikmA, ikm, sp) s0 ∗
      (memRegion (sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) := by
    dsimp only [pqxdhHkdfExtractNoneSpecAt]
    ac_nf at hpre ⊢
  refine h.mono_outcome (ret, ikmA, ikm, sp) (memRegion (sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
      s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [pqxdhHkdfExtractNoneSpecAt] at hq ⊢
    rw [hsplit]
    ac_nf at hq ⊢
  · refine Or.inr ?_
    rcases hrest with ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩ <;>
      simp [pqxdhHkdfExtractNoneSpecAt] at hq

theorem pqxdhHkdfExtractSome_mono_stack {prog : Program} {entry : BitVec 64}
    {P : Primitives} {img : Obj.Image} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (pqxdhHkdfExtractSomeSpecAt s1 P img)) :
    subroutine_ok prog entry (pqxdhHkdfExtractSomeSpecAt s2 P img) := by
  refine subroutine_ok_outcome_intro fun ⟨ret, saltA, salt, ikmA, ikm, sp⟩ R s0 hpc hrun hpre hsp => ?_
  have hsplit : stackAt sp s2 = memRegion (sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt sp s1 := by
    have heq : s2 - s1 + s1 = s2 := Nat.sub_add_cancel hle
    simpa [heq] using stackAt_split_top sp (s2 - s1) s1 (by omega)
  dsimp only [pqxdhHkdfExtractSomeSpecAt] at hpre
  rw [hsplit] at hpre
  have hpre' : s0.mem ⊨ (pqxdhHkdfExtractSomeSpecAt s1 P img).pre (ret, saltA, salt, ikmA, ikm, sp) s0 ∗
      (memRegion (sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) := by
    dsimp only [pqxdhHkdfExtractSomeSpecAt]
    ac_nf at hpre ⊢
  refine h.mono_outcome (ret, saltA, salt, ikmA, ikm, sp) (memRegion (sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
      s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [pqxdhHkdfExtractSomeSpecAt] at hq ⊢
    rw [hsplit]
    ac_nf at hq ⊢
  · refine Or.inr ?_
    rcases hrest with ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩ <;>
      simp [pqxdhHkdfExtractSomeSpecAt] at hq

theorem pqxdhHkdfExpandCells_mono_stack {prog : Program} {entry : BitVec 64}
    {P : Primitives} {img : Obj.Image} {k s1 s2 : Nat}
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (pqxdhHkdfExpandCellsSpecAt s1 P img k)) :
    subroutine_ok prog entry (pqxdhHkdfExpandCellsSpecAt s2 P img k) := by
  refine subroutine_ok_outcome_intro fun ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpc hrun hpre hsp => ?_
  have hsplit : stackAt sp s2 = memRegion (sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt sp s1 := by
    have heq : s2 - s1 + s1 = s2 := Nat.sub_add_cancel hle
    simpa [heq] using stackAt_split_top sp (s2 - s1) s1 (by omega)
  dsimp only [pqxdhHkdfExpandCellsSpecAt] at hpre
  rw [hsplit] at hpre
  have hpre' : s0.mem ⊨
      (pqxdhHkdfExpandCellsSpecAt s1 P img k).pre (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s0 ∗
      (memRegion (sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) := by
    dsimp only [pqxdhHkdfExpandCellsSpecAt]
    ac_nf at hpre ⊢
  refine h.mono_outcome (hkdfA, prk, infoHdrA, infoA, info, okmA, sp)
      (memRegion (sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
      s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [pqxdhHkdfExpandCellsSpecAt] at hq ⊢
    rw [hsplit]
    ac_nf at hq ⊢
  · refine Or.inr ?_
    rcases hrest with ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩ <;>
      simp [pqxdhHkdfExpandCellsSpecAt] at hq

theorem handshakeKeysDerive_mono_stack {prog : Program} {entry : BitVec 64}
    {P : Primitives} {A : RustAlloc} {img : Obj.Image} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (handshakeKeysDeriveSpecAt s1 P A img)) :
    subroutine_ok prog entry (handshakeKeysDeriveSpecAt s2 P A img) := by
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp => ?_
  have hsplit : ∀ sp, stackAt sp s2 =
      memRegion (sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt sp s1 := fun sp => by
    have heq : s2 - s1 + s1 = s2 := Nat.sub_add_cancel hle
    simpa [heq] using stackAt_split_top sp (s2 - s1) s1 (by omega)
  dsimp only [handshakeKeysDeriveSpecAt, Spec.inImage] at hpre
  rw [hsplit s0.sp] at hpre
  have hpre' : s0.mem ⊨ (handshakeKeysDeriveSpecAt s1 P A img).pre g s0 ∗
      (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) := by
    dsimp only [handshakeKeysDeriveSpecAt, Spec.inImage]
    ac_nf at hpre ⊢
  refine h.mono_outcome g (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
      s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨c, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [handshakeKeysDeriveSpecAt, Spec.inImage] at hq ⊢
    rw [hsplit s0.sp]
    ac_nf at hq ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [handshakeKeysDeriveSpecAt, Spec.inImage, rustPanicOnOom] at hq ⊢
    exact allowPanic_frame id (by simpa only [sepConj_assoc] using hq)
  · simp [handshakeKeysDeriveSpecAt, Spec.inImage] at hq
  · simp [handshakeKeysDeriveSpecAt, Spec.inImage] at hq

set_option maxHeartbeats 6000000 in
theorem handshakeKeysDerive_base_ok_min_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {hkdfStk : Nat}
    (hstk : hkdfStk + 464 ≤ 2 ^ 64)
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hext : PqxdhHkdfExtractOk_at_ext hkdfStk P img ext)
    (hexp : PqxdhHkdfExpandMultiInfoOk_at_ext hkdfStk P img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr handshakeKeysDeriveSym)
      (handshakeKeysDeriveSpecAt (hkdfStk + 464) P A img) := by
  have hb := base_aligned_of_loads himg
  refine subroutine_ok_of_sepWP_rodata2 (rodata_0x7c267 himg) (rodata_0x81028 himg) ?_
  intro x R s0 hpc hrun hsp_align hF0
  have hfn : libsignalSessionCode.fnOff handshakeKeysDeriveSym = 0x1ceb8 :=
    libsignalSessionCode_fnOff_0x1ceb8
  have hext_none := subroutine_ok_rel_pqxdh_ext hext.1 libsignalSessionCode_fnOff_0x1ad38 hfn
    (k := 18446744073709543040) (by decide)
  have hexp' := subroutine_ok_rel_pqxdh_ext (hexp 12) libsignalSessionCode_fnOff_0x1a874 hfn
    (k := 18446744073709541820) (by decide)
  simp only [pqxdhHkdfExpandCellsSpecAt, cells, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  have hadrp : (((tripleRatchetProgAtExt img.base ext).fnAddr handshakeKeysDeriveSym +
    64#64 &&&
      0xfffffffffffff000#64) + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024" - 0x1c000)) = img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
    dsimp only [tripleRatchetProgAtExt]
    rw [Program.fnAddr_rebase, hfn]
    exact derive_adrp1 hb
  have hadrp' : (((tripleRatchetProgAtExt img.base ext).fnAddr handshakeKeysDeriveSym +
    64#64 &&&
      0xfffffffffffff000#64) + bv% (page% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") - 0x1c000) + bv% ((ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") % 4096)) = img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
    dsimp only [tripleRatchetProgAtExt]
    rw [Program.fnAddr_rebase, hfn]
    exact derive_adrp2 hb
  code_fetches CryptoVerification.libsignalSessionCode handshakeKeysDerive img.base
    (Rust.withPanics ext) hfn 0x1ceb8 264
  clear himg hext hexp hfn hb
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr handshakeKeysDeriveSym = entry
  examples_hide_fetches
  obtain ⟨secretsPtr, secrets, outPtr⟩ := x
  dsimp only [handshakeKeysDeriveSpecAt] at *
  rw [sepConj_comm ((img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024")) ↦ᵣ bytesToBv8 infoPqxdh)]
  wp_simp_pre_fast [sepConj_assoc]
  refine SepWP.pure_elim fun ⟨hx8, hx0, hx1_nat, hlen_or, _hdisc⟩ => ?_
  have hx1_bv : s0.readReg64 (.gpr 1#5) = BitVec.ofNat 64 secrets.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_nat, BitVec.toNat_ofNat]
    rcases hlen_or with h160 | h192 <;> omega
  subst hx8 hx0
  have hro_eq : infoPqxdh = INFO_PQXDH := by rfl_kernel
  have hinfo_len : BitVec.ofNat 64 INFO_PQXDH.length = 46#64 := by rfl_kernel
  have hprk_len : (bytesToBv8 (hkdfExtractRef P none secrets)).length = 32 := by
    simp [bytesToBv8, hkdfExtractRef_length]
  have hprk_len32 : (hkdfExtractRef P none secrets).length = 32 :=
    hkdfExtractRef_length P none secrets
  obtain ⟨p0, p1, p2, p3, -, hprk⟩ := exists_unpack64_of_length_32 hprk_len
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm, hout⟩ :=
    exists_unpack64_hkdfDerive96 P hWF secrets
  rw [hro_eq, memRegion_out_derive (s0.readReg64 (.gpr 8#5))]
  rw (occs := .pos [1]) [stackAt_split_derive_464 s0.sp hstk, memRegion_464_derive_pre s0.sp]
  wp_simp_pre_fast [sepConj_assoc]
  cells_pre_unfold_fast
  wp_extract_exists
  apply SepWP.of_sepWP_frozen hF0
  wp_steps
  apply SepWP.checkpoint_frozen (by wp_norm_lhs) (by wp_norm_lhs); intro hF1;
    try simp only [arm64_norm] at hF1
  wp_simp_pre_fast [hx1_bv]
  wp_call hext_none (s0.sp - 224#64, s0.readReg64 (.gpr 0#5), secrets, s0.sp - 464#64)
  wp_extract_exists
  rw [hprk (s0.sp - 224#64)]
  apply SepWP.replace_pre (by sep_focus) (hmacCore_split P (s0.sp - 192#64) _)
  wp_extract_exists
  rename_i hhmac
  wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_steps
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs); intro hF2; try simp only [arm64_norm]
    at hF2
  apply SepWP.replace_pre (by sep_focus)
    (hmacState_merge_sub368 P s0.sp (hkdfExtractRef P none secrets) hhmac)
  wp_simp_pre_fast [hadrp, hadrp', ← hinfo_len]
  wp_call hexp' (s0.sp - 368#64, hkdfExtractRef P none secrets, s0.sp - 224#64,
    img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"), INFO_PQXDH, s0.sp - 464#64, s0.sp - 464#64)
  wp_extract_exists
  wp_simp_pre_fast [hokm (s0.sp - 464#64), bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_steps
  apply SepWP.replace_pre (by sep_focus) (cells_sub464_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub368_8_merge s0.sp _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub224_4_merge s0.sp _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub192_4_merge s0.sp _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub160_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub48_6_merge s0.sp _ _ _ _ _ _)
  rw [stackAt_split_derive_464 s0.sp hstk, memRegion_464_derive_post s0.sp,
    hout (s0.readReg64 (.gpr 8#5))]
  clear hext_none hexp' hprk hhmac hokm hout hro_eq hinfo_len hx1_bv
  simp only [sepConj_assoc, *]
  wp_done

theorem handshakeKeysDerive_base_ok_at_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {hkdfStk entryStk : Nat}
    (hle : hkdfStk + 464 ≤ entryStk) (hmax : entryStk ≤ 2 ^ 64)
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hext : PqxdhHkdfExtractOk_at_ext hkdfStk P img ext)
    (hexp : PqxdhHkdfExpandMultiInfoOk_at_ext hkdfStk P img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr handshakeKeysDeriveSym)
      (handshakeKeysDeriveSpecAt entryStk P A img) :=
  handshakeKeysDerive_mono_stack hle hmax
    (handshakeKeysDerive_base_ok_min_ext (Nat.le_trans hle hmax) himg hWF hext hexp)

theorem handshakeKeysDerive_base_ok_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hext : PqxdhHkdfExtractOk_ext P img ext)
    (hexp : PqxdhHkdfExpandMultiInfoOk_ext P img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr handshakeKeysDeriveSym)
      (handshakeKeysDeriveSpecExt P A img) :=
  handshakeKeysDerive_base_ok_at_ext (by decide) (by decide) himg hWF hext hexp

/-! ## Relocatable `[LibsignalPlacement]` Contract for `<HandshakeKeys>::derive` (Block `59`) -/

def pqxdhHkdfExtractNonePlacedSpec (P : Primitives) (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × Bytes × BitVec 64) where
  pre := fun (ret, ikmA, ikm, sp) s =>
    ⌜Keys.LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = 0#64 ∧
      s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = BitVec.ofNat 64 ikm.length ∧
      s.sp = sp ∧ (ikm.length = 160 ∨ ikm.length = 192 ∨ ikm.length = 224)⌝ ∗
    memRegion ret 0xb0 ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack
  post := fun (ret, ikmA, ikm, sp) s0 sf =>
    let prk := hkdfExtractRef P none ikm
    ⌜sf.trace = s0.trace⌝ ∗ (ret ↦ₛ bytesToBv8 prk) ∗ pqxdhHmacStateAt P (ret + 0x20#64) prk ∗
    (ikmA ↦ₛ bytesToBv8 ikm) ∗
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack

def pqxdhHkdfExtractSomePlacedSpec (P : Primitives) (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64) where
  pre := fun (ret, saltA, salt, ikmA, ikm, sp) s =>
    ⌜Keys.LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = saltA ∧ s.readReg64 .x2 =
      32#64 ∧ s.readReg64 .x3 = ikmA ∧
      s.readReg64 .x4 = 32#64 ∧ s.sp = sp ∧ saltA ≠ 0#64 ∧ salt.length = 32 ∧ ikm.length = 32⌝ ∗
    memRegion ret 0xb0 ∗ (saltA ↦ₛ bytesToBv8 salt) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack
  post := fun (ret, saltA, salt, ikmA, ikm, sp) s0 sf =>
    let prk := hkdfExtractRef P (some salt) ikm
    ⌜sf.trace = s0.trace⌝ ∗ (ret ↦ₛ bytesToBv8 prk) ∗ pqxdhHmacStateAt P (ret + 0x20#64) prk ∗
    (saltA ↦ₛ bytesToBv8 salt) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗ memRegion (sp - 8192#64) 3936 ∗
    memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack

def PqxdhHkdfExtractPlacedOk [LibsignalPlacement] (P : Primitives) (prog : Program) : Prop :=
  subroutine_ok prog (lsmpl.base 54)
    (pqxdhHkdfExtractNonePlacedSpec P lsmpl) ∧
  subroutine_ok prog (lsmpl.base 54)
    (pqxdhHkdfExtractSomePlacedSpec P lsmpl)

def pqxdhHkdfExpandCellsPlacedSpec (P : Primitives) (pl : Obj.MultiPlacement) (k : Nat) :
    Spec (BitVec 64 × Bytes × BitVec 64 × BitVec 64 × Bytes × BitVec 64 × BitVec 64) where
  pre := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s =>
    ⌜Keys.LsFrozenInv pl s ∧ s.readReg64 .x0 = hkdfA ∧ s.readReg64 .x1 = infoHdrA ∧
      s.readReg64 .x2 = okmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 (8 * k) ∧ s.sp = sp ∧
      prk.length = 32 ∧
      ((infoA = pl.ρ "libsignal_protocol:.rodata..Lanon.173" ∧ info = INFO_RATCHET ∧ k = 8) ∨
       (infoA = pl.ρ "libsignal_protocol:.rodata..Lanon.184" ∧ info = INFO_MSG_KEYS ∧ k = 10) ∨
       (infoA = pl.ρ "libsignal_protocol:.rodata..Lanon.352" ∧ info = INFO_PQXDH ∧ k = 12))⌝ ∗
    pqxdhHmacStateAt P hkdfA prk ∗
    (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
    (infoA ↦ᵣ bytesToBv8 info) ∗ cells okmA k ∗
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack
  post := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ cells hkdfA 8 ∗ memRegion (hkdfA + 64#64) 80 ∗
    (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
    (infoA ↦ᵣ bytesToBv8 info) ∗
    (okmA ↦ₛ bytesToBv8 (hkdfExpandRef P prk info (8 * k))) ∗ memRegion (sp - 8192#64) 3936 ∗
    memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack

def PqxdhHkdfExpandMultiInfoPlacedOk [LibsignalPlacement] (P : Primitives) (prog : Program) :
    Prop :=
  ∀ k : Nat, subroutine_ok prog (lsmpl.base 53)
    (pqxdhHkdfExpandCellsPlacedSpec P lsmpl k)

def handshakeKeysDerivePlacedBaseSpec (P : Primitives) (A : RustAlloc) :
    Spec HandshakeKeysDeriveGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.secretsPtr ∧
      (s.readReg64 .x1).toNat = g.secrets.length ∧
      (g.secrets.length = 160 ∨ g.secrets.length = 192) ∧
      g.secrets.take 32 = discontinuityBytes⌝ ∗
    (g.secretsPtr ↦ₛ bytesToBv8 g.secrets) ∗ memRegion g.outPtr 100 ∗
    stackAt s.sp pqxdhEntryStack ∗ A.pool
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (g.secretsPtr ↦ₛ bytesToBv8 g.secrets) ∗
    (g.outPtr ↦ₛ bytesToBv8 (handshakeKeysBytes100 (Model.deriveDRKeys P g.secrets))) ∗
    stackAt s0.sp pqxdhEntryStack ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem SepWP.checkpoint_lscro {prog : Program} {mid mid' target_pc : BitVec 64}
    {pl : Obj.MultiPlacement} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hnext : Keys.LsFrozenInv pl s → SepWP prog (Keys.frozenStop mid') s P
        (fun sm Pm => Keys.LsFrozenInv pl sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog (Keys.frozenStop mid) s P
      (fun sm Pm => Keys.LsFrozenInv pl sm → SepWP prog target_pc sm Pm post) := by
  refine Keys.SepWP.done_frozen hpc hrun fun hF => ?_
  exact Keys.SepWP.of_sepWP_lscro hF (hnext hF)

set_option maxHeartbeats 6000000 in
theorem handshakeKeysDerive_placed_ok [LibsignalPlacement] {P : Primitives} {A : RustAlloc}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hext : PqxdhHkdfExtractPlacedOk P ((blkPC_59).rebase (blkPl_59).base H))
    (hexp : PqxdhHkdfExpandMultiInfoPlacedOk P ((blkPC_59).rebase (blkPl_59).base H)) :
    subroutine_ok ((blkPC_59).rebase (blkPl_59).base H) (blkPl_59).base
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec P A)) := by
  refine Keys.subroutine_ok_withLsCodeRoLoaded_rodata''
    (roSym := "libsignal_protocol:.rodata..Lanon.352")
    (roBytes := bytesToBv8 infoPqxdh) (by decide) ?_
  have hext_none := hext.1
  have hexp' := hexp 12
  simp only [pqxdhHkdfExpandCellsPlacedSpec, cells, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  clear hext hexp
  wp_init x s0
  obtain ⟨secretsPtr, secrets, outPtr⟩ := x
  dsimp only [handshakeKeysDerivePlacedBaseSpec] at *
  have hF0 : Keys.LsFrozenInv lsmpl s0 := ‹_›
  have hx1_bv : s0.readReg64 (.gpr 1#5) = BitVec.ofNat 64 secrets.length := by
    apply BitVec.eq_of_toNat_eq
    rw [‹(s0.readReg64 (.gpr 1#5)).toNat = secrets.length›, BitVec.toNat_ofNat]
    rcases ‹secrets.length = 160 ∨ secrets.length = 192› with h160 | h192 <;> omega
  subst outPtr secretsPtr
  have hro_eq : infoPqxdh = INFO_PQXDH := by rfl_kernel
  have hinfo_len : BitVec.ofNat 64 INFO_PQXDH.length = 46#64 := by rfl_kernel
  have hprk_len : (bytesToBv8 (hkdfExtractRef P none secrets)).length = 32 := by
    simp [bytesToBv8, hkdfExtractRef_length]
  have hprk_len32 : (hkdfExtractRef P none secrets).length = 32 :=
    hkdfExtractRef_length P none secrets
  obtain ⟨p0, p1, p2, p3, -, hprk⟩ := exists_unpack64_of_length_32 hprk_len
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm, hout⟩ :=
    exists_unpack64_hkdfDerive96 P hWF secrets
  rw [hro_eq, memRegion_out_derive (s0.readReg64 (.gpr 8#5))]
  rw (occs := .pos [1]) [stackAt_pqxdh_derive_pre s0.sp]
  wp_simp_pre_fast [sepConj_assoc]
  cells_pre_unfold_fast
  wp_extract_exists
  apply Keys.SepWP.of_sepWP_lscro hF0
  wp_steps
  apply SepWP.checkpoint_lscro (by wp_norm_lhs) (by wp_norm_lhs); intro hF1
  try simp only [arm64_norm] at hF1
  wp_simp_pre_fast [hx1_bv]
  wp_call hext_none (s0.sp - 224#64, s0.readReg64 (.gpr 0#5), secrets, s0.sp - 464#64)
  wp_extract_exists
  rw [hprk (s0.sp - 224#64)]
  apply SepWP.replace_pre (by sep_focus) (hmacCore_split P (s0.sp - 192#64) _)
  wp_extract_exists
  rename_i hhmac
  wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_steps
  apply Keys.SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs); intro hF2
  try simp only [arm64_norm] at hF2
  apply SepWP.replace_pre (by sep_focus)
    (hmacState_merge_sub368 P s0.sp (hkdfExtractRef P none secrets) hhmac)
  wp_simp_pre_fast [← hinfo_len]
  wp_call hexp' (s0.sp - 368#64, hkdfExtractRef P none secrets, s0.sp - 224#64,
    lsmpl.ρ "libsignal_protocol:.rodata..Lanon.352", INFO_PQXDH, s0.sp - 464#64, s0.sp - 464#64)
  wp_extract_exists
  wp_simp_pre_fast [hokm (s0.sp - 464#64), bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_steps
  apply SepWP.replace_pre (by sep_focus) (cells_sub464_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub368_8_merge s0.sp _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub224_4_merge s0.sp _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub192_4_merge s0.sp _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub160_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub48_6_merge s0.sp _ _ _ _ _ _)
  rw [stackAt_pqxdh_derive s0.sp, fnFrame_split_derive_post s0.sp, hout (s0.readReg64 (.gpr 8#5))]
  clear hext_none hexp' hprk hhmac hokm hout hro_eq hinfo_len hx1_bv
  simp only [sepConj_assoc, *]
  wp_done

end CryptoVerification.E2E.Pqxdh.Initiator
