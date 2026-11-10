/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bIdentKey
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailC
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SigMsg
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# Inner `SignalMessage` Decode in `PreKeySignalMessage::try_from`

Discharges the `+0x864` continuation (`PreKey864OkW`) across the `SignalMessage::try_from` call and
`Box<[u8]>` slice clone on the inner message field, branching into the `+0x8c0` success
continuation (`PreKey8c0OkW`), clone allocation failure (`+0xa68`), and decode error
(`PreKeySigMsgErrW`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

/-! ## Message length bound -/

theorem w8b_decodePreKey_message_length_le {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {msg : List (BitVec 8)} (hdec : Pksm.decodeProto bs = some m) (hmsg : m.message = some msg) :
    msg.length ≤ bs.length :=
  (decodeProto_field_length_le hdec).2.2.1 msg hmsg

/-! ## Frames and `+0x8c0` continuation -/

/-- Postcondition state at `+0x8c0` after decoding `SignalMessage` (`sp' + 176 .. 288` and
`msgHeapAt`) and cloning `b` into `clonePtr`. -/
def w8bRowSPost (A : RustAlloc) (sp' clonePtr : BitVec 64) (b : List (BitVec 8))
    (innerMsg : SignalMessage) (msgG : SignalMessageGhost)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56) : SepProp :=
  ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
    ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
    ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
    ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
    ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
    ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
    ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
    ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
    ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
    ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
    ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
    msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
    boxU8Buf A clonePtr b

/-- Frame of `+0x8c0` untouched by `SignalMessage::try_from`, excluding `memRegion (sp' + 312) 120`,
the input slice, `A.pool`, and the `Prost.skipFieldStackX 100` stack. -/
def w8bRowSRest (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' sret bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg : List (BitVec 8)) (ipk : PublicKey) : SepProp :=
  ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 56#64) ↦₃₂ identRegId regTag regVal) ∗
    ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 (BitVec.ofNat 64 ik.length)) ∗
    ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
    ((sp' + 144#64) ↦ₛ ipk.bytes.toList) ∗
    ((sp' + 12#64) ↦₃₂ p7.zeroExtend 32) ∗
    ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
    ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
    ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    memRegion (sp' + 64#64) 4 ∗
    ((sp' + 68#64) ↦₃₂ p8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
    ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
    ((sp' + 96#64) ↦₆₄ msgPtr) ∗
    spUnused112 sp' ∗
    ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ p31) ∗
    ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
    sevenBytesHeadAt (sp' + 136#64) p0 p1 p2 p3 p4 p5 p6 ∗
    kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ∗
    vecU8Rest A ikCap ikPtr ik ∗
    Wire.vecU8Buf A bkCap bkPtr bk ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗
    logOff img ∗
    memRegion sp' 12 ∗ memRegion (sp' + 288#64) 8 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 432#64) 8 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ memRegion sret 248 ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

def w8bRowSFrame (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg bytes : List (BitVec 8)) (ipk : PublicKey) : SepProp :=
  w8bRowSRest img A s0 sp' sret bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr
      kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13
      w15 w23 vb kpkOpt kyberOpt bk ik msg ipk ∗
    memRegion (sp' + 312#64) 120 ∗ (ptr ↦ₛ bytes) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)

/-- Continuation from `+0x8c0` to `ret` after a successful `SignalMessage::try_from` and slice clone. -/
def PreKey8c0OkW (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  ∀ (x : RunCompose.PksmGhost) (s0 sf : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (pk ipk : PublicKey)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32)
    (kyberBoxPtr kyberBoxLen : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64)
    (innerMsg : SignalMessage) (msgG : SignalMessageGhost)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56) (clonePtr : BitVec 64),
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    PublicKey.deserialize bk = .ok pk →
    ((m.kyberPreKeyId.isSome && m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ vb.toNat < 0x40)) →
    (bk.take 33).drop 1 = pkBytesOf p0 p1 p2 p3 p4 p5 p6 p7 p8 w9 w13 w15 w23 p31 →
    PublicKey.deserialize ik = .ok ipk →
    SignalMessage.tryFrom protoSignalCodec msg = .ok innerMsg →
    (∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3)) →
    SigMsgOkState img s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberBoxPtr kyberBoxLen ikCap msgCap vb msgG.pqCap clonePtr bk pk ik ipk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2240#64 →
    sf.status = .Running →
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) sf
      (w8bRowSPost A (s0.sp - 608#64) clonePtr x.bytes innerMsg msgG rk0 rk1 rk2 rk3 addrW0
          addrW1 verHi56 ∗
        w8bRowSFrame img A s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen ikCap ikPtr
          msgCap msgPtr kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal
          p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext
          bk ik msg x.bytes ipk)
      (fun sf' Pf =>
        sf'.sp = s0.sp ∧ (calleeSavedVRegs sf' = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf') ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf'))
      (tryFromQp s0)

/-- Error-branch hypothesis for `PreKey864OkW` when `SignalMessage.tryFrom protoSignalCodec msg`
returns an error (`+0x864 → +0x878 → +0x9f0`). -/
def PreKeySigMsgErrW (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  ∀ (x : RunCompose.PksmGhost) (s0 sf : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (pk ipk : PublicKey) (e : SignalProtocolError)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32)
    (kyberBoxPtr kyberBoxLen : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64),
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    PublicKey.deserialize bk = .ok pk →
    ((m.kyberPreKeyId.isSome && m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ vb.toNat < 0x40)) →
    (bk.take 33).drop 1 = pkBytesOf p0 p1 p2 p3 p4 p5 p6 p7 p8 w9 w13 w15 w23 p31 →
    PublicKey.deserialize ik = .ok ipk →
    SignalMessage.tryFrom protoSignalCodec msg = .error e →
    IdentOkState img s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberBoxPtr kyberBoxLen ikCap msgCap vb (identRegId regTag regVal) bk pk ik ipk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2148#64 →
    sf.status = .Running →
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) sf
      (w8bRowIPost img (s0.sp - 608#64) ikPtr regTag regVal ik ipk ∗
        w8bRowIFrame A s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap
          msgPtr kyberBoxPtr kyberBoxLen opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31
          w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik msg x.bytes)
      (fun sf' Pf =>
        sf'.sp = s0.sp ∧ (calleeSavedVRegs sf' = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf') ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf'))
      (tryFromQp s0)

/-! ## Frame regrouping -/

theorem w8b_memRegion120_split (sp' : BitVec 64) :
    memRegion (sp' + 176#64) 120 =
      memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8 := by
  rw [show (120 : Nat) = 112 + 8 by decide,
    Prost.memRegion_split (sp' + 176#64) 112 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Separation-logic frame preserved across the `SignalMessage::try_from` call (`+0x864 → +0x878`). -/
def w8bSigCallFrame (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik bytes : List (BitVec 8)) (ipk : PublicKey) : SepProp :=
  ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
    ((sp' + 144#64) ↦ₛ ipk.bytes.toList) ∗
    ((sp' + 12#64) ↦₃₂ p7.zeroExtend 32) ∗
    ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
    ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
    ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    memRegion (sp' + 64#64) 4 ∗
    ((sp' + 68#64) ↦₃₂ p8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
    ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
    spUnused112 sp' ∗
    ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ p31) ∗
    ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
    sevenBytesHeadAt (sp' + 136#64) p0 p1 p2 p3 p4 p5 p6 ∗
    kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ∗
    vecU8Rest A ikCap ikPtr ik ∗
    Wire.vecU8Buf A bkCap bkPtr bk ∗
    memRegion sp' 12 ∗ memRegion (sp' + 176#64) 120 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 432#64) 8 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ memRegion sret 248 ∗ (ptr ↦ₛ bytes)

theorem w8bRowI_open_sigCall (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg bytes : List (BitVec 8)) (ipk : PublicKey) :
    (w8bRowIPost img sp' ikPtr regTag regVal ik ipk ∗
      w8bRowIFrame A s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr
        kyberBoxLen opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb
        kpkOpt kyberOpt bk ik msg bytes) =
    ((((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
        ((sp' + 56#64) ↦₆₄ BitVec.ofNat 64 ik.length) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        ((sp' + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
        memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72 ∗
        Wire.vecU8Buf A msgCap msgPtr msg ∗
        logOff img ∗ A.pool ∗ stackAt sp' smallRootStack) ∗
      w8bSigCallFrame A s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr kyberBoxPtr kyberBoxLen
        regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb
        kpkOpt kyberOpt bk ik bytes ipk) := by
  unfold w8bRowIPost w8bRowIFrame w8bSigCallFrame
  rw [show smallRootStack = preKeyTryFromSubStack from rfl,
    stackAt_sub_split sp' (Prost.skipFieldStackX 100) preKeyTryFromSubStack (by decide) (by decide)]
  ac_rfl

theorem w8bSigCall_post_open_ok (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg bytes : List (BitVec 8)) (ipk : PublicKey)
    (r : Except SignalProtocolError SignalMessage) :
    ((((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
        ((sp' + 56#64) ↦₃₂ identRegId regTag regVal) ∗
        ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 (BitVec.ofNat 64 ik.length)) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        signalMessageResultAt A [] (sp' + 312#64) r ∗
        Wire.vecU8Buf A msgCap msgPtr msg ∗
        logOff img ∗ A.pool ∗ stackAt sp' smallRootStack) ∗
      w8bSigCallFrame A s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr kyberBoxPtr kyberBoxLen
        regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb
        kpkOpt kyberOpt bk ik bytes ipk) =
    ((signalMessageResultAt A [] (sp' + 312#64) r ∗ memRegion (sp' + 176#64) 112 ∗
        (ptr ↦ₛ bytes) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
      w8bRowSRest img A s0 sp' sret bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr
        kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13
        w15 w23 vb kpkOpt kyberOpt bk ik msg ipk) := by
  unfold w8bSigCallFrame w8bRowSRest
  rw [show smallRootStack = preKeyTryFromSubStack from rfl,
    stackAt_sub_split sp' (Prost.skipFieldStackX 100) preKeyTryFromSubStack (by decide) (by decide),
    w8b_memRegion120_split sp']
  ac_rfl

/-! ## `+0x864` continuation -/

/-- Reduces `PreKey864OkW` to `PreKey8c0OkW` on success and `PreKeySigMsgErrW` on decode error,
discharging the clone allocation-failure branch via `pan_a68_wpX`. -/
theorem preKey864OkW_of_8c0 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hSigTryFrom : subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr tryFromName) (tryFromSpec A img))
    (hTryClone : TryCloneFromRefOkX img A ext)
    (hErr : PreKeySigMsgErrW img A ext) (hOk : PreKey8c0OkW img A ext) :
    PreKey864OkW img A ext := by
  intro x s0 sf vb b1 bs1 m bk ik msg spkId pk ipk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen
    regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5 p6 p7 p8
    p31 w9 w13 w15 w23 hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk hkpk hd hokY hpkb
    hik hkst hbkC hikC hmsgC hpc hrun
  cases hsig : SignalMessage.tryFrom protoSignalCodec msg with
  | error e =>
    exact hErr x s0 sf vb b1 bs1 m bk ik msg spkId pk ipk e bkCap bkPtr ikCap ikPtr msgCap msgPtr
      kyberLen regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5
      p6 p7 p8 p31 w9 w13 w15 w23 hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk hkpk hd
      hokY hpkb hik hsig hkst hbkC hikC hmsgC hpc hrun
  | ok innerMsg =>
    have hmsg_lt : msg.length < 2 ^ 32 := by
      have hle := w8b_decodePreKey_message_length_le hdec hmsgO
      have hlen' := hlen
      rw [hcons] at hlen'
      exact Nat.lt_of_le_of_lt hle (Nat.lt_of_succ_lt hlen')
    have hcomm : ∀ (φ : Prop) (P R : SepProp), (P ∗ (⌜φ⌝ ∗ R)) = (⌜φ⌝ ∗ (P ∗ R)) :=
      fun φ P R => sepConj_left_comm P ⌜φ⌝ R
    rw [w8bRowI_open_sigCall]
    refine SepWPp.bind_frame_tryFrom
      (preKey_sigMsg_call_864_to_878_from_ident_wpX (msgPtr := msgPtr)
        (w56 := BitVec.ofNat 64 ik.length) (tag := 0xfffffffffffffffe#64)
        hSigTryFrom hmsg_lt hkst hpc hrun) ?_
    rintro sm1 Pm1 hpc1 hrun1 ⟨hist1, hPm1⟩
    refine SepWPp.mono_pre
      (Entails.trans (sepConj_mono_left hPm1) (Entails.of_eq (w8bSigCall_post_open_ok ..))) ?_
    refine SepWPp.bind_frame_tryFrom
      (preKey_sigMsg_ok_878_to_8bc_wpX hTryClone hsig hlen hist1 hpc1 hrun1) ?_
    rintro sm2 Pm2 hpc2 hrun2 ⟨hsp2, hal2, hF2, hsym2, hbk2, hpkeq2, hpkb2, hik2, hx1, hx29, hx28,
      hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19, hPm2⟩
    refine SepWPp.mono_pre (sepConj_mono_left hPm2) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_pre fun msgG => SepWPp.exists_pre fun rk0 => SepWPp.exists_pre fun rk1 =>
      SepWPp.exists_pre fun rk2 => SepWPp.exists_pre fun rk3 =>
      SepWPp.exists_pre fun addrW0 => SepWPp.exists_pre fun addrW1 =>
      SepWPp.exists_pre fun verHi56 => SepWPp.pure_pre fun ⟨hx27, hrk⟩ => ?_
    by_cases hx0 : sm2.readReg64 .x0 = 0#64
    · rw [ite_eq_left hx0]
      simp only [hcomm]
      refine SepWPp.pure_pre fun ⟨_, htr2⟩ => ?_
      refine SepWPp.mono_pre (Entails.of_eq (emp_sepConj _).symm) ?_
      refine SepWPp.bind_frame_tryFrom
        (preKey_sigMsg_clone_oom_8bc_to_a68_wpX (len := BitVec.ofNat 64 x.bytes.length)
          hsp2 hal2 hF2 hsym2 htr2 hpc2 hrun2 hx0 hx20) ?_
      rintro sm3 _ hpc3 hrun3 ⟨hfail3, -, -⟩
      exact pan_a68_wpX hfail3 hpc3 hrun3
    · rw [ite_eq_right hx0]
      simp only [sepConj_assoc, hcomm]
      refine SepWPp.pure_pre fun htr2 => ?_
      refine SepWPp.mono_pre (Entails.of_eq (emp_sepConj _).symm) ?_
      refine SepWPp.bind_frame_tryFrom
        (preKey_sigMsg_clone_ok_8bc_to_8c0_wpX (clonePtr := sm2.readReg64 .x0) hx0 hsp2 hal2 hF2
          hsym2 htr2 hbk2 hpkeq2 hpkb2 hik2 hpc2 hrun2 rfl hx1 hx29 hx28 hx27 hx26 hx25 hx24 hx23
          hx22 hx21 hx20 hx19) ?_
      rintro sm3 Pm3 hpc3 hrun3 ⟨hok3, hPm3⟩
      refine SepWPp.mono_pre (Entails.trans (sepConj_mono_left hPm3)
        (Entails.of_eq (emp_sepConj _))) ?_
      refine SepWPp.mono_pre (Entails.of_eq ?_)
        (hOk x s0 sm3 vb b1 bs1 m bk ik msg spkId pk ipk bkCap bkPtr ikCap ikPtr msgCap msgPtr
          kyberLen regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4
          p5 p6 p7 p8 p31 w9 w13 w15 w23 innerMsg msgG rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56
          (sm2.readReg64 .x0) hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk hkpk hd hokY
          hpkb hik hsig hrk hok3 hbkC hikC hmsgC hpc3 hrun3)
      unfold w8bRowSPost w8bRowSFrame
      ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
