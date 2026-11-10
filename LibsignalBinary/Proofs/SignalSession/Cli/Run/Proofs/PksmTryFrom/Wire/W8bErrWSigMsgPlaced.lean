/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSigMsg
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSharedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bSigMsgPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# Relocatable `[LibsignalPlacement]` `SignalMessage::try_from` Error Continuation

Proves `preKeySigMsgErrW_placed_proof` (`+0x864 → +0x878 → +0x9f0 → +0x504 → ret`) on
`preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

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
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

private theorem w8bSigErr_memRegion184_split (sp' : BitVec 64) :
    memRegion (sp' + 112#64) 184 =
      memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 176#64) 48 ∗ memRegion (sp' + 224#64) 72 := by
  rw [ProofLib.memRegion_split (sp' + 112#64) 32 152 (by decide),
    ProofLib.memRegion_split (sp' + 112#64 + 32#64) 32 120 (by decide),
    ProofLib.memRegion_split (sp' + 112#64 + 32#64 + 32#64) 48 72 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem w8bSigErr_spills96_entails_memRegion
    (sp' : BitVec 64) (kpkVal opkTag opkVal spkId regTag regVal regId ikHi p8z : BitVec 32)
    (msgLen kyberLen w15 bkPtr bkCap msgPtr ikPtr : BitVec 64) :
    ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
      ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
      ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
      ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
      ((sp' + 56#64) ↦₃₂ regId) ∗ ((sp' + 60#64) ↦₃₂ ikHi) ∗
      memRegion (sp' + 64#64) 4 ∗
      ((sp' + 68#64) ↦₃₂ p8z) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ⊢
      memRegion (sp' + 16#64) 96 := by
  have hm56 : ((sp' + 56#64) ↦₃₂ regId) ∗ ((sp' + 60#64) ↦₃₂ ikHi) =
      ((sp' + 56#64) ↦₆₄ (ikHi ++ regId)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      pointsTo32_merge64 (sp' + 56#64) regId ikHi
  refine Entails.trans ?_
    (w8bSeg1Cells_entails_memRegion96 sp' bkCap bkPtr w15 kyberLen ikPtr (ikHi ++ regId)
      msgPtr msgLen regTag regVal opkTag opkVal spkId p8z kpkVal)
  rw [← hm56]
  apply entails_of_eq; ac_rfl

/-- Frame carried across `preKey_sigMsg_err_878_to_9f0_placed_wpX` (`+0x878 → +0x9f0`). -/
def w8bSigErr878FramePlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg bytes : List (BitVec 8)) (ipk : PublicKey) : SepProp :=
  ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
    ((sp' + 56#64) ↦₃₂ identRegId regTag regVal) ∗
    ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 (BitVec.ofNat 64 ik.length)) ∗
    ((sp' + 96#64) ↦₆₄ msgPtr) ∗
    Wire.vecU8Buf A msgCap msgPtr msg ∗
    lsLogOff ∗ A.pool ∗ stackAt sp' preKeyTryFromSubStack ∗
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
    memRegion sp' 12 ∗ memRegion (sp' + 224#64) 72 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 432#64) 8 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ memRegion sret 248 ∗ (ptr ↦ₛ bytes)

/-- Frame `R` carried across `ErrTailCWPlaced.e_9f0_words2_placed_wpE` (`+0x9f0 → +0x504`). -/
def w8bSigErr9f0RestPlaced [LibsignalPlacement] (s0 : State)
    (sp' ptr msgLen kyberLen w15 : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal regId ikHi p8z : BitVec 32)
    (bytes : List (BitVec 8)) : SepProp :=
  ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
    ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
    ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 56#64) ↦₃₂ regId) ∗ ((sp' + 60#64) ↦₃₂ ikHi) ∗
    memRegion (sp' + 64#64) 4 ∗
    ((sp' + 68#64) ↦₃₂ p8z) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
    memRegion sp' 16 ∗
    memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 144#64) 32 ∗
    memRegion (sp' + 224#64) 72 ∗
    memRegion (sp' + 296#64) 152 ∗
    memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ (ptr ↦ₛ bytes) ∗ lsLogOff ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

theorem w8bSigCall_post_open_err_placed [LibsignalPlacement] (A : RustAlloc) (s0 : State)
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
        lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack) ∗
      w8bSigCallFrame A s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr kyberBoxPtr kyberBoxLen
        regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb
        kpkOpt kyberOpt bk ik bytes ipk) =
    ((signalMessageResultAt A [] (sp' + 312#64) r ∗ memRegion (sp' + 176#64) 48) ∗
      w8bSigErr878FramePlaced A s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
        kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7
        p8 p31 w9 w13 w15 w23 vb kpkOpt kyberOpt bk ik msg bytes ipk) := by
  unfold w8bSigCallFrame w8bSigErr878FramePlaced
  rw [show smallRootStack = preKeyTryFromSubStack from rfl, w8b_memRegion120_split48 sp']
  ac_rfl

theorem w8bSigErr_open_9f0_placed [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (ew0 ew1 ew2 ew3 ew4 ew5 : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg bytes : List (BitVec 8)) (ipk : PublicKey) :
    (((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
        ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
        ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ∗
        memRegion (sp' + 312#64) 120) ∗
      w8bSigErr878FramePlaced A s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
        kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7
        p8 p31 w9 w13 w15 w23 vb kpkOpt kyberOpt bk ik msg bytes ipk ⊢
    ∃∗ boxAct : Bool, ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool,
      ((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
        ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
        ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ∗
        memRegion sret 248 ∗
        boxSlot A kyberBoxPtr kyberBoxLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        w8bSigErr9f0RestPlaced s0 sp' ptr (BitVec.ofNat 64 msg.length) kyberLen w15
          regTag regVal opkTag opkVal spkId kpkVal (identRegId regTag regVal)
          (BitVec.extractLsb' 32 32 (BitVec.ofNat 64 ik.length)) (p8.zeroExtend 32) bytes := by
  unfold w8bSigErr878FramePlaced w8bSigErr9f0RestPlaced
  have hm12 := pointsTo32_entails_memRegion (sp' + 12#64) (p7.zeroExtend 32)
  have hm112 := memRegion32_112_pack sp' w23 w9 w13 p31 p0 p1 p2 p3 p4 p5 p6
  have hm144 : ((sp' + 144#64) ↦ₛ ipk.bytes.toList) ⊢ memRegion (sp' + 144#64) 32 := by
    simpa [ipk.bytes.toList_length] using
      ProofLib.pointsToBytes_entails_memRegion (sp' + 144#64) ipk.bytes.toList
  have h152 : memRegion (sp' + 296#64) 152 =
      memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 312#64) 120 ∗
        memRegion (sp' + 432#64) 8 ∗ memRegion (sp' + 440#64) 8 := by
    rw [show (152 : Nat) = 16 + (120 + (8 + 8)) by decide,
      Prost.memRegion_split (sp' + 296#64) 16 136 (by decide),
      Prost.memRegion_split (sp' + 296#64 + 16#64) 120 16 (by decide),
      Prost.memRegion_split (sp' + 296#64 + 16#64 + 120#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hvec (cap ptr0 : BitVec 64) (bs : List (BitVec 8)) :
      Wire.vecU8Buf A cap ptr0 bs ⊢ ∃∗ active : Bool, deallocSlot A cap ptr0 active := by
    refine Entails.trans ?_
      (optVecU8Buf_entails_deallocSlot A cap ptr0 (BitVec.ofNat 64 bs.length) (some bs))
    dsimp only [optVecU8Buf]
    rw [pure_true_emp rfl, emp_sepConj]
    exact Entails.refl _
  have hbox : kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ⊢
      ∃∗ boxAct : Bool, boxSlot A kyberBoxPtr kyberBoxLen boxAct := by
    cases kpkOpt with
    | some kpkId =>
      cases kyberOpt with
      | some kyberCt =>
        dsimp only [kyberStageOut]
        refine Entails.pure_left fun ⟨_, hlen, _⟩ => ?_
        subst hlen
        exact Entails.trans (boxU8Buf_entails_boxSlot A kyberBoxPtr kyberCt)
          (Entails.sepExists_intro (!kyberCt.isEmpty))
      | none =>
        dsimp only [kyberStageOut]
        exact Entails.pure_left_only False.elim
    | none =>
      cases kyberOpt with
      | some _ =>
        dsimp only [kyberStageOut]
        exact Entails.pure_left_only False.elim
      | none =>
        dsimp only [kyberStageOut]
        refine Entails.pure_left_only fun ⟨hptr, _⟩ => ?_
        subst hptr
        exact Entails.trans (boxSlot_of_null A kyberBoxLen) (Entails.sepExists_intro false)
  have hmsg := hvec msgCap msgPtr msg
  have hik := Entails.trans (slice_rest_to_vecU8Buf A ikCap ikPtr ik) (hvec ikCap ikPtr ik)
  have hbk := hvec bkCap bkPtr bk
  rw [stackAt_preKeyTryFromSubStack_skipField sp', w8b_memRegion16_split sp', h152]
  refine Entails.trans
    (Q := kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ∗
      Wire.vecU8Buf A msgCap msgPtr msg ∗
      ((ikPtr ↦ₛ ik) ∗ vecU8Rest A ikCap ikPtr ik) ∗
      Wire.vecU8Buf A bkCap bkPtr bk ∗
      ((sp' + 12#64) ↦₃₂ p7.zeroExtend 32) ∗
      (spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ p31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) p0 p1 p2 p3 p4 p5 p6) ∗
      ((sp' + 144#64) ↦ₛ ipk.bytes.toList) ∗ _)
    (by sep_frame) ?_
  refine Entails.trans
    (sepConj_mono hbox (sepConj_mono hmsg (sepConj_mono hik (sepConj_mono hbk
      (sepConj_mono hm12 (sepConj_mono hm112 (sepConj_mono_left hm144))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bkAct =>
    Entails.sepExists_elim fun ikAct =>
    Entails.sepExists_elim fun msgAct =>
    Entails.sepExists_elim fun boxAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro boxAct)
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  apply entails_of_eq; ac_rfl

theorem w8bSigErr_placed_pack [LibsignalPlacement] {A : RustAlloc} {s0 : State}
    {sp' sret ptr msgLen kyberLen w15 msgPtr ikPtr bkPtr bkCap : BitVec 64}
    {regTag regVal opkTag opkVal spkId kpkVal regId ikHi p8z : BitVec 32}
    {e : SignalProtocolError} {bytes : List (BitVec 8)} :
    pksmErrE A [] sret e ∗ memRegion (sp' + 176#64) 48 ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      w8bSigErr9f0RestPlaced s0 sp' ptr msgLen kyberLen w15 regTag regVal opkTag opkVal spkId kpkVal
        regId ikHi p8z bytes ⊢
    pksmErrE A [] sret e ∗ SepProp.emp ∗
      stackAt sp' preKeyTryFromSubStack ∗
      memRegion sp' 296 ∗
      memRegion (sp' + 296#64) 152 ∗
      memRegion (sp' + 448#64) 64 ∗
      preKeyCalleeSavedAt sp' s0 ∗
      (ptr ↦ₛ bytes) ∗ lsLogOff ∗ A.pool := by
  unfold w8bSigErr9f0RestPlaced
  have hm96 := w8bSigErr_spills96_entails_memRegion sp' kpkVal opkTag opkVal spkId regTag regVal
    regId ikHi p8z msgLen kyberLen w15 bkPtr bkCap msgPtr ikPtr
  rw [emp_sepConj, stackAt_preKeyTryFromSubStack_skipField sp',
    w8bMemRegion296_split_16_96 sp', w8bSigErr_memRegion184_split sp']
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_left hm96)))))
  apply entails_of_eq; ac_rfl

theorem preKeySigMsgErrW_placed_proof [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) :
    PreKeySigMsgErrWPlaced A H := by
  intro x s0 sf vb b1 bs1 m bk ik msg spkId pk ipk e bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen
    regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5 p6 p7 p8
    p31 w9 w13 w15 w23 hcons _hv3 _hv4 hlen hdec _hbkO _hikO hmsgO _hspkO _hreg _hopk _hkpk _hd
    _hokY _hpkb _hik hsig hkst hbkC hikC hmsgC hpc hrun
  have hparse : Pksm.pksmParse x.bytes = none := hcons ▸ pksmParse_msgErr hdec hmsgO hsig
  have hbkNe : bkCap ≠ noneCap := by rintro rfl; revert hbkC; decide
  have hikNe : ikCap ≠ noneCap := by rintro rfl; revert hikC; decide
  have hmsgNe : msgCap ≠ noneCap := by rintro rfl; revert hmsgC; decide
  have hmsg_lt : msg.length < 2 ^ 32 := by
    have hle := w8b_decodePreKey_message_length_le hdec hmsgO
    have hlen' := hlen
    rw [hcons] at hlen'
    exact Nat.lt_of_le_of_lt hle (Nat.lt_of_succ_lt hlen')
  rw [w8bRowI_open_sigCall_placed]
  refine Wire.SepWPp.bind_frame_tryFrom
    (preKey_sigMsg_call_864_to_878_from_ident_placed_wpX (msgPtr := msgPtr)
      (w56 := BitVec.ofNat 64 ik.length) (tag := 0xfffffffffffffffe#64)
      hC hmsg_lt hkst hpc hrun) ?_
  rintro sm1 Pm1 hpc1 hrun1 ⟨hist1, hPm1⟩
  refine SepWPp.mono_pre
    (Entails.trans (sepConj_mono_left hPm1) (Entails.of_eq (w8bSigCall_post_open_err_placed ..))) ?_
  refine Wire.SepWPp.bind_frame_tryFrom
    (preKey_sigMsg_err_878_to_9f0_placed_wpX hsig hist1 hpc1 hrun1) ?_
  rintro sm2 Pm2 hpc2 hrun2 ⟨hst2, hPm2⟩
  refine SepWPp.mono_pre (sepConj_mono_left hPm2) ?_
  refine w8bErrW_exists_pre_frame fun ew0 => w8bErrW_exists_pre_frame fun ew1 =>
    w8bErrW_exists_pre_frame fun ew2 => w8bErrW_exists_pre_frame fun ew3 =>
    w8bErrW_exists_pre_frame fun ew4 => w8bErrW_exists_pre_frame fun ew5 => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun hpack => ?_
  refine SepWPp.mono_pre (w8bSigErr_open_9f0_placed ..) ?_
  refine SepWPp.exists_pre fun boxAct => SepWPp.exists_pre fun msgAct =>
    SepWPp.exists_pre fun ikAct => SepWPp.exists_pre fun bkAct => ?_
  refine SepWPp.bind
    (e_9f0_words2_placed_wpE hC [] boxAct msgAct ikAct bkAct hpack hst2 hpc2 hrun2 hmsgNe hikNe hbkNe) ?_
  rintro sm3 Pm3 hpc3 hrun3 ⟨hst3, _, hPm3⟩
  exact SepWPp.mono_pre (Entails.trans hPm3 w8bSigErr_placed_pack)
    (w8b_errTail_close_placed hparse hst3 hpc3 hrun3)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
