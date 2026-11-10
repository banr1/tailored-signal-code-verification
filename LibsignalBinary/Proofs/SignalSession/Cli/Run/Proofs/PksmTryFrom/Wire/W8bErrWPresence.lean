/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPostLoop
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresenceB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWShared
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: Missing-Field Error Continuations (`PreKeyPresenceErrW`)

Proves `preKeyPresenceErrW_proof` (`+0x460 → +0x5e0` / `+0x61c` / `+0x66c` / `+0x678 → +0x504 → ret`)
when any of `base_key`, `identity_key`, `message`, or `signed_pre_key_id` is `none`.
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
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

theorem w8b_memRegion296_split96_104 (sp' : BitVec 64) :
    memRegion sp' 296 ⊢
      ∃∗ w104 : BitVec 64, ∃∗ w96 : BitVec 64,
        memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
          memRegion (sp' + 112#64) 184 := by
  rw [show (296 : Nat) = 96 + (8 + (8 + 184)) by decide,
    Prost.memRegion_split sp' 96 200 (by decide),
    Prost.memRegion_split (sp' + 96#64) 8 192 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 184 (by decide),
    ProofLib.memRegion_eight (sp' + 96#64),
    ProofLib.memRegion_eight (sp' + 96#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem w8b_memRegion296_repack96_104 (sp' w96 w104 : BitVec 64) :
    memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
      memRegion (sp' + 112#64) 184 ⊢ memRegion sp' 296 := by
  rw [show (296 : Nat) = 96 + (8 + (8 + 184)) by decide,
    Prost.memRegion_split sp' 96 200 (by decide),
    Prost.memRegion_split (sp' + 96#64) 8 192 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion (sp' + 96#64) w96)
    (sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 104#64) w104)))

private theorem w8b_optVecU8Buf_none (A : RustAlloc) (cap ptr len : BitVec 64) :
    optVecU8Buf A cap ptr len none = ⌜cap = noneCap⌝ := rfl

private theorem w8b_optVecU8At_none_entails (A : RustAlloc) (pin : VecPin) (slot : BitVec 64) :
    CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A pin slot none ⊢
      ∃∗ bkp : BitVec 64, ∃∗ bkl : BitVec 64, vecHeader slot noneCap bkp bkl := by
  refine Entails.trans (Wire.optVecU8At_entails_header_buf A pin slot none) ?_
  refine Entails.sepExists_elim fun bkc => Entails.sepExists_elim fun bkp =>
    Entails.sepExists_elim fun bkl => ?_
  rw [w8b_optVecU8Buf_none, sepConj_comm]
  refine Entails.pure_left fun hbkc => ?_
  subst hbkc
  exact Entails.trans
    (Entails.sepExists_intro (P := fun bkl => vecHeader slot noneCap bkp bkl) bkl)
    (Entails.sepExists_intro (P := fun bkp => ∃∗ bkl, vecHeader slot noneCap bkp bkl) bkp)

private theorem w8b_wirePreKeyAt_bk_some_eq (A : RustAlloc) (g : WirePreKeyGhost) (a : BitVec 64)
    (m : ProtoPreKeySignalMessage) {bk : List (BitVec 8)} (hbk : m.baseKey = some bk) :
    wirePreKeyAt A g a m =
      (CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A g.kyberCt a m.kyberCiphertext ∗
        (vecHeader (a + 0x18#64) g.baseKey.cap g.baseKey.ptr (BitVec.ofNat 64 bk.length) ∗
          Wire.vecU8Buf A g.baseKey.cap g.baseKey.ptr bk) ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A g.identityKey (a + 0x30#64) m.identityKey ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A g.message (a + 0x48#64) m.message ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x60#64) m.registrationId ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x68#64) m.preKeyId ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x70#64) m.signedPreKeyId ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x78#64) m.kyberPreKeyId) := by
  unfold wirePreKeyAt
  rw [hbk]
  rfl

theorem w8b_memRegion152_of_parts (sp' : BitVec 64) :
    memRegion (sp' + 296#64) 16 ∗
      (memRegion (sp' + 312#64) 48 ∗
        (memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8) ∗
        memRegion (sp' + 440#64) 8) =
      memRegion (sp' + 296#64) 152 := by
  have h80 :
      memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 =
        memRegion (sp' + 360#64) 80 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      (Prost.memRegion_split (sp' + 360#64) 72 8 (by decide)).symm
  have h88 :
      memRegion (sp' + 360#64) 80 ∗ memRegion (sp' + 440#64) 8 =
        memRegion (sp' + 360#64) 88 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      (Prost.memRegion_split (sp' + 360#64) 80 8 (by decide)).symm
  have h136 :
      memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 88 =
        memRegion (sp' + 312#64) 136 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      (Prost.memRegion_split (sp' + 312#64) 48 88 (by decide)).symm
  rw [h80, h88, h136]
  simpa [BitVec.add_assoc, BitVec.reduceAdd] using
    (Prost.memRegion_split (sp' + 296#64) 16 136 (by decide)).symm

theorem w8b_word8_memRegion40_entails_memRegion48 (p w : BitVec 64) :
    (p ↦₆₄ w) ∗ memRegion (p + 8#64) 40 ⊢ memRegion p 48 := by
  rw [show (48 : Nat) = 8 + 40 by decide, Prost.memRegion_split p 8 40 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion p w)

/-- Two consecutive 24-byte `vecHeader`s at `sp' + 312` and `sp' + 336` entail `memRegion (sp' + 312) 48`. -/
theorem w8b_vecHeaders2_entails_memRegion48 (sp' c1 p1 l1 c2 p2 l2 : BitVec 64) :
    vecHeader (sp' + 312#64) c1 p1 l1 ∗ vecHeader (sp' + 336#64) c2 p2 l2 ⊢
      memRegion (sp' + 312#64) 48 := by
  dsimp only [vecHeader]
  rw [ProofLib.memRegion_split (sp' + 312#64) 8 40 (by decide),
    ProofLib.memRegion_split (sp' + 312#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (sp' + 312#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (sp' + 312#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 312#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))

/-- Frame outside the `BkNone` dealloc chain at `+0x5e0`. -/
def w8bBkNoneRest (img : Obj.Image) (s0 : State)
    (sp' sret ptr kyberPtr kyberLen bkPtr bkLen ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64)
    (regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32)
    (bytes : List (BitVec 8)) : SepProp :=
  vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
    vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
    vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
    vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
    ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
    ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
    ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
    ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
    memRegion sp' 96 ∗ memRegion (sp' + 112#64) 184 ∗
    memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 440#64) 8 ∗
    memRegion (sp' + 448#64) 64 ∗ preKeyCalleeSavedAt sp' s0 ∗
    memRegion (sret + 16#64) 232 ∗
    (ptr ↦ₛ bytes) ∗ logOff img ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

/-- Final `BkNone` regroup at `+0x504` (`1284`) into the `w8b_errTail_close` precondition. -/
theorem w8bBkNone_pack {img : Obj.Image} {A : RustAlloc} {s0 : State}
    {sp' sret ptr kyberPtr kyberLen bkPtr bkLen ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64}
    {regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32}
    {bytes : List (BitVec 8)} :
    ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 2) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        w8bBkNoneRest img s0 sp' sret ptr kyberPtr kyberLen bkPtr bkLen
          ikCap ikPtr ikLen msgCap msgPtr msgLen
          regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal bytes) ⊢
    pksmErrE A [] sret .invalidProtobufEncoding ∗ SepProp.emp ∗
      stackAt sp' preKeyTryFromSubStack ∗
      memRegion sp' 296 ∗
      memRegion (sp' + 296#64) 152 ∗
      memRegion (sp' + 448#64) 64 ∗
      preKeyCalleeSavedAt sp' s0 ∗
      (ptr ↦ₛ bytes) ∗ logOff img ∗ A.pool := by
  rw [emp_sepConj, stackAt_preKeyTryFromSubStack_skipField sp', ← w8b_memRegion152_of_parts sp']
  have h48 := w8b_vecHeaders2_entails_memRegion48 sp'
    0x8000000000000002#64 kyberPtr kyberLen noneCap bkPtr bkLen
  have h80 := post_headers_entails_memRegion80W sp' ikCap ikPtr ikLen msgCap msgPtr msgLen
    regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal
  have h296 := w8b_memRegion296_repack96_104 sp' msgPtr ikPtr
  refine Entails.trans (Q :=
      ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 2) ∗ memRegion (sret + 16#64) 232) ∗
      (memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
          (preKeyTryFromSubStack - Prost.skipFieldStackX 100) ∗
        stackAt sp' (Prost.skipFieldStackX 100)) ∗
      (memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 112#64) 184) ∗
      (memRegion (sp' + 296#64) 16 ∗
        (vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
          vecHeader (sp' + 336#64) noneCap bkPtr bkLen) ∗
        (vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
          vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)) ∗
        memRegion (sp' + 440#64) 8) ∗
      memRegion (sp' + 448#64) 64 ∗
      preKeyCalleeSavedAt sp' s0 ∗
      (ptr ↦ₛ bytes) ∗ logOff img ∗ A.pool)
    (by unfold w8bBkNoneRest; apply entails_of_eq; ac_rfl) ?_
  refine Entails.trans
    (sepConj_mono (errCells_invalidProtobufEncoding A [] sret)
      (sepConj_mono_right (sepConj_mono h296
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono h48 (sepConj_mono_left h80))))))) ?_
  apply entails_of_eq; ac_rfl

/-- Frame outside the `IkNone` / `MsgNone` / `SpkNone` dealloc chains (after `post_bk_some_to_57c_wpW`). -/
def w8bBkSomePresRest (img : Obj.Image) (s0 : State)
    (sp' sret ptr msgLen kyberLen ikLen bkLen : BitVec 64)
    (regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32)
    (bytes : List (BitVec 8)) : SepProp :=
  ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
    ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
    ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
    ((sp' + 68#64) ↦₃₂ kpkTag) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗
    memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    memRegion sp' 16 ∗ memRegion (sp' + 112#64) 184 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗
    memRegion (sret + 16#64) 232 ∗
    (ptr ↦ₛ bytes) ∗ logOff img ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

/-- Final `IkNone` / `MsgNone` / `SpkNone` regroup at `+0x504` (`1284`) into `w8b_errTail_close` pre. -/
theorem w8bBkSomePres_pack {img : Obj.Image} {A : RustAlloc} {s0 : State}
    {sp' sret ptr msgLen kyberLen ikLen bkLen bkPtr bkCap msgPtr ikPtr w312 : BitVec 64}
    {regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32}
    {bytes : List (BitVec 8)} :
    ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 2) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        (((sp' + 312#64) ↦₆₄ w312) ∗ memRegion (sp' + 320#64) 40 ∗
          w8bBkSomePresRest img s0 sp' sret ptr msgLen kyberLen ikLen bkLen
            regTag regVal opkTag opkVal spkVal kpkTag kpkVal bytes)) ⊢
    pksmErrE A [] sret .invalidProtobufEncoding ∗ SepProp.emp ∗
      stackAt sp' preKeyTryFromSubStack ∗
      memRegion sp' 296 ∗
      memRegion (sp' + 296#64) 152 ∗
      memRegion (sp' + 448#64) 64 ∗
      preKeyCalleeSavedAt sp' s0 ∗
      (ptr ↦ₛ bytes) ∗ logOff img ∗ A.pool := by
  rw [emp_sepConj, stackAt_preKeyTryFromSubStack_skipField sp',
    w8bMemRegion296_split_16_96 sp', ← w8b_memRegion152_of_parts sp']
  have h48 : ((sp' + 312#64) ↦₆₄ w312) ∗ memRegion (sp' + 320#64) 40 ⊢ memRegion (sp' + 312#64) 48 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      w8b_word8_memRegion40_entails_memRegion48 (sp' + 312#64) w312
  have h96 := w8bSeg1Cells_entails_memRegion96 sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen
    msgPtr msgLen regTag regVal opkTag opkVal spkVal kpkTag kpkVal
  refine Entails.trans ?_
    (sepConj_mono (errCells_invalidProtobufEncoding A [] sret)
      (sepConj_mono_right (sepConj_mono
        (sepConj_mono_right (sepConj_mono_left h96))
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left h48))))))
  unfold w8bBkSomePresRest
  apply entails_of_eq; ac_rfl

private theorem w8b_reassoc_61c (S0 S8 P80 P88 P96 Pool Stack W312 M320 P104 Rest : SepProp) :
    S0 ∗ S8 ∗ P80 ∗ P88 ∗ P96 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ (P104 ∗ Rest)) =
      S0 ∗ S8 ∗ P96 ∗ P104 ∗ P80 ∗ P88 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ Rest) := by
  ac_rfl

private theorem w8b_reassoc_66c (S0 S8 P104 P80 P88 Pool Stack W312 M320 P96 Rest : SepProp) :
    S0 ∗ S8 ∗ P104 ∗ P80 ∗ P88 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ (P96 ∗ Rest)) =
      S0 ∗ S8 ∗ P96 ∗ P104 ∗ P80 ∗ P88 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ Rest) := by
  ac_rfl

/-- Regroup `entry_61c_wpX` post into `w8bBkSomePres_pack` pre (`+0x504`). -/
theorem w8bBkSomePres_pack_61c {img : Obj.Image} {A : RustAlloc} {s0 : State}
    {sp' sret ptr msgLen kyberLen ikLen bkLen bkPtr bkCap msgPtr ikPtr w312 : BitVec 64}
    {regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32}
    {bytes : List (BitVec 8)} :
    ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 2) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        (((sp' + 312#64) ↦₆₄ w312) ∗ memRegion (sp' + 320#64) 40 ∗
          (((sp' + 104#64) ↦₆₄ ikPtr) ∗
            w8bBkSomePresRest img s0 sp' sret ptr msgLen kyberLen ikLen bkLen
              regTag regVal opkTag opkVal spkVal kpkTag kpkVal bytes))) ⊢
    pksmErrE A [] sret .invalidProtobufEncoding ∗ SepProp.emp ∗
      stackAt sp' preKeyTryFromSubStack ∗
      memRegion sp' 296 ∗
      memRegion (sp' + 296#64) 152 ∗
      memRegion (sp' + 448#64) 64 ∗
      preKeyCalleeSavedAt sp' s0 ∗
      (ptr ↦ₛ bytes) ∗ logOff img ∗ A.pool := by
  rw [w8b_reassoc_61c]
  exact w8bBkSomePres_pack

/-- Regroup `entry_66c_wpX` post into `w8bBkSomePres_pack` pre (`+0x504`). -/
theorem w8bBkSomePres_pack_66c {img : Obj.Image} {A : RustAlloc} {s0 : State}
    {sp' sret ptr msgLen kyberLen ikLen bkLen bkPtr bkCap msgPtr ikPtr w312 : BitVec 64}
    {regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32}
    {bytes : List (BitVec 8)} :
    ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 2) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        (((sp' + 312#64) ↦₆₄ w312) ∗ memRegion (sp' + 320#64) 40 ∗
          (((sp' + 96#64) ↦₆₄ msgPtr) ∗
            w8bBkSomePresRest img s0 sp' sret ptr msgLen kyberLen ikLen bkLen
              regTag regVal opkTag opkVal spkVal kpkTag kpkVal bytes))) ⊢
    pksmErrE A [] sret .invalidProtobufEncoding ∗ SepProp.emp ∗
      stackAt sp' preKeyTryFromSubStack ∗
      memRegion sp' 296 ∗
      memRegion (sp' + 296#64) 152 ∗
      memRegion (sp' + 448#64) 64 ∗
      preKeyCalleeSavedAt sp' s0 ∗
      (ptr ↦ₛ bytes) ∗ logOff img ∗ A.pool := by
  rw [w8b_reassoc_66c]
  exact w8bBkSomePres_pack

/-- Regroup `post_ik_none_full_to_61c_wpW` post into `entry_61c_wpX` pre. -/
theorem w8b_open_61c (D1 W0 W8 P80 P88 D2 D3 P96 Pool Stack W312 M320 R : SepProp) :
    (D1 ∗ W0 ∗ W8 ∗ P80 ∗ P88 ∗ D2 ∗ D3 ∗ P96 ∗ Pool ∗ Stack ∗ W312 ∗ M320) ∗ R =
      D1 ∗ W0 ∗ W8 ∗ P80 ∗ P88 ∗ D2 ∗ D3 ∗ P96 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ R) := by
  ac_rfl

/-- Regroup `post_msg_none_full_to_66c_wpW` post into `entry_66c_wpX` pre. -/
theorem w8b_open_66c (W0 W8 D1 P104 D2 P80 P88 D3 Pool Stack W312 M320 R : SepProp) :
    (W0 ∗ W8 ∗ D1 ∗ P104 ∗ D2 ∗ P80 ∗ P88 ∗ D3 ∗ Pool ∗ Stack ∗ W312 ∗ M320) ∗ R =
      W0 ∗ W8 ∗ D1 ∗ P104 ∗ D2 ∗ P80 ∗ P88 ∗ D3 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ R) := by
  ac_rfl

/-- Regroup `post_spk_none_full_to_678_wpW` post into `entry_678_wpX` pre. -/
theorem w8b_open_678 (W0 W8 D1 P96 D2 P104 D3 P80 P88 D4 Pool Stack W312 M320 R : SepProp) :
    (W0 ∗ W8 ∗ D1 ∗ P96 ∗ D2 ∗ P104 ∗ D3 ∗ P80 ∗ P88 ∗ D4 ∗ Pool ∗ Stack ∗ W312 ∗ M320) ∗ R =
      W0 ∗ W8 ∗ D1 ∗ P96 ∗ D2 ∗ P104 ∗ D3 ∗ P80 ∗ P88 ∗ D4 ∗ Pool ∗ Stack ∗ (W312 ∗ M320 ∗ R) := by
  ac_rfl

/-- Regroup `+0x57c` pre for Branch 2 (`ikOpt = none`). -/
theorem w8b_open_ik_none (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml w0 w8 : BitVec 64)
    (regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32)
    (kyberOpt msgOpt : Option (List (BitVec 8))) (bk bytes : List (BitVec 8)) :
    (seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kl ikp ikl mp ml
        regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
      memRegion (sp' + 312#64) 48 ∗
      memRegion (sp' + 360#64) 72 ∗
      memRegion (sp' + 432#64) 8 ∗
      optVecU8Buf A kc kp kl kyberOpt ∗
      Wire.vecU8Buf A bkCap bkPtr bk ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
    (⌜ikc = noneCap⌝ ∗
      optVecU8Buf A mc mp ml msgOpt ∗
      (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗
      memRegion sp' 16 ∗ memRegion (sp' + 112#64) 184 ∗
      memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 440#64) 8 ∗
      memRegion (sp' + 448#64) 64 ∗ preKeyCalleeSavedAt sp' s0 ∗
      memRegion (sret + 16#64) 232 ∗
      (ptr ↦ₛ bytes) ∗ logOff img ∗
      memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
        (preKeyTryFromSubStack - Prost.skipFieldStackX 100)) =
    ⌜ikc = noneCap⌝ ∗
      ((memRegion (sp' + 312#64) 48 ∗
        (Wire.vecU8Buf A bkCap bkPtr bk ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kc kp kl kyberOpt ∗
          optVecU8Buf A mc mp ml msgOpt ∗ ((sp' + 96#64) ↦₆₄ mp) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))) ∗
      (((sp' + 104#64) ↦₆₄ ikp) ∗
        w8bBkSomePresRest img s0 sp' sret ptr ml kl ikl
          (BitVec.ofNat 64 bk.length) regTag regVal opkTag opkVal spkVal kpkTag kpkVal bytes)) := by
  unfold seg1SpillsAtW w8bBkSomePresRest
  ac_rfl

/-- Regroup `+0x57c` pre for `ikOpt = some ik` (`post_ik_some_to_590_wpW`). -/
theorem w8b_open_ik_some (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml w0 w8 : BitVec 64)
    (regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32)
    (kyberOpt msgOpt : Option (List (BitVec 8))) (bk ik bytes : List (BitVec 8)) :
    (seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kl ikp ikl mp ml
        regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
      memRegion (sp' + 312#64) 48 ∗
      memRegion (sp' + 360#64) 72 ∗
      memRegion (sp' + 432#64) 8 ∗
      optVecU8Buf A kc kp kl kyberOpt ∗
      Wire.vecU8Buf A bkCap bkPtr bk ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
    ((⌜ikc.toNat < 2 ^ 63⌝ ∗ Wire.vecU8Buf A ikc ikp ik) ∗
      optVecU8Buf A mc mp ml msgOpt ∗
      (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗
      memRegion sp' 16 ∗ memRegion (sp' + 112#64) 184 ∗
      memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 440#64) 8 ∗
      memRegion (sp' + 448#64) 64 ∗ preKeyCalleeSavedAt sp' s0 ∗
      memRegion (sret + 16#64) 232 ∗
      (ptr ↦ₛ bytes) ∗ logOff img ∗
      memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
        (preKeyTryFromSubStack - Prost.skipFieldStackX 100)) =
    ⌜ikc.toNat < 2 ^ 63⌝ ∗
      ((memRegion (sp' + 312#64) 48 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
      (Wire.vecU8Buf A ikc ikp ik ∗
        optVecU8Buf A mc mp ml msgOpt ∗
        optVecU8Buf A kc kp kl kyberOpt ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ mp) ∗ ((sp' + 104#64) ↦₆₄ ikp) ∗
        w8bBkSomePresRest img s0 sp' sret ptr ml kl ikl
          (BitVec.ofNat 64 bk.length) regTag regVal opkTag opkVal spkVal kpkTag kpkVal bytes)) := by
  unfold seg1SpillsAtW w8bBkSomePresRest
  ac_rfl

/-- Regroup `+0x590` pre for Branch 3 (`msgOpt = none`). -/
theorem w8b_open_msg_none (M48 Pool Stack Ik Pmc Ky Bk W0 W8 P80 P88 P96 P104 Rest : SepProp) :
    (M48 ∗ Pool ∗ Stack) ∗ (Ik ∗ Pmc ∗ Ky ∗ Bk ∗ W0 ∗ W8 ∗ P80 ∗ P88 ∗ P96 ∗ P104 ∗ Rest) =
      Pmc ∗ ((M48 ∗ (W0 ∗ W8 ∗ Ik ∗ P104 ∗ Bk ∗ P80 ∗ P88 ∗ Ky ∗ Pool ∗ Stack)) ∗ (P96 ∗ Rest)) := by
  ac_rfl

/-- Regroup `+0x590` pre for `msgOpt = some msg` (`post_msg_some_to_5a4_wpW`). -/
theorem w8b_open_msg_some (M48 Pool Stack Ik Pmc Msg Ky Bk W0 W8 P80 P88 P96 P104 Rest : SepProp) :
    (M48 ∗ Pool ∗ Stack) ∗ (Ik ∗ (Pmc ∗ Msg) ∗ Ky ∗ Bk ∗ W0 ∗ W8 ∗ P80 ∗ P88 ∗ P96 ∗ P104 ∗ Rest) =
      Pmc ∗ ((M48 ∗ Pool ∗ Stack) ∗ (Msg ∗ Ik ∗ Ky ∗ Bk ∗ W0 ∗ W8 ∗ P80 ∗ P88 ∗ P96 ∗ P104 ∗ Rest)) := by
  ac_rfl

/-- Regroup `+0x5a4` pre for Branch 4 (`spkOpt = none`). -/
theorem w8b_open_spk_none (M48 Pool Stack Msg Ik Ky Bk W0 W8 P80 P88 P96 P104 Rest : SepProp) :
    (M48 ∗ Pool ∗ Stack) ∗ (Msg ∗ Ik ∗ Ky ∗ Bk ∗ W0 ∗ W8 ∗ P80 ∗ P88 ∗ P96 ∗ P104 ∗ Rest) =
      (M48 ∗ (W0 ∗ W8 ∗ Msg ∗ P96 ∗ Ik ∗ P104 ∗ Bk ∗ P80 ∗ P88 ∗ Ky ∗ Pool ∗ Stack)) ∗ Rest := by
  ac_rfl

/-- Branch 1 (`m.baseKey = none`) of `PreKeyPresenceErrW`. -/
theorem w8b_presenceErr_bk_none {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : PksmCallees img A ext)
    (x : RunCompose.PksmGhost) (s0 s : State) (vb : BitVec 8) (m : ProtoPreKeySignalMessage)
    (hparse : Pksm.pksmParse x.bytes = none)
    (hbkO : m.baseKey = none)
    (hst : PreKeyLoopExitState img s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) s
      (wirePreKeyOf A (s0.sp - 608#64 + 312#64) m ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗
        A.pool ∗ stackAt (s0.sp - 608#64) preKeyTryFromSubStack)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf))
      (tryFromQp s0) := by
  rw [w8bMemRegion248_eq_words2 x.ret, stackAt_preKeyTryFromSubStack_skipField]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (w8b_memRegion296_split96_104 (s0.sp - 608#64)))) ?_
  unfold wirePreKeyOf
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun g => ?_
  unfold wirePreKeyAt
  rw [hbkO]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.exists_pre fun w8 => SepWPp.exists_pre fun w0 =>
    SepWPp.exists_pre fun w104 => SepWPp.exists_pre fun w96 => ?_
  refine SepWPp.mono_pre
    (sepConj_mono (Wire.optVecU8At_entails_header_buf A g.kyberCt _ m.kyberCiphertext)
      (sepConj_mono (w8b_optVecU8At_none_entails A g.baseKey _) (sepConj_mono
        (Wire.optVecU8At_entails_header_buf A g.identityKey _ m.identityKey)
        (sepConj_mono (Wire.optVecU8At_entails_header_buf A g.message _ m.message)
          (sepConj_mono (w8b_optU32At_entails _ m.registrationId)
            (sepConj_mono (w8b_optU32At_entails _ m.preKeyId)
              (sepConj_mono (w8b_optU32At_entails _ m.signedPreKeyId)
                (sepConj_mono_left (w8b_optU32At_entails _ m.kyberPreKeyId))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.exists_pre fun pKpk => SepWPp.exists_pre fun pSpk =>
    SepWPp.exists_pre fun pOpk => SepWPp.exists_pre fun pReg =>
    SepWPp.exists_pre fun mc => SepWPp.exists_pre fun mp => SepWPp.exists_pre fun ml =>
    SepWPp.exists_pre fun ikc => SepWPp.exists_pre fun ikp => SepWPp.exists_pre fun ikl =>
    SepWPp.exists_pre fun bkp => SepWPp.exists_pre fun bkl =>
    SepWPp.exists_pre fun kc => SepWPp.exists_pre fun kp => SepWPp.exists_pre fun kl => ?_
  refine SepWPp.mono_pre (P' :=
      (((((s0.sp - 608#64 + 96#64) ↦₆₄ w96) ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ w104) ∗
          vecHeader (s0.sp - 608#64 + 312#64) kc kp kl ∗
          optVecU8Buf A kc kp kl m.kyberCiphertext ∗
          vecHeader (s0.sp - 608#64 + 336#64) noneCap bkp bkl ∗
          vecHeader (s0.sp - 608#64 + 360#64) ikc ikp ikl ∗
          vecHeader (s0.sp - 608#64 + 384#64) mc mp ml ∗
          ((s0.sp - 608#64 + 408#64) ↦₃₂ pReg.1.1) ∗ ((s0.sp - 608#64 + 412#64) ↦₃₂ pReg.1.2) ∗
          ((s0.sp - 608#64 + 416#64) ↦₃₂ pOpk.1.1) ∗ ((s0.sp - 608#64 + 420#64) ↦₃₂ pOpk.1.2) ∗
          ((s0.sp - 608#64 + 424#64) ↦₃₂ pSpk.1.1) ∗ ((s0.sp - 608#64 + 428#64) ↦₃₂ pSpk.1.2) ∗
          ((s0.sp - 608#64 + 432#64) ↦₃₂ pKpk.1.1) ∗ ((s0.sp - 608#64 + 436#64) ↦₃₂ pKpk.1.2)) ∗
        ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
          optVecU8Buf A ikc ikp ikl m.identityKey ∗
          optVecU8Buf A mc mp ml m.message ∗
          A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100))) ∗
      (memRegion (s0.sp - 608#64) 96 ∗ memRegion (s0.sp - 608#64 + 112#64) 184 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗ memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗ preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion (x.ret + 16#64) 232 ∗
        (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗
        memRegion (s0.sp - 608#64 - BitVec.ofNat 64 preKeyTryFromSubStack)
          (preKeyTryFromSubStack - Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom (post_bk_none_full_to_5e0_wpW hst hpc hrun hx24) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hP1⟩
  obtain ⟨hpost1, _hx29, hx28, hx27, hx26, hx25, _hx24, hx23, _hx22, _hx21, _hx20, hx19⟩ := hst1
  change s1.readReg64 .x27 = speWord 2 at hx27
  refine SepWPp.mono_pre (sepConj_mono_left hP1) ?_
  refine w8bErrW_exists_pre_frame fun kyAct => w8bErrW_exists_pre_frame fun ikAct =>
    w8bErrW_exists_pre_frame fun msgAct => ?_
  refine SepWPp.mono_pre (P' :=
      deallocSlot A kc kp kyAct ∗ (x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
        deallocSlot A ikc ikp ikAct ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ ikp) ∗
        deallocSlot A mc mp msgAct ∗ ((s0.sp - 608#64 + 96#64) ↦₆₄ mp) ∗
        A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100) ∗
        w8bBkNoneRest img s0 (s0.sp - 608#64) x.ret x.ptr kp kl bkp bkl
          ikc ikp ikl mc mp ml pReg.1.1 pReg.1.2 pOpk.1.1 pOpk.1.2 pSpk.1.1 pSpk.1.2
          pKpk.1.1 pKpk.1.2 x.bytes)
    (by unfold w8bBkNoneRest; apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind
    (entry_5e0_wpX hC kyAct ikAct msgAct hpost1 hpc1 hrun1 hx19 hx27 hx28 hx25 hx23 hx26) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, _hx19', hP2⟩
  exact SepWPp.mono_pre (Entails.trans hP2 w8bBkNone_pack)
    (w8b_errTail_close hparse hst2 hpc2 hrun2)

/-- Branch 2 (`m.identityKey = none` at `+0x57c` → `+0x61c` → `+0x504`). -/
theorem w8b_presenceErr_ik_none {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : PksmCallees img A ext)
    (x : RunCompose.PksmGhost) (s0 s1 : State) (vb : BitVec 8)
    (bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml w0 w8 : BitVec 64)
    (regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32)
    (kyberOpt msgOpt : Option (List (BitVec 8))) (bk : List (BitVec 8))
    (hparse : Pksm.pksmParse x.bytes = none)
    (hst1 : PresenceErrTailState img s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr kc kp ikc mc (spkTag.zeroExtend 64) vb s1)
    (hpc1 : s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1404#64)
    (hrun1 : s1.status = .Running) :
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) s1
      ((seg1SpillsAtW (s0.sp - 608#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) kl ikp ikl mp ml
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (s0.sp - 608#64 + 312#64) 48 ∗
        memRegion (s0.sp - 608#64 + 360#64) 72 ∗
        memRegion (s0.sp - 608#64 + 432#64) 8 ∗
        optVecU8Buf A kc kp kl kyberOpt ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗
        A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100)) ∗
      (optVecU8Buf A ikc ikp ikl none ∗
        optVecU8Buf A mc mp ml msgOpt ∗
        (x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
        memRegion (s0.sp - 608#64) 16 ∗ memRegion (s0.sp - 608#64 + 112#64) 184 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗ memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗ preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion (x.ret + 16#64) 232 ∗
        (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗
        memRegion (s0.sp - 608#64 - BitVec.ofNat 64 preKeyTryFromSubStack)
          (preKeyTryFromSubStack - Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf))
      (tryFromQp s0) := by
  rw [w8b_optVecU8Buf_none, w8b_open_ik_none]
  refine SepWPp.pure_pre fun hikc => ?_
  subst hikc
  refine SepWPp.bind_frame_tryFrom (post_ik_none_full_to_61c_wpW hst1 hpc1 hrun1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, hbk_ne, hP2⟩
  obtain ⟨hpost2, _hx29, hx28, hx27, hx26, hx25, _hx24, _hx23, _hx22, _hx21, _hx20, hx19⟩ := hst2
  change s2.readReg64 .x27 = speWord 2 at hx27
  refine SepWPp.mono_pre (sepConj_mono_left hP2) ?_
  refine w8bErrW_exists_pre_frame fun bkAct => w8bErrW_exists_pre_frame fun kyAct =>
    w8bErrW_exists_pre_frame fun msgAct => ?_
  rw [w8b_open_61c]
  refine SepWPp.bind
    (entry_61c_wpX hC bkAct kyAct msgAct hpost2 hpc2 hrun2 hx19 hx27 hx28 hx25 hx26 hbk_ne) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hst3, _hx19', hP3⟩
  exact SepWPp.mono_pre (Entails.trans hP3 w8bBkSomePres_pack_61c)
    (w8b_errTail_close hparse hst3 hpc3 hrun3)

/-- Branch 3 (`m.message = none` at `+0x590` → `+0x66c` → `+0x504`). -/
theorem w8b_presenceErr_msg_none {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : PksmCallees img A ext)
    (x : RunCompose.PksmGhost) (s0 s2 : State) (vb : BitVec 8)
    (bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml w0 w8 : BitVec 64)
    (regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32)
    (kyberOpt : Option (List (BitVec 8))) (bk ik : List (BitVec 8))
    (hparse : Pksm.pksmParse x.bytes = none)
    (hst2 : PresenceErrTailState img s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr kc kp ikc mc (spkTag.zeroExtend 64) vb s2)
    (hpc2 : s2.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1424#64)
    (hrun2 : s2.status = .Running) :
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) s2
      ((memRegion (s0.sp - 608#64 + 312#64) 48 ∗
        A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100)) ∗
      (Wire.vecU8Buf A ikc ikp ik ∗
        optVecU8Buf A mc mp ml none ∗
        optVecU8Buf A kc kp kl kyberOpt ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗
        (x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
        ((s0.sp - 608#64 + 80#64) ↦₆₄ bkPtr) ∗ ((s0.sp - 608#64 + 88#64) ↦₆₄ bkCap) ∗
        ((s0.sp - 608#64 + 96#64) ↦₆₄ mp) ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ ikp) ∗
        w8bBkSomePresRest img s0 (s0.sp - 608#64) x.ret x.ptr ml kl ikl
          (BitVec.ofNat 64 bk.length) regTag regVal opkTag opkVal spkVal kpkTag kpkVal x.bytes))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf))
      (tryFromQp s0) := by
  rw [w8b_optVecU8Buf_none, w8b_open_msg_none]
  refine SepWPp.pure_pre fun hmc => ?_
  subst hmc
  refine SepWPp.bind_frame_tryFrom (post_msg_none_full_to_66c_wpW hst2 hpc2 hrun2) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hst3, hik_ne, hbk_ne, hP3⟩
  obtain ⟨hpost3, _hx29, hx28, hx27, _hx26, hx25, _hx24, hx23, _hx22, _hx21, _hx20, hx19⟩ := hst3
  change s3.readReg64 .x27 = speWord 2 at hx27
  refine SepWPp.mono_pre (sepConj_mono_left hP3) ?_
  refine w8bErrW_exists_pre_frame fun ikAct => w8bErrW_exists_pre_frame fun bkAct =>
    w8bErrW_exists_pre_frame fun kyAct => ?_
  rw [w8b_open_66c]
  refine SepWPp.bind
    (entry_66c_wpX hC ikAct bkAct kyAct hpost3 hpc3 hrun3 hx19 hx27 hx23 hx28 hx25 hik_ne hbk_ne) ?_
  rintro s4 P4 hpc4 hrun4 ⟨hst4, _hx19', hP4⟩
  exact SepWPp.mono_pre (Entails.trans hP4 w8bBkSomePres_pack_66c)
    (w8b_errTail_close hparse hst4 hpc4 hrun4)

/-- Branch 4 (`m.message = some msg` and `m.signedPreKeyId = none` at `+0x590` → `+0x5a4` → `+0x678` → `+0x504`). -/
theorem w8b_presenceErr_spk_none {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : PksmCallees img A ext)
    (x : RunCompose.PksmGhost) (s0 s2 : State) (vb : BitVec 8)
    (bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml w0 w8 : BitVec 64)
    (regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32)
    (kyberOpt : Option (List (BitVec 8))) (bk ik msg : List (BitVec 8))
    (hparse : Pksm.pksmParse x.bytes = none)
    (hst2 : PresenceErrTailState img s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr kc kp ikc mc ((0#32 : BitVec 32).zeroExtend 64) vb s2)
    (hpc2 : s2.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1424#64)
    (hrun2 : s2.status = .Running) :
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) s2
      ((memRegion (s0.sp - 608#64 + 312#64) 48 ∗
        A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100)) ∗
      (Wire.vecU8Buf A ikc ikp ik ∗
        optVecU8Buf A mc mp ml (some msg) ∗
        optVecU8Buf A kc kp kl kyberOpt ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗
        (x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
        ((s0.sp - 608#64 + 80#64) ↦₆₄ bkPtr) ∗ ((s0.sp - 608#64 + 88#64) ↦₆₄ bkCap) ∗
        ((s0.sp - 608#64 + 96#64) ↦₆₄ mp) ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ ikp) ∗
        w8bBkSomePresRest img s0 (s0.sp - 608#64) x.ret x.ptr ml kl ikl
          (BitVec.ofNat 64 bk.length) regTag regVal opkTag opkVal spkVal kpkTag kpkVal x.bytes))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf))
      (tryFromQp s0) := by
  have hmsg_buf : optVecU8Buf A mc mp ml (some msg) ⊢
      ⌜mc.toNat < 2 ^ 63⌝ ∗ Wire.vecU8Buf A mc mp msg := by
    dsimp only [optVecU8Buf]
    refine Entails.pure_left fun _ => ?_
    refine Entails.trans (vecU8Buf_cap_lt_len A mc mp msg) (Entails.pure_left fun ⟨_, hlt, _⟩ => ?_)
    rw [pure_true_emp hlt, emp_sepConj]; exact Entails.refl _
  refine SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmsg_buf))) ?_
  rw [w8b_open_msg_some]
  refine SepWPp.pure_pre fun hmsg_lt => ?_
  refine SepWPp.bind_frame_tryFrom (post_msg_some_to_5a4_wpW hC.dropSpe hst2 hpc2 hrun2 hmsg_lt) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hst3, hP3⟩
  refine SepWPp.mono_pre (sepConj_mono_left hP3) ?_
  rw [w8b_open_spk_none]
  refine SepWPp.bind_frame_tryFrom (post_spk_none_full_to_678_wpW hst3 hpc3 hrun3) ?_
  rintro s4 P4 hpc4 hrun4 ⟨hst4, hmsg_ne, hik_ne, hbk_ne, hP4⟩
  obtain ⟨hpost4, _hx29, hx28, hx27, hx26, hx25, _hx24, hx23, _hx22, _hx21, _hx20, hx19⟩ := hst4
  change s4.readReg64 .x27 = speWord 2 at hx27
  refine SepWPp.mono_pre (sepConj_mono_left hP4) ?_
  refine w8bErrW_exists_pre_frame fun msgAct => w8bErrW_exists_pre_frame fun ikAct =>
    w8bErrW_exists_pre_frame fun bkAct => w8bErrW_exists_pre_frame fun kyAct => ?_
  rw [w8b_open_678]
  refine SepWPp.bind
    (entry_678_wpX hC msgAct ikAct bkAct kyAct hpost4 hpc4 hrun4 hx19 hx27 hx26 hx23 hx28 hx25
      hmsg_ne hik_ne hbk_ne) ?_
  rintro s5 P5 hpc5 hrun5 ⟨hst5, _hx19', hP5⟩
  exact SepWPp.mono_pre (Entails.trans hP5 w8bBkSomePres_pack)
    (w8b_errTail_close hparse hst5 hpc5 hrun5)

/-- Continuation from `+0x57c` (`1404`) when `m.baseKey = some bk` and
`m.identityKey = none ∨ m.message = none ∨ m.signedPreKeyId = none`. -/
theorem w8b_presenceErr_after_57c {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : PksmCallees img A ext)
    (x : RunCompose.PksmGhost) (s0 s1 : State) (vb : BitVec 8)
    (bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml w0 w8 : BitVec 64)
    (regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32)
    (kyberOpt ikOpt msgOpt : Option (List (BitVec 8))) (spkOpt : Option (BitVec 32))
    (bk : List (BitVec 8))
    (hparse : Pksm.pksmParse x.bytes = none)
    (hspkCells : w8bOptU32Cells spkOpt (spkTag, spkVal))
    (herr : ikOpt = none ∨ msgOpt = none ∨ spkOpt = none)
    (hst1 : PresenceErrTailState img s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr kc kp ikc mc (spkTag.zeroExtend 64) vb s1)
    (hpc1 : s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1404#64)
    (hrun1 : s1.status = .Running) :
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) s1
      ((seg1SpillsAtW (s0.sp - 608#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) kl ikp ikl mp ml
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (s0.sp - 608#64 + 312#64) 48 ∗
        memRegion (s0.sp - 608#64 + 360#64) 72 ∗
        memRegion (s0.sp - 608#64 + 432#64) 8 ∗
        optVecU8Buf A kc kp kl kyberOpt ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗
        A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100)) ∗
      (optVecU8Buf A ikc ikp ikl ikOpt ∗
        optVecU8Buf A mc mp ml msgOpt ∗
        (x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
        memRegion (s0.sp - 608#64) 16 ∗ memRegion (s0.sp - 608#64 + 112#64) 184 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗ memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗ preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion (x.ret + 16#64) 232 ∗
        (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗
        memRegion (s0.sp - 608#64 - BitVec.ofNat 64 preKeyTryFromSubStack)
          (preKeyTryFromSubStack - Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf))
      (tryFromQp s0) := by
  rcases hikO : ikOpt with _ | ik
  · exact w8b_presenceErr_ik_none hC x s0 s1 vb bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml
      w0 w8 regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal kyberOpt msgOpt bk
      hparse hst1 hpc1 hrun1
  · have hik_buf : optVecU8Buf A ikc ikp ikl (some ik) ⊢
        ⌜ikc.toNat < 2 ^ 63⌝ ∗ Wire.vecU8Buf A ikc ikp ik := by
      dsimp only [optVecU8Buf]
      refine Entails.pure_left fun _ => ?_
      refine Entails.trans (vecU8Buf_cap_lt_len A ikc ikp ik) (Entails.pure_left fun ⟨_, hlt, _⟩ => ?_)
      rw [pure_true_emp hlt, emp_sepConj]; exact Entails.refl _
    refine SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_left hik_buf)) ?_
    rw [w8b_open_ik_some]
    refine SepWPp.pure_pre fun hik_lt => ?_
    refine SepWPp.bind_frame_tryFrom (post_ik_some_to_590_wpW hC.dropSpe hst1 hpc1 hrun1 hik_lt) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hst2, hP2⟩
    refine SepWPp.mono_pre (sepConj_mono_left hP2) ?_
    rcases hmsgO : msgOpt with _ | msg
    · exact w8b_presenceErr_msg_none hC x s0 s2 vb bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml
        w0 w8 regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal kyberOpt bk ik
        hparse hst2 hpc2 hrun2
    · have hspkO : spkOpt = none := by
        rcases herr with h | h | h
        · simp [hikO] at h
        · simp [hmsgO] at h
        · exact h
      subst hspkO
      have hspk0 : spkTag = 0#32 := hspkCells
      subst hspk0
      exact w8b_presenceErr_spk_none hC x s0 s2 vb bkCap bkPtr kc kp kl ikc ikp ikl
        mc mp ml w0 w8 regTag regVal opkTag opkVal spkVal kpkTag kpkVal kyberOpt bk ik msg
        hparse hst2 hpc2 hrun2

/-- `PreKeyPresenceErrW` from presence bridges + ErrTailB + `w8b_errTail_close`. -/
theorem preKeyPresenceErrW_proof {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : PksmCallees img A ext) :
    PreKeyPresenceErrW img A ext := by
  intro x s0 s vb b1 bs1 m hcons _hv3 _hv4 _hlen hdec herr hst hpc hrun hx24
  have hparse : Pksm.pksmParse x.bytes = none := by
    rw [hcons]
    rcases herr with h | h | h | h
    · exact pksmParse_bkNone hdec h
    · exact pksmParse_ikNone hdec h
    · exact pksmParse_msgNone hdec h
    · exact pksmParse_spkNone hdec h
  rcases hbkO : m.baseKey with _ | bk
  · exact w8b_presenceErr_bk_none hC x s0 s vb m hparse hbkO hst hpc hrun hx24
  · have herr' : m.identityKey = none ∨ m.message = none ∨ m.signedPreKeyId = none := by
      rcases herr with h | h
      · simp [hbkO] at h
      · exact h
    rw [w8bMemRegion296_split_16_96, w8bMemRegion248_eq_words2 x.ret,
      stackAt_preKeyTryFromSubStack_skipField]
    unfold wirePreKeyOf
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre fun g => ?_
    rw [w8b_wirePreKeyAt_bk_some_eq A g _ m hbkO]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      BitVec.add_assoc, BitVec.reduceAdd]
    refine SepWPp.exists_pre fun w8 => SepWPp.exists_pre fun w0 => ?_
    refine SepWPp.mono_pre
      (sepConj_mono (Wire.optVecU8At_entails_header_buf A g.kyberCt _ m.kyberCiphertext)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono
          (Wire.optVecU8At_entails_header_buf A g.identityKey _ m.identityKey)
          (sepConj_mono (Wire.optVecU8At_entails_header_buf A g.message _ m.message)
            (sepConj_mono (w8b_optU32At_entails _ m.registrationId)
              (sepConj_mono (w8b_optU32At_entails _ m.preKeyId)
                (sepConj_mono (w8b_optU32At_entails _ m.signedPreKeyId)
                  (sepConj_mono_left (w8b_optU32At_entails _ m.kyberPreKeyId)))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      BitVec.add_assoc, BitVec.reduceAdd]
    refine SepWPp.exists_pre fun pKpk => SepWPp.exists_pre fun pSpk =>
      SepWPp.exists_pre fun pOpk => SepWPp.exists_pre fun pReg =>
      SepWPp.exists_pre fun mc => SepWPp.exists_pre fun mp => SepWPp.exists_pre fun ml =>
      SepWPp.exists_pre fun ikc => SepWPp.exists_pre fun ikp => SepWPp.exists_pre fun ikl =>
      SepWPp.exists_pre fun kc => SepWPp.exists_pre fun kp => SepWPp.exists_pre fun kl => ?_
    refine SepWPp.mono_pre (P' :=
        (memRegion (s0.sp - 608#64 + 16#64) 96 ∗
          vecHeader (s0.sp - 608#64 + 312#64) kc kp kl ∗
          optVecU8Buf A kc kp kl m.kyberCiphertext ∗
          vecHeader (s0.sp - 608#64 + 336#64) g.baseKey.cap g.baseKey.ptr (BitVec.ofNat 64 bk.length) ∗
          Wire.vecU8Buf A g.baseKey.cap g.baseKey.ptr bk ∗
          vecHeader (s0.sp - 608#64 + 360#64) ikc ikp ikl ∗
          vecHeader (s0.sp - 608#64 + 384#64) mc mp ml ∗
          ((s0.sp - 608#64 + 408#64) ↦₃₂ pReg.1.1) ∗ ((s0.sp - 608#64 + 412#64) ↦₃₂ pReg.1.2) ∗
          ((s0.sp - 608#64 + 416#64) ↦₃₂ pOpk.1.1) ∗ ((s0.sp - 608#64 + 420#64) ↦₃₂ pOpk.1.2) ∗
          ((s0.sp - 608#64 + 424#64) ↦₃₂ pSpk.1.1) ∗ ((s0.sp - 608#64 + 428#64) ↦₃₂ pSpk.1.2) ∗
          ((s0.sp - 608#64 + 432#64) ↦₃₂ pKpk.1.1) ∗ ((s0.sp - 608#64 + 436#64) ↦₃₂ pKpk.1.2) ∗
          A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100)) ∗
        (optVecU8Buf A ikc ikp ikl m.identityKey ∗
          optVecU8Buf A mc mp ml m.message ∗
          (x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
          memRegion (s0.sp - 608#64) 16 ∗ memRegion (s0.sp - 608#64 + 112#64) 184 ∗
          memRegion (s0.sp - 608#64 + 296#64) 16 ∗ memRegion (s0.sp - 608#64 + 440#64) 8 ∗
          memRegion (s0.sp - 608#64 + 448#64) 64 ∗ preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
          memRegion (x.ret + 16#64) 232 ∗
          (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗
          memRegion (s0.sp - 608#64 - BitVec.ofNat 64 preKeyTryFromSubStack)
            (preKeyTryFromSubStack - Prost.skipFieldStackX 100)))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_tryFrom (post_bk_some_to_57c_wpW hC.dropSpe hst hpc hrun hx24) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hP1⟩
    exact SepWPp.mono_pre (sepConj_mono_left hP1)
      (w8b_presenceErr_after_57c hC x s0 s1 vb g.baseKey.cap g.baseKey.ptr
        kc kp kl ikc ikp ikl mc mp ml w0 w8
        pReg.1.1 pReg.1.2 pOpk.1.1 pOpk.1.2 pSpk.1.1 pSpk.1.2 pKpk.1.1 pKpk.1.2
        m.kyberCiphertext m.identityKey m.message m.signedPreKeyId bk hparse pSpk.2 herr'
        hst1 hpc1 hrun1)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
