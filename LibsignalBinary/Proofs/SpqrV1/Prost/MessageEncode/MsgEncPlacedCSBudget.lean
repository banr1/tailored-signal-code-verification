/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Call Helpers for 48-Byte `message::encode`

Provides polymorphic-outcome (`Q`, `Qp`, `oom`) budget-threaded call and tailcall steppers under
`MsgEnc48CalleeSavedPlaced` for `encode_varint`, `do_reserve_and_handle` (`[local#2, 7]`), and
`encode_repeated`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost sp_sub_48_aligned)
open CryptoVerification.SpqrV1.Auth (stackAt_encodeVarint_eq_doReserve64)
open CryptoVerification.SpqrV1.Varint
  (EncodeRepeatedGhost encodeRepeatedBytes encodeRepeatedStackOf repeatedBytesSliceAt)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (MsgEnc48CalleeSavedPlaced msgEnc48RepeatedStackOf msgEnc48SavedFrame msgEnc48VarintStackOf
   stackAt_msgEnc48_repeated_eq_bottom stackAt_msgEnc48_repeated_recombine
   stackAt_msgEnc48_varint_eq_bottom stackAt_msgEnc48_varint_recombine
   withMsgEnc48CSPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (EncodeVarintEnv encodeVarintEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
  (encodeVarintSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserve2SpecOf doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
  (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (EncodeRepeatedEnv encodeRepeated59DetSpecOf encodeRepeatedEvents encodeRepeatedSpecOf
   encodeVarintDetSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (encodeRepeatedStep pushBytesStep sepWPp_call_cs_placed_noPanic)

theorem step_msg48_encode_varint_call_placed {resStack : Nat} {prog : Program}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) curSt) sm ∗
          stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, curSt)) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withMsgEnc48CSPlaced, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs) := hev
    subst hev_eq
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)

theorem step_msg48_do_reserve2_call_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat) (curSt : M.σ)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) curSt) sm ∗
          stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs additional, curSt))
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP, stackAt_encodeVarint_eq_doReserve64 hres (sp - 48#64)] at hm
    simp only [withMsgEnc48CSPlaced, doReserve2SpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hbound, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, doReserve2SpecOf, doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve64 hres (sp - 48#64)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_msg48_do_reserve7_call_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A lim)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat) (curSt : M.σ)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) curSt) sm ∗
          stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs additional, curSt))
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP, stackAt_encodeVarint_eq_doReserve64 hres (sp - 48#64)] at hm
    simp only [withMsgEnc48CSPlaced, doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve64 hres (sp - 48#64)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_msg48_encode_varint_tailcall_placed {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (val v curCap curPtr sp fp lr r21 v3 r20 r19 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcc : CalleeSavedPreserved s0 s) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (0x30 + resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      Q sf ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
        A.pool lim (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) curSt) sf ∗
        stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact halign
  refine sepWPp_call_cs_placed_noPanic (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, curSt))
    (F := memRegion (sp - BitVec.ofNat 64 (msgEnc48VarintStackOf resStack)) 48 ∗ F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    have hm0 : s.mem ⊨ (stackAt (sp - 48#64) (0x30 + resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗
        (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ F ∗ R') := by
      rw [hP] at hm; convert hm using 1; sep_ac_rfl
    have hm1 : s.mem ⊨ stackAt sp (msgEnc48VarintStackOf resStack) ∗
        (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ F ∗ R') :=
      Satisfies.mono (sepConj_mono_left (stackAt_msgEnc48_varint_recombine hres sp fp lr r21 v3 r20 r19)) hm0
    rw [stackAt_msgEnc48_varint_eq_bottom hres sp] at hm1
    simp only [withMsgEnc48CSPlaced, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm1 using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs) := hev
    subst hev_eq
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hccm : CalleeSavedPreserved s0 sm := by
      rcases hcc with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
      rcases hcsm with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
      exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22, h23'.trans h23,
        h24'.trans h24, h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28,
        hfp'.trans hfp, hv'.trans hv⟩
    refine SepWPp.weaken_pre ?_
      (SepWPp.done hpcm hrunm
        (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hccm
          (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hge hpres))
    rw [stackAt_msgEnc48_varint_eq_bottom hres sp]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_msg48_encode_varint_det_call_placed {resStack : Nat} {prog : Program}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1 →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) curSt) sm ∗
          stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, curSt)) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withMsgEnc48CSPlaced, encodeVarintDetSpecOf, encodeVarintFitSpecOf,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeVarintDetSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres, hcap_eq⟩ => ?_
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs) := hev
    subst hev_eq
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
        hge hpres hcap_eq)

theorem step_msg48_encode_varint_det_tailcall_placed {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (val v curCap curPtr sp fp lr r21 v3 r20 r19 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcc : CalleeSavedPreserved s0 s) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (0x30 + resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1 →
      Q sf ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
        A.pool lim (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) curSt) sf ∗
        stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact halign
  refine sepWPp_call_cs_placed_noPanic (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, curSt))
    (F := memRegion (sp - BitVec.ofNat 64 (msgEnc48VarintStackOf resStack)) 48 ∗ F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    have hm0 : s.mem ⊨ (stackAt (sp - 48#64) (0x30 + resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗
        (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ F ∗ R') := by
      rw [hP] at hm; convert hm using 1; sep_ac_rfl
    have hm1 : s.mem ⊨ stackAt sp (msgEnc48VarintStackOf resStack) ∗
        (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ F ∗ R') :=
      Satisfies.mono (sepConj_mono_left (stackAt_msgEnc48_varint_recombine hres sp fp lr r21 v3 r20 r19)) hm0
    rw [stackAt_msgEnc48_varint_eq_bottom hres sp] at hm1
    simp only [withMsgEnc48CSPlaced, encodeVarintDetSpecOf, encodeVarintFitSpecOf,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm1 using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeVarintDetSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres, hcap_eq⟩ => ?_
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs) := hev
    subst hev_eq
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hccm : CalleeSavedPreserved s0 sm := by
      rcases hcc with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
      rcases hcsm with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
      exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22, h23'.trans h23,
        h24'.trans h24, h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28,
        hfp'.trans hfp, hv'.trans hv⟩
    refine SepWPp.weaken_pre ?_
      (SepWPp.done hpcm hrunm
        (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hccm
          (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
          hge hpres hcap_eq))
    rw [stackAt_msgEnc48_varint_eq_bottom hres sp]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_msg48_encode_repeated_call_placed {resStack : Nat} {prog : Program}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A lim)))
    (tag : Nat) (base v curCap curPtr sp ret_pc : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29) (helems : elems.length < 2 ^ 58)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag) (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length) (hx3 : s.readReg64 .x3 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).1 →
      SepWPp prog ret sm
        ((repeatedBytesSliceAt base elems ∗
          vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool lim (M.stepEvents (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)) curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine sepWPp_call_cs_placed_noPanic
    (x := (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs, curSt)) (F := F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withMsgEnc48CSPlaced, encodeRepeatedSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeRepeatedSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres, hcap_eq⟩ => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs) := hev
    subst hev_eq
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
        hge hpres hcap_eq)

theorem step_msg48_encode_repeated_tailcall_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A lim)))
    (tag : Nat) (base v curCap curPtr sp fp lr r21 v3 r20 r19 : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29) (helems : elems.length < 2 ^ 58)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag) (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length) (hx3 : s.readReg64 .x3 = v)
    (hcc : CalleeSavedPreserved s0 s) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).1 →
      Q sf ((repeatedBytesSliceAt base elems ∗
        vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
        A.pool lim (M.stepEvents (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)) curSt) sf ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact halign
  refine sepWPp_call_cs_placed_noPanic
    (x := (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs, curSt))
    (F := memRegion (sp - BitVec.ofNat 64 (msgEnc48RepeatedStackOf resStack)) 48 ∗ F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    have hm0 : s.mem ⊨ (stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ F ∗ R') := by
      rw [hP] at hm; convert hm using 1; sep_ac_rfl
    have hm1 : s.mem ⊨ stackAt sp (msgEnc48RepeatedStackOf resStack) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ F ∗ R') :=
      Satisfies.mono (sepConj_mono_left (stackAt_msgEnc48_repeated_recombine hres sp fp lr r21 v3 r20 r19)) hm0
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp] at hm1
    simp only [withMsgEnc48CSPlaced, encodeRepeatedSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm1 using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeRepeatedSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres, hcap_eq⟩ => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs) := hev
    subst hev_eq
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hccm : CalleeSavedPreserved s0 sm := by
      rcases hcc with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
      rcases hcsm with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
      exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22, h23'.trans h23,
        h24'.trans h24, h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28,
        hfp'.trans hfp, hv'.trans hv⟩
    refine SepWPp.weaken_pre ?_
      (SepWPp.done hpcm hrunm
        (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hccm
          (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
          hge hpres hcap_eq))
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_msg48_encode_repeated59_det_call_placed {resStack : Nat} {prog : Program}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeRepeated59DetSpecOf resStack A lim)))
    (tag : Nat) (base v curCap curPtr sp ret_pc : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29) (helems : elems.length < 2 ^ 59)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag) (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length) (hx3 : s.readReg64 .x3 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).1 →
      SepWPp prog ret sm
        ((repeatedBytesSliceAt base elems ∗
          vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool lim (M.stepEvents (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)) curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine sepWPp_call_cs_placed_noPanic
    (x := (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs, curSt)) (F := F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withMsgEnc48CSPlaced, encodeRepeated59DetSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeRepeated59DetSpecOf, encodeRepeatedSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres, hcap_eq⟩ => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs) := hev
    subst hev_eq
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
        hge hpres hcap_eq)

theorem step_msg48_encode_repeated59_det_tailcall_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeRepeated59DetSpecOf resStack A lim)))
    (tag : Nat) (base v curCap curPtr sp fp lr r21 v3 r20 r19 : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29) (helems : elems.length < 2 ^ 59)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag) (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length) (hx3 : s.readReg64 .x3 = v)
    (hcc : CalleeSavedPreserved s0 s) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).1 →
      Q sf ((repeatedBytesSliceAt base elems ∗
        vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
        A.pool lim (M.stepEvents (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)) curSt) sf ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact halign
  refine sepWPp_call_cs_placed_noPanic
    (x := (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs, curSt))
    (F := memRegion (sp - BitVec.ofNat 64 (msgEnc48RepeatedStackOf resStack)) 48 ∗ F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    have hm0 : s.mem ⊨ (stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ F ∗ R') := by
      rw [hP] at hm; convert hm using 1; sep_ac_rfl
    have hm1 : s.mem ⊨ stackAt sp (msgEnc48RepeatedStackOf resStack) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ F ∗ R') :=
      Satisfies.mono (sepConj_mono_left (stackAt_msgEnc48_repeated_recombine hres sp fp lr r21 v3 r20 r19)) hm0
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp] at hm1
    simp only [withMsgEnc48CSPlaced, encodeRepeated59DetSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm1 using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeRepeated59DetSpecOf, encodeRepeatedSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres, hcap_eq⟩ => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs) := hev
    subst hev_eq
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hccm : CalleeSavedPreserved s0 sm := by
      rcases hcc with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
      rcases hcsm with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
      exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22, h23'.trans h23,
        h24'.trans h24, h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28,
        hfp'.trans hfp, hv'.trans hv⟩
    refine SepWPp.weaken_pre ?_
      (SepWPp.done hpcm hrunm
        (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hccm
          (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
          hge hpres hcap_eq))
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
