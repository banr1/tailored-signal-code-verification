/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedPlacedCommon
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Call-Step Helpers for `encode_repeated`

Provides `RustCliAllocBudget`-threaded call steppers under `EncRepeatedCalleeSavedPlaced`
for `memcpy`, `encode_varint`, and `do_reserve_and_handle`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedPlacedCommonBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall reserveCap sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open CryptoVerification.SpqrV1.Varint
  (stackAt_encodeVarint_eq_doReserve sp_sub_80_aligned
   EncRepeatedCalleeSavedPlaced withEncRepeatedCSPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintEvents EncodeVarintEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
  (sepWPp_call_cs_placed_noPanic encodeVarintSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserveSpecOf doReserve2SpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (pushBytesStep pushBytesStep_snd_eq)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeVarintDetSpecOf)

theorem step_memcpy_call_gen_placed {prog : Program} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64}
    (hmemcpy : subroutine_ok prog call_pc sessionMemcpyRegionBudgetSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8)) (curSt : M.σ)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ A.pool lim curSt s) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim curSt sm) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (dst, src, bs)) (F := A.pool lim curSt s ∗ F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      memcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    rw [← A.pool_of_vmPreserved hvm]
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm' hcsm
        (hcs.trans (EncRepeatedCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hvm)
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_encode_varint_det_call_gen_placed {resStack : Nat} {prog : Program}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc
      (withEncRepeatedCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1 →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 80#64) (0x30 + resStack)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine sepWPp_call_cs_placed_noPanic
    (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, curSt)) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withEncRepeatedCSPlaced, encodeVarintDetSpecOf, encodeVarintFitSpecOf, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withEncRepeatedCSPlaced, encodeVarintDetSpecOf]
    rw [hsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun evs => ?_
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    refine SepWPp.weaken_pre (P' :=
      ⌜sm.trace = s.trace⌝ ∗
      ⌜curCap.toNat ≤ nextCap.toNat ∧
        (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
          nextCap = curCap ∧ nextPtr = curPtr) ∧
        nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1⌝ ∗
      ⌜EncodeVarintEnv (EncodeVarintGhost.mk val v curCap curPtr curBs) evs⌝ ∗
      ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
        A.pool lim (M.stepEvents evs curSt) sm ∗
        stackAt (sp - 80#64) (0x30 + resStack)) ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun htrm =>
      SepWPp.pure_elim fun ⟨hge, hpres, hcap_det⟩ =>
      SepWPp.pure_elim fun hev => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hev_eq : evs = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).2 := by
      rw [hev, encodeVarintEvents, pushBytesStep_snd_eq]
    rw [hev_eq]
    exact hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
      (hcs.trans (EncRepeatedCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
      hge hpres hcap_det

theorem step_encode_varint_call_gen_placed {resStack : Nat} {prog : Program}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc
      (withEncRepeatedCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 80#64) (0x30 + resStack)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine sepWPp_call_cs_placed_noPanic
    (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, curSt)) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withEncRepeatedCSPlaced, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withEncRepeatedCSPlaced, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun evs => ?_
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    refine SepWPp.weaken_pre (P' :=
      ⌜sm.trace = s.trace⌝ ∗
      ⌜curCap.toNat ≤ nextCap.toNat ∧
        (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
          nextCap = curCap ∧ nextPtr = curPtr)⌝ ∗
      ⌜EncodeVarintEnv (EncodeVarintGhost.mk val v curCap curPtr curBs) evs⌝ ∗
      ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
        A.pool lim (M.stepEvents evs curSt) sm ∗
        stackAt (sp - 80#64) (0x30 + resStack)) ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun htrm =>
      SepWPp.pure_elim fun ⟨hge, hpres⟩ =>
      SepWPp.pure_elim fun hev => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hev_eq : evs = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).2 := by
      rw [hev, encodeVarintEvents, pushBytesStep_snd_eq]
    rw [hev_eq]
    exact hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
      (hcs.trans (EncRepeatedCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hge hpres

theorem step_do_reserve2_call_gen_placed {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat) (curSt : M.σ)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim curSt
      (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) curSt) sm ∗
          stackAt (sp - 80#64) (0x30 + resStack)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs additional, curSt))
    (F := memRegion (sp - 80#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve hres (sp - 80#64)] at hm
    simp only [withEncRepeatedCSPlaced, doReserve2SpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hbound, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withEncRepeatedCSPlaced, doReserve2SpecOf, doReserveSpecOf]
    rw [hsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun newPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (EncRepeatedCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve hres (sp - 80#64)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_do_reserve7_call_gen_placed {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withEncRepeatedCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat) (curSt : M.σ)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim curSt
      (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) curSt) sm ∗
          stackAt (sp - 80#64) (0x30 + resStack)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs additional, curSt))
    (F := memRegion (sp - 80#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve hres (sp - 80#64)] at hm
    simp only [withEncRepeatedCSPlaced, doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withEncRepeatedCSPlaced, doReserveSpecOf]
    rw [hsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun newPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (EncRepeatedCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve hres (sp - 80#64)]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedPlacedCommonBudget
