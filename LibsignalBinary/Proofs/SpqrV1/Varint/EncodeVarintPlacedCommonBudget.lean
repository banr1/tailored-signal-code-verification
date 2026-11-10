/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded `[LibsignalPlacement]` `do_reserve_and_handle` Call Helpers

Provides stack-parametric budget specifications (`doReserveSpecOf`, `doReserve2SpecOf`)
and `EncVarintCalleeSavedPlaced` call steppers advancing `pushByteStep`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget)
open CryptoVerification
  (LibsignalPlacement LibsignalCodeLoaded lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap
  (vecU8At vecHeader)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall reserveCap doReserveStack doReserveStackX)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (vecU8Buf vecU8At_eq_header_sep_buf sp_sub_48_aligned reserveCap_bounds EncVarintCalleeSavedPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveEvents DoReserveEnv fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (pushByteStep)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
  (pushByteStep_of_eq sepWPp_call_cs_placed_noPanic doReserveSpecWithPlaced)

/-- Stack-parametric budget specification of `do_reserve_and_handle` (`align = 1, elem_size = 1`
passed in `x3, x4`). -/
def doReserveSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      newCap + 1 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp resStack
  post := fun (x, st) s0' sf =>
    ⌜sf.trace = s0'.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      vecU8At A.repAlloc x.v (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)) p' x.bs) ∗
    A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗ stackAt s0'.sp resStack

theorem doReserve7_with_placed_of_ok [LibsignalPlacement] {prog : Program} {target : BitVec 64}
    {resStack : Nat} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h : subroutine_ok prog target (withLsCodeLoaded lsmpl (doReserveSpecOf resStack A lim))) :
    subroutine_ok prog target (doReserveSpecWithPlaced resStack s0 A lim) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWithPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine (h.to_outcome x R s hpc hrun ?_ hsp).mono_outcome fun _ hout => hout
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcl0.of_keepsFrozen hpre.1.1.2.2.2.2.2.2.2.2.2.2, ?_⟩
  simp only [doReserveSpecOf, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre.1.2, hpre.2⟩

theorem step_doReserve_call_gen_placed {prog : Program} {resTarget : BitVec 64} {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {s0 s : State}
    (hdoReserve : subroutine_ok prog resTarget (doReserveSpecWithPlaced resStack s0 A lim))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hcap_eq : curCap.toNat = curBs.length) (hlen_lt : curBs.length < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = resTarget) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64) (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs_s : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      EncVarintCalleeSavedPlaced s0 sm → curBs.length < newCap.toNat → curCap.toNat ≤ newCap.toNat →
      newCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp prog ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc newCap p' curBs ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget.step_doReserve_call_gen_placed
    A lim hdoReserve v curCap curPtr sp ret_pc curBs curSt hcap_eq hlen_lt hfits
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hx3 hx4 hcs_s hP hnext

/-- Stack-parametric budget specification of `do_reserve_and_handle [local#2]`, which hardcodes
`align = 1, elem_size = 1` and does not read `x3` or `x4`. -/
def doReserve2SpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      newCap + 1 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp resStack
  post := (doReserveSpecOf resStack A lim).post

def doReserve2Spec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) :=
  doReserve2SpecOf doReserveStack A lim

def doReserve2SpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) :=
  doReserve2SpecOf doReserveStackX A lim

def doReserve2SpecWithPlaced (resStack : Nat) (s0 : State) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜EncVarintCalleeSavedPlaced s0 s ∧ s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp resStack
  post := (doReserve2SpecOf resStack A lim).post

theorem doReserve2_with_placed_of_ok [LibsignalPlacement] {prog : Program} {target : BitVec 64}
    {resStack : Nat} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h : subroutine_ok prog target (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A lim))) :
    subroutine_ok prog target (doReserve2SpecWithPlaced resStack s0 A lim) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  simp only [doReserve2SpecWithPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine (h.to_outcome x R s hpc hrun ?_ hsp).mono_outcome fun _ hout => hout
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcl0.of_keepsFrozen hpre.1.1.2.2.2.2.2.2.2.2.2.2, ?_⟩
  simp only [doReserve2SpecOf, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre.1.2, hpre.2⟩

theorem step_doReserve2_call_gen_placed {prog : Program} {resTarget : BitVec 64} {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {s0 s : State}
    (hdoReserve : subroutine_ok prog resTarget (doReserve2SpecWithPlaced resStack s0 A lim))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hcap_eq : curCap.toNat = curBs.length) (hlen_lt : curBs.length < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = resTarget) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64) (hcs_s : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      EncVarintCalleeSavedPlaced s0 sm → curBs.length < newCap.toNat → curCap.toNat ≤ newCap.toNat →
      newCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp prog ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc newCap p' curBs ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  obtain ⟨hres_bound, hnew_gt, hnew_ge⟩ := reserveCap_bounds hlen_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  have hstep_eq := pushByteStep_of_eq v curCap curPtr curBs hcap_eq
  refine sepWPp_call_cs_placed_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs 1, curSt)) (F := F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [doReserve2SpecWithPlaced, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hcs_s, hx0, hx1_toNat, hx2_toNat, ?_, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [doReserve2SpecWithPlaced, doReserve2SpecOf, doReserveSpecOf,
      vecU8At_eq_header_sep_buf, vecHeader, hsp, hcap_eq,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hnew_ge' : curCap.toNat ≤ (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)).toNat := by
      rw [hcap_eq]; exact hnew_ge
    have hnew_toNat :
        (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)).toNat =
          (pushByteStep curCap.toNat curBs.length).1 := by
      rw [hstep_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hstep_evs : (pushByteStep curCap.toNat curBs.length).2 =
        doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1) := by
      rw [hstep_eq]
    rw [← hstep_evs]
    refine SepWPp.weaken_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p'
      hpcm hrunm hspm htrm' hcsm.1 hcsm.2.1
      (hcs_s.trans (EncVarintCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
      hnew_gt hnew_ge' hnew_toNat)
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
