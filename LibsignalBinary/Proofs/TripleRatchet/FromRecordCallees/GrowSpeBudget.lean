/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.FromRecordCalleesCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Contracts for `RawVec::grow_one` (Blocks `42` & `43`)

Verifies `<RawVec<SignalProtocolError>>::grow_one` (block `42`, stride `48`) and
`<RawVec<Chain>>::grow_one` (block `43`, stride `104`) under `[LibsignalPlacement]` over
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement
  blkPC_42 blkPl_42 blkLib_eq_42
  blkPC_43 blkPl_43 blkLib_eq_43
  blkPC_45 blkPl_45
  lsRustAllocSym lsRustNoAllocShimSym lsRustReallocSym
  lsmpl subroutine_ok_withLsCodeLoaded_of_plain ls_subroutine_ok_of_block withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalSession (GrowGhost)
open CryptoVerification.LibsignalTripleRatchet (
  FinishGrowCall extHookStack finishGrowStack finishGrowStackX
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustReallocEvents
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  rustCliReallocBudgetSpec rustCliReallocNoOomSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecGrowEvents rawVecNewCap)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  FinishGrowEnv finishGrowEvents finishGrowSpec finishGrowSpecX noAllocShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrowBudget (
  finish_grow_placed_ok finish_grow_placed_ok_noOom
  finish_grow_placed_ok_x finish_grow_placed_ok_x_noOom
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv growOneSpeEnv_events growOneSpeEvents growOneSpeSpec
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Shared Stack Splits and Arithmetic Helpers -/

private def growPad (sp : BitVec 64) : SepProp :=
  memRegion (sp - 4608#64) 400

private theorem stackAt_grow_one_spe (sp : BitVec 64) :
    stackAt sp growOneSpeStack =
      growPad sp ∗
      (stackAt (sp - 64#64) finishGrowStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7))) := by
  have h1 := stackAt_split_bottom sp 4208 400 (by decide)
  have h2 := stackAt_split_cells sp 4144 8 (by decide)
  change stackAt sp growOneSpeStack = growPad sp ∗ stackAt sp 4208 at h1
  change stackAt sp 4208 = stackAt (sp - 64#64) finishGrowStack ∗ cells (sp - 64#64) 8 at h2
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, hc8]

private def growPadX (sp : BitVec 64) : SepProp :=
  memRegion (sp - 16896#64) 400

private theorem stackAt_grow_one_104_x (sp : BitVec 64) :
    stackAt sp (464 + finishGrowStackX) =
      growPadX sp ∗
      (stackAt (sp - 64#64) finishGrowStackX ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7))) := by
  have h1 := stackAt_split_bottom sp 16496 400 (by decide)
  have h2 := stackAt_split_cells sp 16432 8 (by decide)
  change stackAt sp (464 + finishGrowStackX) = growPadX sp ∗ stackAt sp 16496 at h1
  change stackAt sp 16496 = stackAt (sp - 64#64) finishGrowStackX ∗ cells (sp - 64#64) 8 at h2
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, hc8]

private theorem grow_new_cap_eq {stride : Nat} {cap : BitVec 64}
    (hpos : 0 < stride)
    (h : max (2 * cap.toNat) 4 * stride + 8 ≤ 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have h2cap_lt : 2 * cap.toNat < 2 ^ 64 := by
    have : 2 * cap.toNat ≤ max (2 * cap.toNat) 4 * stride :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_mul_of_pos_right _ hpos)
    omega
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    have hlt : 4 < 2 * cap.toNat := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
      exact hc
    omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hle : ¬ 4 < 2 * cap.toNat := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
      exact hc
    change 4 = max (2 * cap.toNat) 4
    omega

private theorem memRegion_24_cells3 (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ o2 : BitVec 64, ∃∗ o1 : BitVec 64, ∃∗ o0 : BitVec 64,
        (a ↦₆₄ o0) ∗ ((a + 8#64) ↦₆₄ o1) ∗ ((a + 16#64) ↦₆₄ o2) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem finishGrowEvents_eq_rawVecGrow (stride : Nat) (cap : BitVec 64)
    (hnew : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4) :
    finishGrowEvents cap.toNat (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat 8 stride =
      rawVecGrowEvents stride 4 8 cap := by
  unfold finishGrowEvents rawVecGrowEvents rawVecNewCap
  rw [hnew]
  by_cases h0 : cap = 0#64
  · subst h0
    simp only [BitVec.toNat_zero, ↓reduceIte]
    rfl
  · have hnat : cap.toNat ≠ 0 := fun hz => h0 (BitVec.eq_of_toNat_eq hz)
    simp only [h0, hnat, ↓reduceIte]

private theorem instantiate_post_exists {α : Sort _} {prog : Program} {target_pc : BitVec 64}
    {s0 s : State} {P R : SepProp} {Q : α → State → SepProp} {oom : State → SepProp}
    (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Q w sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom) :
    SepWP prog target_pc s P (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (∃∗ a, Q a sf) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  refine SepWP.mono h fun sf P_f _ _ ⟨hq, hsp, hcs⟩ => ⟨fun hm => ?_, hsp, hcs⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨w, hq hm⟩

/-! ## Cell-Unfolded `finish_grow` Wrappers (`stride = 48` and `stride = 104`, `align = 8`) -/

private abbrev FGGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def fgCellSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stride : BitVec 64) (hookStack : Nat) : Spec (FGGhost × M.σ) where
  pre := fun ((out, cap, ptr, new, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ (cap = 0#64 → bs = []) ∧ bs.length = cap.toNat * stride.toNat ∧
      cap.toNat ≤ new.toNat ∧ 0 < new.toNat ∧ 0 < stride.toNat ∧
      new.toNat * stride.toNat + 8 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (finishGrowEvents cap.toNat new.toNat 8 stride.toNat)⌝ ∗
    (if cap = 0#64 then emp else A.repAlloc.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool lim st s ∗ stackAt fsp (hookStack + 48) ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2)
  post := fun ((out, cap, _, new, bs, _, _, _, fsp), st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.repAlloc.live p' (new.toNat * stride.toNat) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * stride.toNat - bs.length) ∗
      A.pool lim (M.stepEvents (finishGrowEvents cap.toNat new.toNat 8 stride.toNat) st) sf ∗
      stackAt fsp (hookStack + 48) ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * stride.toNat))

private theorem fgCell_ok_of_finishGrow {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (stride : BitVec 64) (hookStack : Nat)
    (hfg : subroutine_ok prog entry
      (LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack M A lim hookStack)) :
    subroutine_ok prog entry (fgCellSpec M A lim stride hookStack) := by
  refine subroutine_ok_outcome_intro
    fun ⟨⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [fgCellSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hc0_nil, hbs, hle, hpos, hspos, hbound, hfit⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 8#64, stride, bs⟩
  have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have hlay : RustLayoutOk (new.toNat * stride.toNat) (8#64 : BitVec 64).toNat := by
    rw [ha8]
    refine ⟨⟨Nat.mul_pos hpos hspos, ⟨3, rfl⟩, hbound⟩, by decide⟩
  have hfit_env : FitsEnv M lim st (FinishGrowEnv hcall) := by
    rw [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.fitsEnv_finishGrow_iff]
    exact hfit
  have hold : hcall.oldBuf A.repAlloc =
      (if cap = 0#64 then emp else A.repAlloc.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) := by
    dsimp only [FinishGrowCall.oldBuf, hcall]
    by_cases hc : cap = 0#64
    · simp only [hc, ↓reduceIte]
    · simp only [hc, ↓reduceIte, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp]
  have hpre' : s0.mem ⊨
      (LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack M A lim hookStack).pre
        (hcall, st) s0 ∗ R := by
    simp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      hcall, hold, memRegion_24_cells3, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hc0_nil, Nat.le_of_eq hbs, hle, hpos, hspos, hlay, hfit_env⟩, ?_⟩
    convert hmem using 1
    sep_ac_rfl
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      fgCellSpec, hcall, ha8, RustCliAllocBudget.repAlloc_live,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    refine ⟨p', ?_⟩
    convert hq using 1
    sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-! ## 1. Block `42`: `RawVec<SignalProtocolError>::grow_one` (`stride = 48`, `allocHookStack`) -/

/-- Block `42`: `<alloc::raw_vec::RawVec<SignalProtocolError>>::grow_one` meets
`growOneSpeSpec M A lim` under `[LibsignalPlacement]`, given `finishGrowSpec M A lim`. -/
theorem grow_one_spe_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base (finishGrowSpec M A lim)) :
    subroutine_ok ((blkPC_42).rebase (blkPl_42).base H)
      (blkPl_42).base
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) := by
  simp only [withLsCodeLoaded, growOneSpeSpec, stackAt_grow_one_spe, sepExists_sepConj_right]
  have hfg_cell : subroutine_ok ((blkPC_42).rebase (blkPl_42).base H) (lsmpl.base 45)
      (withLsCodeLoaded lsmpl (fgCellSpec M A lim 48#64 allocHookStack)) :=
    ls_subroutine_ok_of_block
      (subroutine_ok_withLsCodeLoaded_of_plain (fgCell_ok_of_finishGrow 48#64 allocHookStack hfg))
  simp only [withLsCodeLoaded, fgCellSpec] at hfg_cell
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hbound63 : max (2 * cap.toNat) 4 * 48 + 8 ≤ 2 ^ 63 := by omega
  have hEnv : FitsEnv M lim st (GrowOneSpeEnv cap) := by assumption
  have hnew_eq := grow_new_cap_eq (stride := 48) (by decide) hbound63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hevs_eq : finishGrowEvents cap.toNat new.toNat 8 48 = growOneSpeEvents cap :=
    finishGrowEvents_eq_rawVecGrow 48 cap hnew_toNat
  have hfit_fg : FitsEvents M lim st (finishGrowEvents cap.toNat new.toNat 8 (48#64 : BitVec 64).toNat) := by
    change FitsEvents M lim st (finishGrowEvents cap.toNat new.toNat 8 48)
    rw [hevs_eq]
    exact hEnv (growOneSpeEvents cap) (growOneSpeEnv_events cap)
  have hc0_nil : cap = 0#64 → bs = [] := fun hc0 => by
    subst hc0
    exact List.eq_nil_of_length_eq_zero ‹bs.length = (0#64 : BitVec 64).toNat * 48›
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * (48#64 : BitVec 64).toNat + 8 ≤ 2 ^ 63 := by
    change new.toNat * 48 + 8 ≤ 2 ^ 63; omega
  have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 48 = new.toNat * 48 - bs.length := by
    rw [Nat.sub_mul, hnew_toNat, ‹bs.length = cap.toNat * 48›]
  simp only [RustCliAllocBudget.repAlloc_live] at hfg_cell ⊢
  apply CryptoVerification.sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
  wp_steps_sync_pool (lsmpl.base 45)
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_call
  wp_call hfg_cell ((s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64), st)
  simp only [show (48#64 : BitVec 64).toNat = 48 from rfl] at *
  rw [hevs_eq, ← hsub_mul]
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply instantiate_post_exists (growOneSpeEvents cap)
  simp only [growOneSpeEnv_events cap, and_true, hnew_toNat,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_done

/-- Block `42`: `<alloc::raw_vec::RawVec<SignalProtocolError>>::grow_one` meets
`growOneSpeSpec M A lim` under `[LibsignalPlacement]` and `HookSat` budget allocator contracts. -/
theorem grow_one_spe_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_42).rebase (blkPl_42).base H)
      (blkPl_42).base
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) :=
  grow_one_spe_placed_ok_of_fg (finish_grow_placed_ok hshim halloc hrealloc)

/-- `NoOom`-`HookSat` variant of `grow_one_spe_placed_ok`. -/
theorem grow_one_spe_placed_ok_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok ((blkPC_42).rebase (blkPl_42).base H)
      (blkPl_42).base
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) :=
  grow_one_spe_placed_ok_of_fg (finish_grow_placed_ok_noOom hshim halloc hrealloc)

/-! ## 2. Block `43`: `RawVec<Chain>::grow_one` (`stride = 104`, `extHookStack`) -/

/-- Deterministic `AllocEvent` list emitted by `RawVec<Chain>::grow_one` (`stride = 104, minCap = 4, align = 8`). -/
abbrev growOne104Events (cap : BitVec 64) : List AllocEvent :=
  rawVecGrowEvents 104 4 8 cap

/-- Allocation envelope for `RawVec<Chain>::grow_one`. -/
def GrowOne104Env (cap : BitVec 64) (evs : List AllocEvent) : Prop :=
  (cap = 0#64 ∧ evs = rustAllocEvents (4 * 104) 8) ∨
  (cap ≠ 0#64 ∧ evs = rustReallocEvents (cap.toNat * 104) (max (2 * cap.toNat) 4 * 104) 8)

theorem growOne104Env_events (cap : BitVec 64) :
    GrowOne104Env cap (growOne104Events cap) := by
  unfold GrowOne104Env growOne104Events rawVecGrowEvents rawVecNewCap
  by_cases h : cap = 0#64
  · simp only [h, ↓reduceIte, true_and, true_or]
  · exact Or.inr ⟨h, by simp only [h, ↓reduceIte]⟩

/-- Budget-threaded total-correctness contract for `RawVec<Chain>::grow_one` (`464 + finishGrowStackX`). -/
def growOne104SpecX (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
      max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOne104Env cap)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool lim st s ∗ stackAt s.sp (464 + finishGrowStackX)
  post := fun ((v, cap, _, bs), st) s0 sf =>
    let newCap := max (2 * cap.toNat) 4
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ GrowOne104Env cap evs⌝ ∗
      (∃∗ p' : BitVec 64,
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (newCap * 104) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 bs.length) ((newCap - cap.toNat) * 104)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp (464 + finishGrowStackX)

/-- Block `43`: `<alloc::raw_vec::RawVec<Chain>>::grow_one` meets
`growOne104SpecX M A lim` under `[LibsignalPlacement]`, given `finishGrowSpecX M A lim`. -/
theorem grow_one_104_placed_ok_of_fg_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base (finishGrowSpecX M A lim)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H)
      (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOne104SpecX M A lim)) := by
  simp only [withLsCodeLoaded, growOne104SpecX, stackAt_grow_one_104_x, sepExists_sepConj_right]
  have hfg_cell : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (lsmpl.base 45)
      (withLsCodeLoaded lsmpl (fgCellSpec M A lim 104#64 extHookStack)) :=
    ls_subroutine_ok_of_block
      (subroutine_ok_withLsCodeLoaded_of_plain (fgCell_ok_of_finishGrow 104#64 extHookStack hfg))
  simp only [withLsCodeLoaded, fgCellSpec] at hfg_cell
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hbound63 : max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by omega
  have hEnv : FitsEnv M lim st (GrowOne104Env cap) := by assumption
  have hnew_eq := grow_new_cap_eq (stride := 104) (by decide) hbound63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hevs_eq : finishGrowEvents cap.toNat new.toNat 8 104 = growOne104Events cap :=
    finishGrowEvents_eq_rawVecGrow 104 cap hnew_toNat
  have hfit_fg : FitsEvents M lim st (finishGrowEvents cap.toNat new.toNat 8 (104#64 : BitVec 64).toNat) := by
    change FitsEvents M lim st (finishGrowEvents cap.toNat new.toNat 8 104)
    rw [hevs_eq]
    exact hEnv (growOne104Events cap) (growOne104Env_events cap)
  have hc0_nil : cap = 0#64 → bs = [] := fun hc0 => by
    subst hc0
    exact List.eq_nil_of_length_eq_zero ‹bs.length = (0#64 : BitVec 64).toNat * 104›
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * (104#64 : BitVec 64).toNat + 8 ≤ 2 ^ 63 := by
    change new.toNat * 104 + 8 ≤ 2 ^ 63; omega
  have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = new.toNat * 104 - bs.length := by
    rw [Nat.sub_mul, hnew_toNat, ‹bs.length = cap.toNat * 104›]
  simp only [RustCliAllocBudget.repAlloc_live] at hfg_cell ⊢
  apply CryptoVerification.sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
  wp_steps_sync_pool (lsmpl.base 45)
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_call
  wp_call hfg_cell ((s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64), st)
  simp only [show (104#64 : BitVec 64).toNat = 104 from rfl] at *
  rw [hevs_eq, ← hsub_mul]
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply instantiate_post_exists (growOne104Events cap)
  simp only [growOne104Env_events cap, and_true, hnew_toNat,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_done

/-- Block `43`: `<alloc::raw_vec::RawVec<Chain>>::grow_one` meets
`growOne104SpecX M A lim` under `[LibsignalPlacement]` and `HookSat` budget allocator contracts. -/
theorem grow_one_104_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H)
      (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOne104SpecX M A lim)) :=
  grow_one_104_placed_ok_of_fg_x (finish_grow_placed_ok_x hshim halloc hrealloc)

/-- `NoOom`-`HookSat` variant of `grow_one_104_placed_ok_x`. -/
theorem grow_one_104_placed_ok_x_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H)
      (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOne104SpecX M A lim)) :=
  grow_one_104_placed_ok_of_fg_x (finish_grow_placed_ok_x_noOom hshim halloc hrealloc)

end LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget
