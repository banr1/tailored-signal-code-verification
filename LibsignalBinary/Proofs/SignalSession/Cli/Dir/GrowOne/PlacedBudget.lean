/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs

/-!
# Budget-Threaded `[LibsignalPlacement]` `RawVec<(String, Vec<u8>)>::grow_one` (Block 586)

Verifies Block 586 (`grow_one`) against `withLsCodeRoLoaded lsmpl (growOneDirBytesInnerSpec A lim)`
and `growOneDirSpecPlaced A lim stk` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.PlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (LayoutOk arrayAt vecAt vecBuf vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  FinishGrowCall SepWP.instantiate_post_exists extHookStack finishGrowStackX
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded
)
open CryptoVerification.SignalSession.Cli (dirEntryAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_586 lsProg_586)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (
  CliPanicHooksPlaced satisfies_lscro_pre
)
open CryptoVerification.SignalSession.Cli.GrowOne.Helpers (
  FGCellsGhost cliGrowOneStack grow_new_cap_eq memRegion_bound_of_pointsTo64
  stackAt_cliGrowOne stackAt_split_stk
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustReallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecGrowEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  FinishGrowEnv finishGrowEvents finishGrowSpecWithStack finishGrowSpecX fitsEnv_finishGrow_iff
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.LayoutBudget (
  FinishGrowNeEnv FinishGrowZeroEnv GrowOneDirBytesEnv
  finishGrowNeCellsSpec finishGrowZeroCellsSpec growOneDirBytesInnerSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget (growOneDirRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (growOneDirSpecPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem memRegion_24_cells_p (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

/-- Refinement of `finishGrowZeroCellsSpec` adding `align.toNat ≤ 2 ^ 31` (`RustLayoutOk`),
which holds automatically at concrete Rust alignments (`1`, `8`, …). -/
def finishGrowZeroCellsRustSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FGCellsGhost × M.σ) :=
  { finishGrowZeroCellsSpec A lim with
    pre := fun ((out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st) s =>
      ⌜align.toNat ≤ 2 ^ 31⌝ ∗
        (finishGrowZeroCellsSpec A lim).pre
          ((out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st) s }

/-- Refinement of `finishGrowNeCellsSpec` adding `align.toNat ≤ 2 ^ 31` (`RustLayoutOk`). -/
def finishGrowNeCellsRustSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FGCellsGhost × M.σ) :=
  { finishGrowNeCellsSpec A lim with
    pre := fun ((out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st) s =>
      ⌜align.toNat ≤ 2 ^ 31⌝ ∗
        (finishGrowNeCellsSpec A lim).pre
          ((out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st) s }

theorem finish_grow_zero_cells_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (hFG : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (finishGrowSpecX M A lim))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (finishGrowZeroCellsRustSpec A lim)) := by
  refine subroutine_ok_outcome_intro
    fun ⟨(out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [finishGrowZeroCellsRustSpec, finishGrowZeroCellsSpec, FinishGrowZeroEnv,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hal31, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay, hfit⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hpre0 : s0.mem ⊨ (finishGrowSpecX M A lim).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrowSpecX, finishGrowSpecWithStack, fitsEnv_finishGrow_iff,
      finishGrowEvents, hcall, FinishGrowCall.oldBuf, BitVec.toNat_zero, ↓reduceIte,
      memRegion_24_cells_p, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, hstr,
      ⟨hlay, hal31⟩, hfit _ rfl⟩,
      by convert hmem using 1; sep_ac_rfl⟩
  have hpre' := satisfies_lscro_pre hcrl hpre0
  refine hFG.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded] at hq
    simp only [finishGrowSpecX, finishGrowSpecWithStack, finishGrowZeroCellsRustSpec,
      finishGrowZeroCellsSpec, FinishGrowZeroEnv, finishGrowEvents, hcall, BitVec.toNat_zero,
      ↓reduceIte, pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero,
      emp_sepConj, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    refine ⟨rustAllocEvents (new.toNat * stride.toNat) align.toNat, p',
      BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2, rfl⟩, ?_⟩
    convert hq.2 using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

theorem finish_grow_ne_cells_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (hFG : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (finishGrowSpecX M A lim))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (finishGrowNeCellsRustSpec A lim)) := by
  refine subroutine_ok_outcome_intro
    fun ⟨(out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [finishGrowNeCellsRustSpec, finishGrowNeCellsSpec, FinishGrowNeEnv,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hal31, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay, hfit⟩, hmem⟩
  subst hfsp
  have hcap_nat_ne : cap.toNat ≠ 0 := fun hc => hcap (BitVec.eq_of_toNat_eq hc)
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, align, stride, bs⟩
  have hpre0 : s0.mem ⊨ (finishGrowSpecX M A lim).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrowSpecX, finishGrowSpecWithStack, fitsEnv_finishGrow_iff,
      finishGrowEvents, hcall, FinishGrowCall.oldBuf, hcap, hcap_nat_ne, ↓reduceIte,
      memRegion_24_cells_p, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, hstr, ⟨hlay, hal31⟩, hfit _ rfl⟩,
      by convert hmem using 1; sep_ac_rfl⟩
  have hpre' := satisfies_lscro_pre hcrl hpre0
  refine hFG.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded] at hq
    simp only [finishGrowSpecX, finishGrowSpecWithStack, finishGrowNeCellsRustSpec,
      finishGrowNeCellsSpec, FinishGrowNeEnv, finishGrowEvents, hcall, hcap_nat_ne, ↓reduceIte,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    refine ⟨rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat,
      p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2, rfl⟩, ?_⟩
    convert hq.2 using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

theorem growOneDirBytes_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_hpan : CliPanicHooksPlaced H)
    (hFG : subroutine_ok (lsProg_586 H) (lsmpl.base 587)
      (withLsCodeRoLoaded lsmpl (finishGrowSpecX M A lim))) :
    subroutine_ok (lsProg_586 H) (blkPl_586).base
      (withLsCodeRoLoaded lsmpl (growOneDirBytesInnerSpec A lim)) := by
  dsimp only [withLsCodeRoLoaded]
  simp only [growOneDirBytesInnerSpec, sepExists_sepConj_left, sepExists_sepConj_right]
  simp only [stackAt_cliGrowOne, sepExists_sepConj_right]
  wp_init x s0
  obtain ⟨⟨v, cap, ptr, bs⟩, st⟩ := x
  have hcrl : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  dsimp only at *
  have hfg0 := finish_grow_zero_cells_placed_ok_x hFG
  have hfg1 := finish_grow_ne_cells_placed_ok_x hFG
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (48#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 48; omega, hpow, ?_⟩
    change new.toNat * 48 + 8 ≤ 2 ^ 63; omega
  have hal31 : (8#64 : BitVec 64).toNat ≤ 2 ^ 31 := by decide
  have hfit_env : FitsEnv M lim st (GrowOneDirBytesEnv cap) := by assumption
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 48 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 48 = new.toNat * 48 := by rw [hnew_toNat]; rfl
    have hevs_eq : GrowOneDirBytesEnv 0#64 = FinishGrowZeroEnv new 48#64 8#64 := by
      funext evs
      simp only [GrowOneDirBytesEnv, FinishGrowZeroEnv, rawVecGrowEvents, BitVec.toNat_zero,
        ↓reduceIte, hnew_toNat]
      rfl
    have hfit0 : FitsEnv M lim st (FinishGrowZeroEnv new 48#64 8#64) := hevs_eq ▸ hfit_env
    simp only [↓reduceIte, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply sepWP_seq_lscro hcrl (mid := lsmpl.base 587)
    wp_steps_sync_pool (lsmpl.base 587)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    wp_call_lscro hfg0 hcrl1
      ((s0.sp - 56#64, 0#64, ptr, new, 8#64, 48#64, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64), st)
    wp_steps_sync_pool (s0.readReg64 .lr)
    dsimp only [new]
    apply SepWP.instantiate_post_exists w
    apply SepWP.instantiate_post_exists w_1
    rw [hevs_eq]
    wp_done
  · simp only [hcap0, ↓reduceIte, sepConj_assoc]
    have hcap_nat_ne : cap.toNat ≠ 0 := fun hc => hcap0 (BitVec.eq_of_toNat_eq hc)
    have hsub_eq : max (2 * cap.toNat) 4 * 48 - bs.length = new.toNat * 48 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 48 = new.toNat * 48 := by
      rw [hnew_toNat]
    have hevs_eq : GrowOneDirBytesEnv cap = FinishGrowNeEnv cap new 48#64 8#64 := by
      funext evs
      simp only [GrowOneDirBytesEnv, FinishGrowNeEnv, rawVecGrowEvents, hcap0,
        ↓reduceIte, hnew_toNat]
      rfl
    have hfit1 : FitsEnv M lim st (FinishGrowNeEnv cap new 48#64 8#64) := hevs_eq ▸ hfit_env
    rw [hsub_eq, hmul_eq]
    apply sepWP_seq_lscro hcrl (mid := lsmpl.base 587)
    wp_steps_sync_pool (lsmpl.base 587)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    wp_call_lscro hfg1 hcrl1
      ((s0.sp - 56#64, cap, ptr, new, 8#64, 48#64, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64), st)
    wp_steps_sync_pool (s0.readReg64 .lr)
    dsimp only [new]
    apply SepWP.instantiate_post_exists w
    apply SepWP.instantiate_post_exists w_1
    rw [hevs_eq]
    wp_done

private def vecHeaderBytesP (cap ptr len : BitVec 64) : List (BitVec 8) :=
  unpack64 cap ++ (unpack64 ptr ++ unpack64 len)

private theorem vecHeader_eq_bytes_p (a cap ptr len : BitVec 64) :
    vecHeader a cap ptr len = (a ↦ₛ vecHeaderBytesP cap ptr len) := by
  unfold vecHeader vecHeaderBytesP
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  simp only [pointsToBytes_append, unpack64_length, h16, ← pointsTo64_eq_pointsToBytes]

private theorem dirEntry_body_eq_p (b c1 p1 l1 c2 p2 l2 : BitVec 64) (R1 R2 : SepProp) :
    (vecHeader b c1 p1 l1 ∗ R1) ∗ (vecHeader (b + 0x18#64) c2 p2 l2 ∗ R2) =
      (b ↦ₛ (vecHeaderBytesP c1 p1 l1 ++ vecHeaderBytesP c2 p2 l2)) ∗ (R1 ∗ R2) := by
  have hl : (vecHeaderBytesP c1 p1 l1).length = 24 := by simp [vecHeaderBytesP, unpack64_length]
  rw [vecHeader_eq_bytes_p, vecHeader_eq_bytes_p, pointsToBytes_append, hl]
  change _ = (_ ∗ ((b + 0x18#64) ↦ₛ _)) ∗ _
  sep_ac_rfl

private theorem dirEntry_reloc_p (A : CryptoVerification.RustHeap.RustAlloc)
    (e : List (BitVec 8) × List (BitVec 8)) (a : BitVec 64) :
    dirEntryAt A e a ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 48 ∧ ∀ b : BitVec 64, (b ↦ₛ bs) ∗ H ⊢ dirEntryAt A e b⌝ ∗ (a ↦ₛ bs) ∗ H := by
  dsimp only [dirEntryAt, vecU8, vecU8At]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  rw [dirEntry_body_eq_p]
  apply Entails.sepExists_right
    (vecHeaderBytesP c1 p1 (BitVec.ofNat 64 e.1.length) ++
      vecHeaderBytesP c2 p2 (BitVec.ofNat 64 e.2.length))
  apply Entails.sepExists_right
  refine Entails.pure_right ⟨by simp [vecHeaderBytesP, unpack64_length], fun b => ?_⟩ (Entails.refl _)
  rw [← dirEntry_body_eq_p]
  exact sepConj_mono
    (Entails.sepExists_right c1 (Entails.sepExists_right p1 (Entails.refl _)))
    (Entails.sepExists_right c2 (Entails.sepExists_right p2 (Entails.refl _)))

private theorem arrayAt_dirEntry_reloc_p (A : CryptoVerification.RustHeap.RustAlloc) :
    ∀ (xs : List (List (BitVec 8) × List (BitVec 8))) (a : BitVec 64),
      arrayAt (dirEntryAt A) 48 a xs ⊢
        ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
          ⌜bs.length = xs.length * 48 ∧
            ∀ b : BitVec 64, (b ↦ₛ bs) ∗ H ⊢ arrayAt (dirEntryAt A) 48 b xs⌝ ∗
          (a ↦ₛ bs) ∗ H
  | [], a => by
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    simp only [arrayAt, pointsToBytes_nil, List.length_nil, Nat.zero_mul, emp_sepConj]
    exact Entails.pure_right ⟨trivial, fun _ => Entails.refl emp⟩ (Entails.refl emp)
  | e :: xs, a => by
    dsimp only [arrayAt]
    refine Entails.trans (sepConj_mono (dirEntry_reloc_p A e a) (arrayAt_dirEntry_reloc_p A xs (a + 48#64))) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs1
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro H1
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs2
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro H2
    rw [sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hl1, hr1⟩
    rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hl2, hr2⟩
    refine Entails.sepExists_right (bs1 ++ bs2) (Entails.sepExists_right (H1 ∗ H2) ?_)
    have hlen : (bs1 ++ bs2).length = (e :: xs).length * 48 := by
      simp only [List.length_append, List.length_cons, hl1, hl2]; omega
    refine Entails.pure_right ⟨hlen, fun b => ?_⟩ ?_
    · rw [pointsToBytes_append, hl1]
      change ((b ↦ₛ bs1) ∗ ((b + 48#64) ↦ₛ bs2)) ∗ (H1 ∗ H2) ⊢
        dirEntryAt A e b ∗ arrayAt (dirEntryAt A) 48 (b + 48#64) xs
      have harr : ((b ↦ₛ bs1) ∗ ((b + 48#64) ↦ₛ bs2)) ∗ (H1 ∗ H2) =
          ((b ↦ₛ bs1) ∗ H1) ∗ (((b + 48#64) ↦ₛ bs2) ∗ H2) := by sep_ac_rfl
      rw [harr]
      exact sepConj_mono (hr1 b) (hr2 (b + 48#64))
    · rw [pointsToBytes_append, hl1]
      change (a ↦ₛ bs1) ∗ H1 ∗ ((a + 48#64) ↦ₛ bs2) ∗ H2 ⊢
        ((a ↦ₛ bs1) ∗ ((a + 48#64) ↦ₛ bs2)) ∗ (H1 ∗ H2)
      exact Entails.of_eq (by sep_ac_rfl)

theorem growOneDir_placed_of_bytes [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hbs_ok : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (growOneDirBytesInnerSpec A lim)))
    (hstk : 0x40 + finishGrowStackX ≤ stk) :
    subroutine_ok prog entry (growOneDirSpecPlaced A lim stk) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨v, cap, ptr, xs⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [growOneDirSpecPlaced, growOneDirRawSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hcap32, hfit⟩, hmem⟩
  dsimp only [vecAt, vecHeader, vecBuf] at hmem
  have hmem_p : s0.mem ⊨
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        (if cap = 0 then emp
         else A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
           arrayAt (dirEntryAt A.repAlloc) 48 ptr xs ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * 48))
             ((cap.toNat - xs.length) * 48)) ∗
        stackAt s0.sp stk ∗ A.pool lim st s0 ∗ R) := by
    convert hmem using 1; sep_ac_rfl
  rw [satisfies_pure_sepConj] at hmem_p
  rcases hmem_p with ⟨⟨hxs_le, _, hptr_ne⟩, hmem_s⟩
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk) (a := v) (v := cap)
      (R := ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        (if cap = 0 then emp
         else A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
           arrayAt (dirEntryAt A.repAlloc) 48 ptr xs ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * 48))
             ((cap.toNat - xs.length) * 48)) ∗
        A.pool lim st s0 ∗ R) ?_
    dsimp only [stackAt] at hmem_s
    convert hmem_s using 1; sep_ac_rfl
  rw [stackAt_split_stk s0.sp hstk hstk_hi] at hmem_s
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliGrowOneStack)
  let newCap := max (2 * cap.toNat) 4
  have hmax_eq : max (2 * cap.toNat) 4 = newCap := rfl
  have hbound : newCap * 48 + 8 ≤ 2 ^ 63 := by dsimp [newCap]; omega
  have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [newCap]; omega)]
  have hnew_ne : BitVec.ofNat 64 newCap ≠ 0 := by
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [hnew_toNat] at ht
    change newCap = 0 at ht
    dsimp [newCap] at ht; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hxs0 : xs = [] :=
      List.eq_nil_of_length_eq_zero (by simpa using hxs_le)
    subst hxs0
    simp only [show (0#64 : BitVec 64) = 0 from rfl, ↓reduceIte] at hmem_s
    let F_extra := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗ stkRem
    have hpre0 : s0.mem ⊨ (growOneDirBytesInnerSpec A lim).pre ((v, 0#64, ptr, []), st) s0 ∗ (F_extra ∗ R) := by
      simp only [growOneDirBytesInnerSpec, ↓reduceIte, emp_sepConj,
        sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, Nat.zero_le _, hptr_ne, hbound, hfit⟩, ?_⟩
      convert hmem_s using 1
      dsimp [F_extra, stkRem]
      sep_ac_rfl
    have hpre' := satisfies_lscro_pre hcrl hpre0
    refine hbs_ok.mono_outcome ((v, 0#64, ptr, []), st) (F_extra ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeRoLoaded, growOneDirBytesInnerSpec, RustCliAllocBudget.live,
        growOneDirSpecPlaced, growOneDirRawSpec] at hq ⊢
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨htrace, hevs⟩, hq⟩
      refine ⟨⟨htrace, hevs⟩, ?_⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨p', hq⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨⟨hp', _⟩, hmemf⟩
      refine ⟨p', ?_⟩
      dsimp only [vecAt, vecHeader, vecBuf, List.length_nil]
      rw [hmax_eq] at hmemf ⊢
      simp only [hnew_ne, ↓reduceIte, hnew_toNat, Nat.sub_zero, Nat.zero_mul,
        pointsToBytes_nil, emp_sepConj, BitVec.add_zero] at hmemf ⊢
      have harray0 : arrayAt (dirEntryAt A.repAlloc) 48 p' [] = emp := rfl
      rw [harray0, emp_sepConj]
      have hpost_p : sf.mem ⊨
          ⌜0 ≤ newCap ∧ newCap * 48 < 2 ^ 63 ∧ p' ≠ 0⌝ ∗
          (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗
            (A.repAlloc.live p' (newCap * 48) 8 ∗ memRegion p' (newCap * 48)) ∗
            (stkRem ∗ stackAt s0.sp cliGrowOneStack) ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨Nat.zero_le _, by omega, hp'⟩, ?_⟩
        convert hmemf using 1
        dsimp [F_extra, stkRem]
        sep_ac_rfl
      rw [← stackAt_split_stk s0.sp hstk hstk_hi] at hpost_p
      convert hpost_p using 1; sep_ac_rfl
    · dsimp only [withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  · have hcap0_z : cap ≠ 0 := hcap0
    simp only [hcap0_z, ↓reduceIte] at hmem_s
    have hsplit : s0.mem ⊨
        (∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
          ⌜bs.length = xs.length * 48 ∧
            ∀ b : BitVec 64, (b ↦ₛ bs) ∗ H ⊢ arrayAt (dirEntryAt A.repAlloc) 48 b xs⌝ ∗
          (ptr ↦ₛ bs) ∗ H) ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
          A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
          memRegion (ptr + BitVec.ofNat 64 (xs.length * 48))
            ((cap.toNat - xs.length) * 48) ∗
          (stkRem ∗ stackAt s0.sp cliGrowOneStack) ∗ A.pool lim st s0 ∗ R) := by
      refine Satisfies.mono (sepConj_mono_left (arrayAt_dirEntry_reloc_p A.repAlloc xs ptr)) ?_
      dsimp only [stkRem]
      convert hmem_s using 1; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hsplit
    rcases hsplit with ⟨bs, hsplit⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hsplit
    rcases hsplit with ⟨H, hsplit⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hsplit
    rcases hsplit with ⟨⟨hbs_len, hrec⟩, hsplit⟩
    let F_extra := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗ H ∗ stkRem
    have hbs_le : bs.length ≤ cap.toNat * 48 := by rw [hbs_len]; omega
    have hmr_old :
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 48 - bs.length) =
        memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48) := by
      rw [hbs_len, Nat.sub_mul]
    have hpre0 : s0.mem ⊨ (growOneDirBytesInnerSpec A lim).pre ((v, cap, ptr, bs), st) s0 ∗ (F_extra ∗ R) := by
      simp only [growOneDirBytesInnerSpec, hcap0, ↓reduceIte,
        sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hbs_le, hptr_ne, hbound, hfit⟩, ?_⟩
      rw [hmr_old]
      convert hsplit using 1
      dsimp [F_extra, stkRem]
      sep_ac_rfl
    have hpre' := satisfies_lscro_pre hcrl hpre0
    refine hbs_ok.mono_outcome ((v, cap, ptr, bs), st) (F_extra ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeRoLoaded, growOneDirBytesInnerSpec, RustCliAllocBudget.live,
        growOneDirSpecPlaced, growOneDirRawSpec] at hq ⊢
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨htrace, hevs⟩, hq⟩
      refine ⟨⟨htrace, hevs⟩, ?_⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨p', hq⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨⟨hp', _⟩, hmemf⟩
      refine ⟨p', ?_⟩
      dsimp only [vecAt, vecHeader, vecBuf]
      rw [hmax_eq] at hmemf ⊢
      simp only [hnew_ne, ↓reduceIte, hnew_toNat]
      have hmr_new :
          memRegion (p' + BitVec.ofNat 64 bs.length) (newCap * 48 - bs.length) =
          memRegion (p' + BitVec.ofNat 64 (xs.length * 48)) ((newCap - xs.length) * 48) := by
        rw [hbs_len, Nat.sub_mul]
      have hreasm : sf.mem ⊨
          arrayAt (dirEntryAt A.repAlloc) 48 p' xs ∗
          (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
            A.repAlloc.live p' (newCap * 48) 8 ∗
            memRegion (p' + BitVec.ofNat 64 (xs.length * 48)) ((newCap - xs.length) * 48) ∗
            (stkRem ∗ stackAt s0.sp cliGrowOneStack) ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) := by
        refine Satisfies.mono (sepConj_mono_left (hrec p')) ?_
        rw [hmr_new] at hmemf
        convert hmemf using 1
        dsimp [F_extra, stkRem]
        sep_ac_rfl
      rw [← stackAt_split_stk s0.sp hstk hstk_hi] at hreasm
      have hpost_p : sf.mem ⊨
          ⌜xs.length ≤ newCap ∧ newCap * 48 < 2 ^ 63 ∧ p' ≠ 0⌝ ∗
          (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
            (A.repAlloc.live p' (newCap * 48) 8 ∗ arrayAt (dirEntryAt A.repAlloc) 48 p' xs ∗
              memRegion (p' + BitVec.ofNat 64 (xs.length * 48)) ((newCap - xs.length) * 48)) ∗
            stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨by dsimp [newCap]; omega, by omega, hp'⟩, ?_⟩
        convert hreasm using 1; sep_ac_rfl
      convert hpost_p using 1; sep_ac_rfl
    · dsimp only [withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.PlacedBudget
