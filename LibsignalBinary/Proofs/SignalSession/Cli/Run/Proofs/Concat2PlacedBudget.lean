/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve

/-!
# Budget-Threaded Placed `<[&[u8]] as Concat<u8>>::concat` (Block `598`)

Defines budget-threaded `cliConcat2SpecPlaced` under `RustCliAllocBudget M` and proves
`cliConcat2_placed_ok` and `cliConcat2_placed_at_block` on Block `598` from
`AllocContractsXCliPlaced A lim H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2PlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ
)
open CryptoVerification.RustHeap (LayoutOk vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack memcpyName sessionMemcpyRegionSpec withStack
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsRoCl ls_subroutine_ok_rocl_of_block
  sepWP_seq_lscro subroutine_ok_rocl_of_plain withLsCodeRoLoaded withLsRoCl
)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_598 instIsLsBlockProg_598 lsProg_598)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617 instIsLsBlockProg_617)
open CryptoVerification.SignalSession.Cli.RunProofs (lsRawVecHandleErrorSymCli)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open CryptoVerification.SpqrV1.ChainProofs (SliceConcat2Ghost bytesAt bytesAt_false bytesAt_true)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget (
  cliConcat2Events cliConcat2Spec
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (
  allocNoOomExtern_lscro_of_cli shim_lscro_of_cli
)

/-- Budget-form relocatable `[LibsignalPlacement]` counterpart of `cliConcat2SpecPlaced`
(Block `598`). -/
def cliConcat2SpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (SliceConcat2Ghost × M.σ) :=
  withLsCodeRoLoaded lsmpl (cliConcat2Spec M A lim stk)

section Concat2PlacedBudgetHelpers

open scoped CryptoVerification.SpqrV1.Alloc.DoReserveNorm

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev cliConcatStackPlaced : Nat := 96 + extHookStack

private theorem memRegion_24_cells_concat_placed (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_cliConcat_placed (sp : BitVec 64) :
    stackAt sp cliConcatStackPlaced =
      stackAt (sp - 96#64) extHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 16384 12 (by decide)
  have hsum : 16384 + 8 * 12 = cliConcatStackPlaced := by decide
  rw [hsum] at h1
  change stackAt sp cliConcatStackPlaced =
    stackAt (sp - 96#64) extHookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]

private theorem stackAt_split_ge_concat_placed (sp : BitVec 64) {n m : Nat}
    (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

private theorem subroutine_ok_frame_weaken_concat_placed {α : Type} {prog : Program}
    {entry : BitVec 64} {spec spec' : Spec α} (F : α → State → SepProp)
    (h : subroutine_ok prog entry spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, spec.post x s0 sf ∗ F x s0 ⊢ spec'.post x s0 sf)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hexit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry spec' := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp => ?_
  have hp' : s0.mem ⊨ spec.pre x s0 ∗ (F x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hp
  refine h.mono_outcome x (F x s0 ∗ R) s0 hpc hrun hp' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq
  · rw [hpan] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem ofNat_getLsbD_63_false_placed {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_getElem_63_false_placed {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false :=
  ofNat_getLsbD_63_false_placed h

private theorem ofNat_beq_zero_false_concat_placed {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem ofNat_ult_of_le_placed {a b : Nat} (hle : a ≤ b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = false := by
  have ha : a < 2 ^ 64 := by omega
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_false_iff_not]
  omega

private def cliMemcpyBytesAtConcatSpecPlaced (ro : Bool) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length ∧
     bs.length ≤ 2 ^ 64⌝ ∗
    memRegion dst bs.length ∗
    bytesAt ro src bs ∗
    stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
    (dst ↦ₛ bs) ∗
    bytesAt ro src bs ∗
    stackAt s0.sp extHookStack

private theorem cliMemcpy_bytesAt_concat_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (ro : Bool) :
    subroutine_ok (lsProg_598 H) (lsρ memcpyName)
      (withLsRoCl lsmpl (cliMemcpyBytesAtConcatSpecPlaced ro)) := by
  cases ro
  · have hmc := @ls_subroutine_ok_rocl_of_block _ _ (lsProg_598 H) (lsProg_617 H) 598 617 H
      (instIsLsBlockProg_598 H) (instIsLsBlockProg_617 H) (lsρ memcpyName) _
      (hA.session_memcpy_region extHookStack (Nat.le_refl _) (by decide))
      _ _ _ _ (by decide) (by decide) (by decide)
    refine subroutine_ok_mono hmc ?_ ?_
    · intro ⟨dst, src, bs⟩ R s0 hpre
      obtain ⟨hcrl, hrest⟩ := extract_withLsRoCl hpre
      dsimp only [withLsRoCl, withStack, sessionMemcpyRegionBudgetSpec,
        sessionMemcpyRegionSpec, memcpyRegionSpec]
      dsimp only [cliMemcpyBytesAtConcatSpecPlaced, bytesAt_false] at hrest
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcrl, ?_⟩
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hrest ⊢
      exact ⟨⟨hrest.1.1, hrest.1.2.1, hrest.1.2.2.1⟩, hrest.2⟩
    · intro ⟨dst, src, bs⟩ R s0 sf hpost
      dsimp only [withLsRoCl, cliMemcpyBytesAtConcatSpecPlaced, withStack,
        sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
        bytesAt_false] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, ⟨hpost.2.2.1.1, hpost.2.2.1.2, hpost.2.1⟩, hpost.2.2.2⟩
  · have hmc_plain : subroutine_ok (lsProg_598 H) (lsρ memcpyName)
        (withVmPreserved sessionMemcpyRegionROSpec) :=
      ls_hook_ok_ultra_of_mem (prog := lsProg_598 H) (i := 598)
        (hprog := instIsLsBlockProg_598 H) hRO
    have hmc := subroutine_ok_rocl_of_plain (pl := lsmpl) hmc_plain
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨
        (withLsRoCl lsmpl (withVmPreserved sessionMemcpyRegionROSpec)).pre
          (dst, src, bs) s0 ∗ (stackAt s0.sp extHookStack ∗ R) := by
      obtain ⟨hcrl, hrest⟩ := extract_withLsRoCl hpre
      dsimp only [withLsRoCl, withVmPreserved, sessionMemcpyRegionROSpec]
      dsimp only [cliMemcpyBytesAtConcatSpecPlaced, bytesAt_true] at hrest
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcrl, ?_⟩
      simpa only [sepConj_assoc] using hrest
    refine hmc.mono_outcome (dst, src, bs) (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hal ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsRoCl, cliMemcpyBytesAtConcatSpecPlaced, withVmPreserved,
        sessionMemcpyRegionROSpec, bytesAt_true] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, ⟨hpost.2.2.1.1, hpost.2.2.1.2, hpost.2.1⟩, hpost.2.2.2⟩
    · simp only [withVmPreserved, sessionMemcpyRegionROSpec,
        satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [withVmPreserved, sessionMemcpyRegionROSpec,
        satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [withVmPreserved, sessionMemcpyRegionROSpec,
        satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1

private theorem vecU8_of_zero_placed (A : CryptoVerification.RustHeap.RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A v [] := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.le_refl, true_and, ↓reduceIte, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
      ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) by sep_ac_rfl]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.refl _)

private theorem vecU8_of_pos_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (v p' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live p' bs.length 1 ∗ (p' ↦ₛ bs) ⊢
      vecU8 A.repAlloc v bs := by
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change bs.length = 0 at ht
    omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold RustCliAllocBudget.live vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 bs.length))
  refine Entails.trans ?_ (Entails.sepExists_intro p')
  simp only [hne0, htoNat, Nat.le_refl, hlt, ↓reduceIte,
    Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ⌜True ∧ True ∧ p' ≠ 0⌝ ∗
        A.repAlloc.live p' bs.length 1 ∗ (p' ↦ₛ bs) =
      ⌜True ∧ True ∧ p' ≠ 0⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.repAlloc.live p' bs.length 1 ∗ (p' ↦ₛ bs)) by sep_ac_rfl]
  exact Entails.pure_right ⟨trivial, trivial, hp'⟩ (Entails.refl _)

private theorem vecU8_of_append_pos_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (v p' : BitVec 64) (bs0 bs1 : List (BitVec 8))
    (hpos : 0 < bs0.length + bs1.length) (hlt : bs0.length + bs1.length < 2 ^ 63)
    (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length)) ∗
      A.live p' (bs0.length + bs1.length) 1 ∗ (p' ↦ₛ (bs0 ++ bs1)) ⊢
      vecU8 A.repAlloc v (bs0 ++ bs1) := by
  rw [← List.length_append]
  exact vecU8_of_pos_placed A v p' (bs0 ++ bs1) (by rw [List.length_append]; exact hpos)
    (by rw [List.length_append]; exact hlt) hp'

set_option maxHeartbeats 1600000 in
theorem cliConcat2_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec)) :
    subroutine_ok (lsProg_598 H) (blkPl_598).base
      (cliConcat2SpecPlaced M A lim cliConcatStackPlaced) := by
  unfold cliConcat2SpecPlaced withLsCodeRoLoaded cliConcat2Spec
  simp only [memRegion_24_cells_concat_placed, stackAt_cliConcat_placed,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  have hshim := shim_lscro_of_cli (callerProg := lsProg_598 H) hA (stk := extHookStack) (by decide) (by decide)
  have halloc := allocNoOomExtern_lscro_of_cli (callerProg := lsProg_598 H) hA
  have hmc_any := cliMemcpy_bytesAt_concat_placed_ok hA hRO
  clear hA hRO
  dsimp only [withLsCodeRoLoaded, lsProg_598, ↓reduceIte] at hshim halloc hmc_any ⊢
  wp_init x s0
  obtain ⟨⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1⟩, st⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hmax : bs0.length + bs1.length < 2 ^ 63 := ‹_›
  have hfit_evs : FitsEvents M lim st (cliConcat2Events bs0 bs1) := ‹_›
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have htot_lt63 : bs1.length + bs0.length < 2 ^ 63 := by omega
  have htot_lt64 : bs1.length + bs0.length < 2 ^ 64 := by omega
  have h0_lt64 : bs0.length < 2 ^ 64 := by omega
  have h1_lt64 : bs1.length < 2 ^ 64 := by omega
  have h0_le64 : bs0.length ≤ 2 ^ 64 := by omega
  have h1_le64 : bs1.length ≤ 2 ^ 64 := by omega
  have hadd_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd01_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by
    rw [← BitVec.ofNat_add]
  have hsub_bv : BitVec.ofNat 64 (bs0.length + bs1.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs1.length := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
      omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]
      omega
  have hcs1 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le_placed (by omega) (by omega)
  have hbit63 : (BitVec.ofNat 64 (bs0.length + bs1.length)).getLsbD 63 = false :=
    ofNat_getLsbD_63_false_placed (by omega)
  have helem63 : (BitVec.ofNat 64 (bs0.length + bs1.length))[63] = false :=
    ofNat_getElem_63_false_placed (by omega)
  have htot_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length)).toNat = bs0.length + bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0_toNat : (BitVec.ofNat 64 bs0.length).toNat = bs0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64]
  have h1_toNat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
  have hhi0 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le_placed (by omega) (by omega)
  have hhi1 : (BitVec.ofNat 64 bs1.length).ult (BitVec.ofNat 64 bs1.length) = false :=
    ProofLib.bitvec_ult_self _
  have h0_eq : bs0 = [] ∨ 0 < bs0.length := by cases bs0 <;> simp
  have h1_eq : bs1 = [] ∨ 0 < bs1.length := by cases bs1 <;> simp
  rcases h0_eq with rfl | hpos0 <;>
    rcases h1_eq with rfl | hpos1
  · simp only [cliConcat2Events, List.length_nil, Nat.add_zero, ↓reduceIte,
      M.stepEvents_nil, List.nil_append] at *
    wp_steps_sync_pool (s0.readReg64 .lr)
    apply SepWP.fold (vecU8_of_zero_placed A.repAlloc outVec) (by sep_focus)
    wp_done
  · simp only [cliConcat2Events, List.length_nil, Nat.zero_add, Nat.ne_of_gt hpos1, ↓reduceIte,
      List.nil_append] at *
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false :=
      ofNat_beq_zero_false_concat_placed hpos1 h1_lt64
    have hrlay : RustLayoutOk bs1.length 1 := ⟨⟨hpos1, hpow1, by omega⟩, hal1⟩
    apply sepWP_seq_lscro hcrl0 (mid := lsρ lsRustNoAllocShimSymCli)
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    apply sepWP_seq_lscro hcrl1 (mid := lsρ lsRustAllocSymCli)
    rcases hcrl1 with ⟨hcl1, hro1⟩
    wp_call hshim ()
    refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl2
    apply sepWP_seq_lscro hcrl2 (mid := lsρ memcpyName)
    rcases hcrl2 with ⟨hcl2, hro2⟩
    wp_call halloc (bs1.length, 1, st)
    have hoom : sf_1.readReg64 Reg.x0 ≠ 0#64 := by tauto
    have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
    wp_steps_sync_pool (lsρ memcpyName)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    rintro ⟨hcl3, hro3⟩
    wp_apply using (hmc_any ro1)
    refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
    wp_steps_sync_pool (s0.readReg64 .lr)
    apply SepWP.fold (vecU8_of_pos_placed A outVec (sf_1.readReg64 Reg.x0) bs1 hpos1 hmax hoom)
      (by sep_focus)
    wp_done
  · simp only [cliConcat2Events, List.length_nil, Nat.add_zero, Nat.ne_of_gt hpos0, ↓reduceIte,
      List.append_nil] at *
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false :=
      ofNat_beq_zero_false_concat_placed hpos0 h0_lt64
    have hrlay : RustLayoutOk bs0.length 1 := ⟨⟨hpos0, hpow1, by omega⟩, hal1⟩
    apply sepWP_seq_lscro hcrl0 (mid := lsρ lsRustNoAllocShimSymCli)
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    apply sepWP_seq_lscro hcrl1 (mid := lsρ lsRustAllocSymCli)
    rcases hcrl1 with ⟨hcl1, hro1⟩
    wp_call hshim ()
    refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl2
    apply sepWP_seq_lscro hcrl2 (mid := lsρ memcpyName)
    rcases hcrl2 with ⟨hcl2, hro2⟩
    wp_call halloc (bs0.length, 1, st)
    have hoom : sf_1.readReg64 Reg.x0 ≠ 0#64 := by tauto
    have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
    wp_steps_sync_pool (lsρ memcpyName)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    rintro ⟨hcl3, hro3⟩
    wp_apply using (hmc_any ro0)
    refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
    wp_steps_sync_pool (s0.readReg64 .lr)
    apply SepWP.fold (vecU8_of_pos_placed A outVec (sf_1.readReg64 Reg.x0) bs0 hpos0 hmax hoom)
      (by sep_focus)
    wp_done
  · have hsum_ne0 : bs0.length + bs1.length ≠ 0 := by omega
    simp only [cliConcat2Events, hsum_ne0, ↓reduceIte] at *
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length) == 0#64) = false :=
      ofNat_beq_zero_false_concat_placed (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false :=
      ofNat_beq_zero_false_concat_placed hpos0 h0_lt64
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false :=
      ofNat_beq_zero_false_concat_placed hpos1 h1_lt64
    have hrlay : RustLayoutOk (bs0.length + bs1.length) 1 := ⟨⟨by omega, hpow1, by omega⟩, hal1⟩
    apply sepWP_seq_lscro hcrl0 (mid := lsρ lsRustNoAllocShimSymCli)
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    apply sepWP_seq_lscro hcrl1 (mid := lsρ lsRustAllocSymCli)
    rcases hcrl1 with ⟨hcl1, hro1⟩
    wp_call hshim ()
    refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl2
    apply sepWP_seq_lscro hcrl2 (mid := lsρ memcpyName)
    rcases hcrl2 with ⟨hcl2, hro2⟩
    wp_call halloc (bs0.length + bs1.length, 1, st)
    have hoom : sf_1.readReg64 Reg.x0 ≠ 0#64 := by tauto
    have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
    rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs1.length (by omega)]
    wp_steps_sync_pool (lsρ memcpyName)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    rintro ⟨hcl3, hro3⟩
    wp_apply using (hmc_any ro0)
    refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
    apply sepWP_seq_lscro (mid := lsρ memcpyName) ‹_›
    wp_steps_sync_pool (lsρ memcpyName)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    rintro ⟨hcl4, hro4⟩
    wp_apply using (hmc_any ro1)
    refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
    wp_steps_sync_pool (s0.readReg64 .lr)
    apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs0 bs1).symm)
      (by sep_focus)
    apply SepWP.fold (vecU8_of_append_pos_placed A outVec (sf_1.readReg64 Reg.x0) bs0 bs1
      (by omega) hmax hoom) (by sep_focus)
    wp_done

end Concat2PlacedBudgetHelpers

/-- `<[&[u8]] as Concat<u8>>::concat` (Block `598`) meets budget-threaded
`cliConcat2SpecPlaced M A lim stk`. -/
theorem cliConcat2_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_598 H) (blkPl_598).base
      (cliConcat2SpecPlaced M A lim stk) := by
  refine subroutine_ok_frame_weaken_concat_placed
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliConcatStackPlaced))
    (cliConcat2_exact_placed_ok hA hRO) ?_ ?_
  · intro x s0
    dsimp only [cliConcat2SpecPlaced, withLsCodeRoLoaded, cliConcat2Spec]
    rw [stackAt_split_ge_concat_placed s0.sp hstk hstk64]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro x s0 sf
    dsimp only [cliConcat2SpecPlaced, withLsCodeRoLoaded, cliConcat2Spec]
    rw [stackAt_split_ge_concat_placed s0.sp hstk hstk64]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Cross-block transfer of `cliConcat2_placed_ok` to any caller block `i < 619`
(e.g. `run` at Block `579`). -/
theorem cliConcat2_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [hcaller : IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_598).base
      (cliConcat2SpecPlaced M A lim stk) := by
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_598 H) i 598 H
    hcaller (instIsLsBlockProg_598 H) (blkPl_598).base _
    (cliConcat2_placed_ok hA hRO stk hstk hstk64)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2PlacedBudget
