/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpers -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Proof of `<ChainEpochDirection>::next_key_internal` (Block `362`)

Proves the `RustCliAllocBudget`-threaded `[LibsignalPlacement]` contract
(`nextKeyInternal_placed_ok`) for `<spqr::chain::ChainEpochDirection>::next_key_internal`
(Block `362`) against `nextKeyInternalSpecX hkdf M A lim`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification (LibsignalPlacement lsmpl lsρ blkPC_362 blkPl_362)
open CryptoVerification.LibsignalSpqrV1 (ChainEpochDirection HkdfFn chainNextInfo)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SpqrV1.ChainProofs (
  HkdfToSliceGhost NextKeyInternalGhost SliceConcat2Ghost
  bytesAt_false bytesAt_true exists_unpack64_of_length_64_split hkdfToSliceSpec
  hkdfToSliceSpqrSpec nextKeyNext nextKeyOut nextKeyOutAt
)
open CryptoVerification.LibsignalTripleRatchet.Keys.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  LsCallInv
  SepWPp.call_allowPanic_lsCallInv_ret
  cells8_entails_memRegion_64 chainNextInfo_length memRegion_36_out_split
  onPanic_entails_of_trace_eq pointsTo32_rev32_eq_toBEBytes pointsToBytes_memRegion_entails
  rejoin_stack_nextKeyInternalX rodata_chainNextInfo_placed rodata_zeros32_placed
  stackAt_nextKeyInternalX_split subroutine_ok_withLsCallInv_rodata2_keep toBEBytes_4_length
  vecU8_nonempty_entails withLsCallInv
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEnv FitsEvents NullAllowed
  RustCliAllocBudget VmPreserved fitsEvents_append not_nullAllowed_of_fitsAllocEvents
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliAllocNoOomSpecWithStack
  rustCliDeallocBudgetSpecWithStack
)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (
  NextKeyInternalEnv SliceConcat2Env nextKeyInternalEvents nextKeyInternalSpecX
  sliceConcat2Events sliceConcat2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustAllocNoOomSpecWithStack rustAllocSpecWithStack rustDeallocSpecWithStack
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_4_length chainNextInfo_length List.length_append
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h01 : AllocCallPreserved s0 s1) (h12 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

/-- Strengthen a pure/crypto non-allocating `Spec α` with `AllocCallPreserved s0 sf ∧ VmPreserved s0 sf`
so both `AllocCallPreserved` and `A.pool lim st` transport across the call. -/
def withAllocVmPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    post := fun x s0 sf => ⌜AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗ spec.post x s0 sf }

/-- Specialize conditional-OOM `rustAllocSpecWithStack` to total-correctness
`rustAllocNoOomSpecWithStack` whenever `FitsEvents` holds at the call site. -/
theorem subroutine_ok_allocNoOomWithStack_of_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    {zeroed : Bool} {stk : Nat}
    (h : subroutine_ok P entry (rustAllocSpecWithStack M A lim zeroed stk)) :
    subroutine_ok P entry (rustAllocNoOomSpecWithStack M A lim zeroed stk) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨size, align, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlay, hFit, hlr⟩, hrest⟩
  have hpreB : s0.mem ⊨ (rustAllocSpecWithStack M A lim zeroed stk).pre (size, align, st) s0 ∗ R := by
    dsimp only [rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay, hlr⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (size, align, st) R s0 hpc hrun hpreB hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack] at hpost
    by_cases hnull : sf.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hna : NullAllowed size align := by
        have hEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
              stackAt s0.sp stk ∗ ⌜NullAllowed size align⌝) ∗ R =
            ⌜NullAllowed size align⌝ ∗
              (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
                stackAt s0.sp stk ∗ R) := by sep_ac_rfl
        rw [hEq, satisfies_pure_sepConj] at hpost
        exact hpost.1
      exact False.elim (not_nullAllowed_of_fitsAllocEvents hlay hFit hna)
    · simp only [hnull, ↓reduceIte] at hpost
      dsimp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack]
      have hEq1 :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt s0.sp stk ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) size align ∗
              (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
               else memRegion (sf.readReg64 .x0) size))) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
              (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
                stackAt s0.sp stk ∗ A.live (sf.readReg64 .x0) size align ∗
                (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
                 else memRegion (sf.readReg64 .x0) size) ∗ R)) := by sep_ac_rfl
      rw [hEq1, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hacp, hpost⟩
      rw [satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hal, hspRest⟩
      have hne0 : sf.readReg64 .x0 ≠ 0#64 := hnull
      have hEq2 :
          (⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % align = 0⌝ ∗
            A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt s0.sp stk ∗ A.live (sf.readReg64 .x0) size align ∗
            (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
             else memRegion (sf.readReg64 .x0) size)) ∗ R =
          ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt s0.sp stk ∗ A.live (sf.readReg64 .x0) size align ∗
              (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
               else memRegion (sf.readReg64 .x0) size) ∗ R) := by sep_ac_rfl
      rw [hEq2, satisfies_pure_sepConj]
      exact ⟨⟨hacp, hne0, hal⟩, hspRest⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · dsimp only [rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hFit)

/-- Strengthen the normal-return `post` of a `Spec` by an entailment before `wpp_init` / `wp_init`,
so deterministic `∃∗ evs` envelopes are instantiated up front without triggering `wpp_init`'s
existential expansion over `stackAt`. -/
theorem subroutine_ok_post_entails {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (post' : α → State → State → SepProp)
    (hpost : ∀ x s0 sf, post' x s0 sf ⊢ spec.post x s0 sf)
    (h : subroutine_ok prog entry { spec with post := post' }) :
    subroutine_ok prog entry spec := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hm hsp _ => ?_
  refine h.mono_outcome x R s0 hpc hrun hm hsp fun sf hout => ?_
  rcases hout with ⟨h1, h2, hp⟩ | ⟨h1, hp⟩ | ⟨c, h1, hp⟩ | ⟨h1, hp⟩
  · exact Or.inl ⟨h1, h2, Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hp⟩
  · exact Or.inr (Or.inl ⟨h1, hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, h1, hp⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, hp⟩))

private def nextKeyInternalPostConcrete [LibsignalPlacement] (hkdf : HkdfFn)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    (NextKeyInternalGhost × M.σ) → State → State → SepProp :=
  fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      (lsρ "spqr:.rodata..Lanon.161" ↦ᵣ chainNextInfo) ∗
      (lsρ "spqr:.rodata.cst32+0x0" ↦ᵣ List.replicate 32 0#8) ∗
      nextKeyOutAt x.out (x.ctr + 1#32) (nextKeyOut hkdf x.next x.ctr) ∗
      (x.nextA ↦ₛ nextKeyNext hkdf x.next x.ctr) ∗
      (x.ctrA ↦₃₂ (x.ctr + 1#32)) ∗
      A.pool lim (M.stepEvents nextKeyInternalEvents st) sf ∗
      stackAt s0.sp CryptoVerification.SpqrV1.ChainProofs.nextKeyInternalStackX

set_option maxHeartbeats 1600000 in
/-- Relocatable `<spqr::chain::ChainEpochDirection>::next_key_internal` (Block `362`) meets
`withLsCallInv lsmpl (nextKeyInternalSpecX hkdf M A lim)` under `[LibsignalPlacement]`. -/
theorem nextKeyInternal_placed_ok [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_concat : subroutine_ok ((blkPC_362).rebase (blkPl_362).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat2Spec M A lim)))
    (h_hkdf : subroutine_ok ((blkPC_362).rebase (blkPl_362).base H)
      (lsmpl.base 379) (withLsCallInv lsmpl (withAllocVmPreserved (hkdfToSliceSpqrSpec hkdf))))
    (h_dealloc : subroutine_ok ((blkPC_362).rebase (blkPl_362).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpecWithStack M A lim extHookStack)) :
    subroutine_ok ((blkPC_362).rebase (blkPl_362).base H) (blkPl_362).base
      (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf M A lim)) := by
  refine subroutine_ok_withLsCallInv_rodata2_keep
    rodata_chainNextInfo_placed rodata_zeros32_placed ?_
  refine subroutine_ok_post_entails
    (nextKeyInternalPostConcrete hkdf M A lim)
    (fun (x, st) s0 sf => by
      dsimp only [nextKeyInternalPostConcrete, nextKeyInternalSpecX]
      refine Entails.pure_left fun ⟨htr, hacp⟩ => ?_
      refine sepConj_mono_right (sepConj_mono_right ?_)
      refine Entails.sepExists_right nextKeyInternalEvents ?_
      exact Entails.pure_right ⟨htr, hacp, rfl⟩ (Entails.refl _))
    ?_
  wpp_init x_st s0
  rcases x_st with ⟨⟨out, nextA, next, ctrA, ctr⟩, st⟩
  dsimp only [nextKeyInternalSpecX] at *
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨‹_›, ‹_›⟩
  have hfits_env : FitsEnv M lim st NextKeyInternalEnv := ‹_›
  have hfits_all : FitsEvents M lim st nextKeyInternalEvents := hfits_env nextKeyInternalEvents rfl
  rw [nextKeyInternalEvents, fitsEvents_append] at hfits_all
  rcases hfits_all with ⟨hfits_alloc, hfits_dealloc⟩
  have hx0 : s0.readReg64 (.gpr 0#5) = out := ‹_›
  have hx1 : s0.readReg64 (.gpr 1#5) = nextA := ‹_›
  have hx3 : s0.readReg64 (.gpr 3#5) = ctrA := ‹_›
  subst hx0 hx1 hx3
  rw [stackAt_nextKeyInternalX_split s0.sp,
    memRegion_36_out_split (s0.readReg64 (.gpr 0#5))]
  sep_elim_exists
  refine CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts.SepWPp.of_sepWP_lsCallInv
    (mid := lsmpl.base 386) hinv0 ?_
  wp_steps_sync_pool (lsmpl.base 386)
  refine SepWP.fold (Entails.of_eq (pointsTo32_rev32_eq_toBEBytes (s0.sp - 52#64) (ctr + 1#32))) (by sep_focus) ?_
  refine SepWP.fold (cells8_entails_memRegion_64 s0.sp 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  let x_concat : SliceConcat2Ghost :=
    ⟨s0.sp - 112#64, s0.sp - 88#64, false, s0.sp - 52#64, toBEBytes 4 (ctr + 1#32),
      true, lsρ "spqr:.rodata..Lanon.161", chainNextInfo⟩
  have hfits_concat : FitsEnv M lim st (SliceConcat2Env x_concat) := by
    intro evs hevs
    rw [hevs]
    simpa [SliceConcat2Env, sliceConcat2Events, x_concat] using hfits_alloc
  change subroutine_ok _ _ (withLsCallInv lsmpl (sliceConcat2Spec M A lim)) at h_concat
  apply (SepWPp.call_allowPanic_lsCallInv_ret h_concat (x := (x_concat, st)) hinv1)
  · wp_norm_goal
  · wp_norm_lhs
  · wp_norm_goal
  · wp_norm_lhs
  · intro R' hmR'
    rw [← sepConj_assoc]
    refine Satisfies.mono (sepConj_mono_left ?_) hmR'
    dsimp only [sliceConcat2Spec, x_concat]
    simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false, toBEBytes_4_length, chainNextInfo_length,
      sepConj_assoc, wp_norm, arm64_norm]
    refine Entails.pure_right hfits_concat ?_
    sep_frame
  · intro _; dsimp only [sliceConcat2Spec]; exact Entails.pure_left False.elim
  · exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf hF_sf
  dsimp only [sliceConcat2Spec, x_concat]
  simp only [toBEBytes_4_length, chainNextInfo_length, Nat.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro evs_concat
  apply SepWP.exists_elim; intro ptr_info
  refine CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts.SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htrace_sf, hacp_sf, hevs_concat⟩
  have hevs_concat_eq : evs_concat = rustAllocEvents (4 + chainNextInfo.length) 1 := by
    simpa [SliceConcat2Env, sliceConcat2Events, x_concat] using hevs_concat
  subst hevs_concat_eq
  dsimp only [CryptoVerification.RustHeap.vecU8At, CryptoVerification.RustHeap.vecHeader]
  simp (config := { decide := true }) only [
    List.length_append, toBEBytes_4_length, chainNextInfo_length, Nat.reduceAdd,
    BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.sub_self, memRegion_zero, sepConj_emp,
    ite_false, bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
  refine CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts.SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨_, _, hptr_ne⟩
  have hsp_sf' : sf.sp = s0.sp - 176#64 := by simpa [wp_norm, arm64_norm] using hsp_sf
  have hcs_sf_norm := hcs_sf
  unfold CalleeSavedPreserved at hcs_sf_norm
  simp only [wp_norm, arm64_norm] at hcs_sf_norm
  rcases hcs_sf_norm with ⟨hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf,
    hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩
  wp_norm_hyp hpc_sf; wp_norm_hyp hsp_sf'; wp_norm_hyp hx19_sf; wp_norm_hyp hx20_sf
  wp_norm_hyp hx21_sf; wp_norm_hyp hx22_sf; wp_norm_hyp hx23_sf; wp_norm_hyp hx24_sf
  wp_norm_hyp hx25_sf; wp_norm_hyp hx26_sf; wp_norm_hyp hx27_sf; wp_norm_hyp hx28_sf
  wp_norm_hyp hx29_sf; wp_norm_hyp hvregs_sf; wp_norm_hyp htrace_sf
  apply CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts.SepWP.seq_lsCallInv
    (mid := lsmpl.base 379) hF_sf
  wp_steps_sync_pool (lsmpl.base 379)
  have hstack_sf : stackAt (s0.sp - 176#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [hsp_sf']
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  have ⟨hro2, hcl2⟩ := hinv2
  have hnext_lt : next.length < 2 ^ 63 := by omega
  have hinfo_ge : 32 ≤ (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo).length := by simp
  have hinfo_lt : (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo).length < 55 := by simp
  have hinfo_len64 : 35#64 = BitVec.ofNat 64 (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo).length := by
    simp [toBEBytes_4_length, chainNextInfo_length]
  wp_call h_hkdf
    (⟨true, lsρ "spqr:.rodata.cst32+0x0", List.replicate 32 0#8,
      false, s0.readReg64 (.gpr 1#5), next,
      false, ptr_info, toBEBytes 4 (ctr + 1#32) ++ chainNextInfo,
      s0.sp - 176#64, 64⟩ : HkdfToSliceGhost)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  have hmr35 :
      (ptr_info ↦ₛ (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo)) ⊢ memRegion ptr_info 35 := by
    simpa only [List.length_append, toBEBytes_4_length, chainNextInfo_length, Nat.reduceAdd] using
      pointsToBytes_entails_memRegion ptr_info (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo)
  refine SepWP.fold hmr35 (by sep_focus) ?_
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  wp_call h_dealloc (ptr_info, 35, 1, _)
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hokm_all, hokm_take, hokm_drop⟩ :=
    exists_unpack64_of_length_64_split ‹List.length (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64) = 64›
  obtain ⟨n0, n1, n2, n3, -, hnext_cells⟩ := exists_unpack64_of_length_32 ‹next.length = 32›
  have hokm_sp := hokm_all (s0.sp - 176#64)
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hokm_sp
  refine SepWP.fold (Entails.of_eq hokm_sp) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hnext_cells (s0.readReg64 (.gpr 1#5)))) (by sep_focus) ?_
  wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
  have hokm_out := (hokm_drop (s0.readReg64 (.gpr 0#5) + 4#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hokm_out
  refine SepWP.fold (Entails.of_eq hokm_out) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hokm_take (s0.readReg64 (.gpr 1#5))).symm) (by sep_focus) ?_
  have hstack_back : stackAt sf_1.sp extHookStack = stackAt (s0.sp - 176#64) extHookStack := by
    rw [← hstack_sf1, ← hstack_sf]
  refine SepWP.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
  have hbe_len : (toBEBytes 4 (ctr + 1#32)).length = 4 := by simp
  refine SepWP.fold (rejoin_stack_nextKeyInternalX s0.sp w0 w1 w2 w3 w4 w5 w6 w7 _ _ _ _ _ _ _ hbe_len _ _ _ _ _ _) (by sep_focus) ?_
  have hkey_len :
      (List.take 32
        (List.drop 32
          (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64))).length = 32 := by
    rw [List.length_take_of_le (by
      rw [List.length_drop, ‹List.length (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64) = 64›])]
  have hacp_0 : AllocCallPreserved s0 sf := by
    simpa only [wp_norm, arm64_norm] using hacp_sf
  have hacp_1 : AllocCallPreserved sf sf_1 := by
    simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›
  have hacp_2 : AllocCallPreserved sf_1 sf_2 := by
    simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›
  have hacp_02 : AllocCallPreserved s0 sf_2 :=
    allocCallPreserved_trans (allocCallPreserved_trans hacp_0 hacp_1) hacp_2
  have htr_02 : sf_2.trace = s0.trace := hacp_02.2.1
  wp_norm_hyp htr_02
  have hpool_eq :
      M.stepEvents (rustDeallocEvents 35 1) (M.stepEvents (rustAllocEvents 35 1) st) =
        M.stepEvents nextKeyInternalEvents st := by
    rw [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    simp only [nextKeyInternalEvents, chainNextInfo_length]
  rw [hpool_eq]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨?_, by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal⟩
  intro hmR
  dsimp only [nextKeyInternalPostConcrete, nextKeyOutAt, nextKeyOut, nextKeyNext,
    ChainEpochDirection.nextKeyInternal]
  refine Satisfies.mono (sepConj_mono_left ?_) hmR
  simp only [sepConj_assoc]
  refine Entails.pure_right
    ⟨by wp_norm_goal, by simpa only [wp_norm, arm64_norm] using hacp_02⟩ ?_
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
