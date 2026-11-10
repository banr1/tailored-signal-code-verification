/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpers -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.New
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Proof of `<spqr::chain::Chain>::new` (Block `363`)

Proves the `RustCliAllocBudget`-threaded `[LibsignalPlacement]` contract (`chainNew_placed_ok`)
for `<spqr::chain::Chain>::new` (Block `363`) against `chainNewSpecX hkdf M A lim`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.NewBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement lsmpl lsρ blkPC_363 blkPl_363)
open CryptoVerification.LibsignalSpqrV1 (Direction HkdfFn chainStartInfo)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainGhost ChainNewGhost HkdfToSliceGhost VecDequeGrowGhost
  bytesAt bytesAt_false bytesAt_true chainAt chainEpochAlign chainEpochSize
  chainNewStackX chainNewVal hkdfToSliceSpec hkdfToSliceSpqrSpec
)
open CryptoVerification.LibsignalTripleRatchet.Keys.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.ChainProofs.ChainNewFacts (
  cedCells_eq_pointsToBytes cedCells_reframe cells12_entails_memRegion_96
  chainAt_new_intro chainEpochDirectionAt_new_intro chainStartInfo_length
  csel_cedSrc_dir_not csel_cedSrc_switch_not exists_unpack64_of_length_96_split
  hokm_sp_reframe memRegion_32_cells4 memRegion_88_out_split rejoin_stack_chainNewX
  rodata_chainStartInfo_placed stackAt_chainNewX_split tst_dir_toI32
  vecDequeAt_empty_sp_intro vecDequeGrow_post_unpack
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  LsCallInv
  SepWPp.call_allowPanic_lsCallInv_mid rodata_zeros32_placed
  subroutine_ok_withLsCallInv_rodata2_keep withLsCallInv
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  RustCliAllocBudget VmPreserved fitsEvents_append rustAllocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (
  ChainNewEnv VecDequeGrowEnv chainNewEvents chainNewSpecX vecDequeGrowEvents vecDequeGrowSpec
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (
  allocCallPreserved_trans subroutine_ok_allocNoOomWithStack_of_budget
  subroutine_ok_post_entails withAllocVmPreserved
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustAllocNoOomSpecWithStack rustAllocSpecWithStack withStack
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false chainStartInfo_length chainEpochSize
  tst_dir_toI32 csel_cedSrc_dir_not csel_cedSrc_switch_not
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

private def chainNewPostConcrete [LibsignalPlacement] (hkdf : HkdfFn)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    (ChainNewGhost × M.σ) → State → State → SepProp :=
  fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      (lsρ "spqr:.rodata.cst32+0x0" ↦ᵣ List.replicate 32 0#8) ∗
      (lsρ "spqr:.rodata..Lanon.167" ↦ᵣ chainStartInfo) ∗
      (∃∗ G : ChainGhost,
        ⌜G.linksCap = 4#64 ∧ G.linksHead = 0#64⌝ ∗
        chainAt A.repAlloc x.out G (chainNewVal hkdf x.initialKey x.dir x.params)) ∗
      bytesAt x.ikmRO x.ikmA x.initialKey ∗
      A.pool lim (M.stepEvents chainNewEvents st) sf ∗
      stackAt s0.sp chainNewStackX

set_option maxHeartbeats 1600000 in
/-- Relocatable `<spqr::chain::Chain>::new` (Block `363`) meets
`withLsCallInv lsmpl (chainNewSpecX hkdf M A lim)` under `[LibsignalPlacement]`. -/
theorem chainNew_placed_ok [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_hkdf : subroutine_ok ((blkPC_363).rebase (blkPl_363).base H)
      (lsmpl.base 379) (withLsCallInv lsmpl (withAllocVmPreserved (hkdfToSliceSpqrSpec hkdf))))
    (h_grow : subroutine_ok ((blkPC_363).rebase (blkPl_363).base H)
      (lsmpl.base 353) (withLsCallInv lsmpl (vecDequeGrowSpec M A lim)))
    (h_shim : subroutine_ok ((blkPC_363).rebase (blkPl_363).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (h_alloc : subroutine_ok ((blkPC_363).rebase (blkPl_363).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack)) :
    subroutine_ok ((blkPC_363).rebase (blkPl_363).base H) (blkPl_363).base
      (withLsCallInv lsmpl (chainNewSpecX hkdf M A lim)) := by
  have h_alloc_nooom := subroutine_ok_allocNoOomWithStack_of_budget h_alloc
  refine subroutine_ok_withLsCallInv_rodata2_keep rodata_zeros32_placed rodata_chainStartInfo_placed ?_
  refine subroutine_ok_post_entails
    (chainNewPostConcrete hkdf M A lim)
    (fun (x, st) s0 sf => by
      dsimp only [chainNewPostConcrete, chainNewSpecX]
      refine Entails.pure_left fun ⟨htr, hacp⟩ => ?_
      refine sepConj_mono_right (sepConj_mono_right ?_)
      refine Entails.sepExists_right chainNewEvents ?_
      exact Entails.pure_right ⟨htr, hacp, rfl⟩ (Entails.refl _))
    ?_
  wpp_init x_st s0
  rcases x_st with ⟨⟨out, ikmRO, ikmA, initialKey, dir, params⟩, st⟩
  dsimp only [chainNewSpecX] at *
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨‹_›, ‹_›⟩
  have hfits_env : FitsEnv M lim st ChainNewEnv := ‹_›
  have hfits_all : FitsEvents M lim st chainNewEvents := hfits_env chainNewEvents rfl
  let st1 := M.stepEvents (rustAllocEvents 72 1) st
  let st2 := M.stepEvents (rustAllocEvents 32 1) st1
  let st3 := M.stepEvents (rustAllocEvents 72 1) st2
  let st4 := M.stepEvents (rustAllocEvents 32 1) st3
  let st5 := M.stepEvents (rustAllocEvents (4 * chainEpochSize) chainEpochAlign) st4
  simp only [chainNewEvents, vecDequeGrowEvents, ↓reduceIte, List.append_nil,
    List.append_assoc, fitsEvents_append] at hfits_all
  rcases hfits_all with ⟨hfits1, hfits2, hfits3, hfits4, hfits5, hfits6⟩
  have hx0 : s0.readReg64 (.gpr 0#5) = out := ‹_›
  have hx1 : s0.readReg64 (.gpr 1#5) = ikmA := ‹_›
  subst hx0 hx1
  rw [stackAt_chainNewX_split s0.sp, memRegion_88_out_split (s0.readReg64 (.gpr 0#5))]
  sep_elim_exists
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  refine CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts.SepWPp.of_sepWP_lsCallInv
    (mid := lsmpl.base 353) hinv0 ?_
  apply CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts.SepWP.seq_lsCallInv
    (mid := lsmpl.base 379) hinv0
  wp_steps_sync_pool (lsmpl.base 379)
  refine SepWP.fold (cells12_entails_memRegion_96 s0.sp 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  wp_call h_hkdf
    (⟨true, lsρ "spqr:.rodata.cst32+0x0", List.replicate 32 0#8, ikmRO, s0.readReg64 (.gpr 1#5), initialKey,
      true, lsρ "spqr:.rodata..Lanon.167", chainStartInfo, s0.sp - 224#64, 96⟩ : HkdfToSliceGhost)
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  have hstack_sf : stackAt (s0.sp - 224#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 224#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  wp_call h_shim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  wp_call h_alloc_nooom (72, 1, st)
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm_all, hokm_root, hokm_a2b, hokm_b2a⟩ :=
    exists_unpack64_of_length_96_split ‹List.length (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) = 96›
  refine SepWP.fold (Entails.of_eq (hokm_sp_reframe s0.sp hokm_all dir)) (by sep_focus) ?_
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
    rw [‹sf_2.sp = sf_1.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
  wp_call h_shim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by
    rw [‹sf_3.sp = sf_2.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
  wp_call h_alloc_nooom (32, 1, st1)
  refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_4.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
  sep_elim_exists
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt sf_4.sp extHookStack := by
    rw [‹sf_4.sp = sf_3.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
  wp_call h_shim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  have hstack_sf5 : stackAt sf_4.sp extHookStack = stackAt sf_5.sp extHookStack := by
    rw [‹sf_5.sp = sf_4.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf5) (by sep_focus) ?_
  wp_call h_alloc_nooom (72, 1, st2)
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  have hstack_sf6 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by
    rw [‹sf_6.sp = sf_5.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf6) (by sep_focus) ?_
  wp_call h_shim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  have hstack_sf7 : stackAt sf_6.sp extHookStack = stackAt sf_7.sp extHookStack := by
    rw [‹sf_7.sp = sf_6.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf7) (by sep_focus) ?_
  wp_call h_alloc_nooom (32, 1, st3)
  refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_8.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
  sep_elim_exists
  wp_steps_sync_pool (lsmpl.base 353)
  refine SepWP.fold (vecDequeAt_empty_sp_intro A.repAlloc s0.sp) (by sep_focus) ?_
  have hstack_sf8 : stackAt sf_7.sp extHookStack = stackAt sf_8.sp extHookStack := by
    rw [‹sf_8.sp = sf_7.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf8) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv10
  let x_grow : VecDequeGrowGhost := ⟨s0.sp - 128#64, 0#64, 8#64, 0#64, []⟩
  have hfits_grow : FitsEnv M lim st4 (VecDequeGrowEnv x_grow) := by
    intro evs hevs
    rw [hevs]
    simpa [VecDequeGrowEnv, vecDequeGrowEvents, x_grow, st4, st3, st2, st1] using hfits5
  change subroutine_ok _ _ (withLsCallInv lsmpl (vecDequeGrowSpec M A lim)) at h_grow
  apply (SepWPp.call_allowPanic_lsCallInv_mid h_grow (x := (x_grow, st4)) hinv10)
  · wp_norm_goal
  · wp_norm_lhs
  · wp_norm_goal
  · wp_norm_lhs
  · intro R' hmR'
    rw [← sepConj_assoc]
    dsimp only [vecDequeGrowSpec, x_grow, st4]
    refine Satisfies.mono (sepConj_mono_left ?_) hmR'
    simp only [wp_norm, arm64_norm]
    refine Entails.pure_right ⟨rfl, hfits_grow⟩ ?_
    sep_frame
  · intro _; dsimp only [vecDequeGrowSpec]; exact Entails.pure_left False.elim
  · exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  intro sf_9 hpc_sf9 hrun_sf9 hsp_sf9 hcs_sf9 hF_sf9
  dsimp only [vecDequeGrowSpec, x_grow]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro evs_grow
  apply SepWPp.exists_elim; intro ptr_links
  apply SepWPp.exists_elim; intro head_links
  refine CryptoVerification.SpqrV1.ChainProofs.ChainNewFacts.SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htrace_sf9, hacp_sf9, hevs_grow⟩
  have hevs_grow_eq : evs_grow = rustAllocEvents (4 * chainEpochSize) chainEpochAlign := by
    simpa [VecDequeGrowEnv, vecDequeGrowEvents, x_grow] using hevs_grow
  subst hevs_grow_eq
  refine CryptoVerification.SpqrV1.ChainProofs.ChainNewFacts.SepWPp.pure_left_focus _ (by sep_focus) ?_
  intro hhead_eq
  have hhead0 : head_links = 0#64 := hhead_eq trivial
  subst hhead0
  have hsp_sf9' : sf_9.sp = sf_8.sp := by simpa [wp_norm, arm64_norm] using hsp_sf9
  have hcs_sf9_norm := hcs_sf9
  unfold CalleeSavedPreserved at hcs_sf9_norm
  simp only [wp_norm, arm64_norm] at hcs_sf9_norm
  rcases hcs_sf9_norm with ⟨hx19_9, hx20_9, hx21_9, hx22_9, hx23_9, hx24_9,
    hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, hvregs_9⟩
  wp_norm_hyp hpc_sf9; wp_norm_hyp hsp_sf9'; wp_norm_hyp hx19_9; wp_norm_hyp hx20_9
  wp_norm_hyp hx21_9; wp_norm_hyp hx22_9; wp_norm_hyp hx23_9; wp_norm_hyp hx24_9
  wp_norm_hyp hx25_9; wp_norm_hyp hx26_9; wp_norm_hyp hx27_9; wp_norm_hyp hx28_9
  wp_norm_hyp hx29_9; wp_norm_hyp hvregs_9; wp_norm_hyp htrace_sf9
  apply SepWPp.of_sepWP_ret
  refine SepWP.fold (vecDequeGrow_post_unpack A.repAlloc s0.sp ptr_links) (by sep_focus) ?_
  sep_elim_exists
  refine CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts.SepWP.pure_left_focus _ (by sep_focus) ?_
  intro hptr'_ne
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  have hstack_sf9 : stackAt sf_8.sp extHookStack = stackAt sf_9.sp extHookStack := by
    rw [hsp_sf9']
  refine SepWP.fold (Entails.of_eq hstack_sf9) (by sep_focus) ?_
  wp_call h_shim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  have hstack_sf10 : stackAt sf_9.sp extHookStack = stackAt sf_10.sp extHookStack := by
    rw [‹sf_10.sp = sf_9.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf10) (by sep_focus) ?_
  wp_call h_alloc_nooom (32, 1, st5)
  refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_11.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
  sep_elim_exists
  wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
  refine SepWP.fold (Entails.of_eq (cedCells_eq_pointsToBytes hokm_a2b hokm_b2a dir (sf_4.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (cedCells_eq_pointsToBytes hokm_a2b hokm_b2a dir.switch (sf_8.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hokm_root (sf_11.readReg64 (.gpr 0#5))).symm) (by sep_focus) ?_
  have hoom1_64 : sf_2.readReg64 (.gpr 0#5) ≠ 0#64 := ‹_›
  have hoom2_64 : sf_4.readReg64 (.gpr 0#5) ≠ 0#64 := ‹_›
  have hoom3_64 : sf_6.readReg64 (.gpr 0#5) ≠ 0#64 := ‹_›
  have hoom4_64 : sf_8.readReg64 (.gpr 0#5) ≠ 0#64 := ‹_›
  have hoom5_64 : sf_11.readReg64 (.gpr 0#5) ≠ 0#64 := ‹_›
  (conv => arg 4; simp only [← RustCliAllocBudget.repAlloc_live])
  refine SepWP.fold (chainEpochDirectionAt_new_intro A.repAlloc ptr_links (sf_4.readReg64 (.gpr 0#5)) (sf_2.readReg64 (.gpr 0#5)) ‹List.length (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) = 96› dir hoom2_64 hoom1_64) (by sep_focus) ?_
  have hrecv_intro := chainEpochDirectionAt_new_intro A.repAlloc (ptr_links + 56#64) (sf_8.readReg64 (.gpr 0#5)) (sf_6.readReg64 (.gpr 0#5)) ‹List.length (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) = 96› dir.switch hoom4_64 hoom3_64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrecv_intro
  refine SepWP.fold hrecv_intro (by sep_focus) ?_
  refine SepWP.fold (chainAt_new_intro A.repAlloc hkdf (s0.readReg64 (.gpr 0#5)) ptr_links (sf_4.readReg64 (.gpr 0#5)) (sf_2.readReg64 (.gpr 0#5)) (sf_8.readReg64 (.gpr 0#5)) (sf_6.readReg64 (.gpr 0#5)) (sf_11.readReg64 (.gpr 0#5)) initialKey dir params ‹List.length (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) = 96› hptr'_ne hoom5_64) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (cedCells_reframe s0.sp w4 w5 w6 w7 w8 w9 w10 w11 dir).symm) (by sep_focus) ?_
  have hstack_all : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 224#64) extHookStack := by
    rw [← hstack_sf10, ← hstack_sf9, ← hstack_sf8, ← hstack_sf7, ← hstack_sf6, ← hstack_sf5, ← hstack_sf4, ← hstack_sf3, ← hstack_sf2, ← hstack_sf1, ← hstack_sf]
  refine SepWP.fold (Entails.of_eq hstack_all) (by sep_focus) ?_
  refine SepWP.fold (rejoin_stack_chainNewX s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  have hacp_0 : AllocCallPreserved s0 sf := by
    have h := ‹AllocCallPreserved _ sf›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_1 : AllocCallPreserved sf sf_1 := by
    have h := ‹AllocCallPreserved _ sf_1›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_2 : AllocCallPreserved sf_1 sf_2 := by
    have h := ‹AllocCallPreserved _ sf_2›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_3 : AllocCallPreserved sf_2 sf_3 := by
    have h := ‹AllocCallPreserved _ sf_3›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_4 : AllocCallPreserved sf_3 sf_4 := by
    have h := ‹AllocCallPreserved _ sf_4›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_5 : AllocCallPreserved sf_4 sf_5 := by
    have h := ‹AllocCallPreserved _ sf_5›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_6 : AllocCallPreserved sf_5 sf_6 := by
    have h := ‹AllocCallPreserved _ sf_6›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_7 : AllocCallPreserved sf_6 sf_7 := by
    have h := ‹AllocCallPreserved _ sf_7›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_8 : AllocCallPreserved sf_7 sf_8 := by
    have h := ‹AllocCallPreserved _ sf_8›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_9 : AllocCallPreserved sf_8 sf_9 := by
    unfold AllocCallPreserved at hacp_sf9 ⊢; simpa only [wp_norm, arm64_norm] using hacp_sf9
  have hacp_10 : AllocCallPreserved sf_9 sf_10 := by
    have h := ‹AllocCallPreserved _ sf_10›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_11 : AllocCallPreserved sf_10 sf_11 := by
    have h := ‹AllocCallPreserved _ sf_11›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_0_11 : AllocCallPreserved s0 sf_11 :=
    allocCallPreserved_trans
      (allocCallPreserved_trans
        (allocCallPreserved_trans
          (allocCallPreserved_trans
            (allocCallPreserved_trans
              (allocCallPreserved_trans hacp_0 hacp_1)
              (allocCallPreserved_trans hacp_2 hacp_3))
            (allocCallPreserved_trans hacp_4 hacp_5))
          (allocCallPreserved_trans hacp_6 hacp_7))
        (allocCallPreserved_trans hacp_8 hacp_9))
      (allocCallPreserved_trans hacp_10 hacp_11)
  have htr_11 : sf_11.trace = s0.trace := hacp_0_11.2.1
  wp_norm_hyp htr_11
  have hpool_eq :
      M.stepEvents (rustAllocEvents 32 1) st5 =
        M.stepEvents chainNewEvents st := by
    dsimp only [st5, st4, st3, st2, st1]
    simp only [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append,
      chainNewEvents, List.append_assoc]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨?_, by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal⟩
  intro hmR
  dsimp only [chainNewPostConcrete]
  refine Satisfies.mono (sepConj_mono_left ?_) hmR
  rw [hpool_eq]
  try simp only [sepConj_assoc]
  refine Entails.pure_right
    ⟨by wp_norm_goal, by unfold AllocCallPreserved at hacp_0_11 ⊢; simpa only [wp_norm, arm64_norm] using hacp_0_11⟩ ?_
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Chain.NewBudget
