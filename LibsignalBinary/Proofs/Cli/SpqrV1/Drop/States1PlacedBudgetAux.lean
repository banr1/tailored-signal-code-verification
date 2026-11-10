/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Chunked `States` Drop Glue (Block `443`, Part 2/2)

Proves the remaining five variant contracts (`ct2Sampled`, `headerSent`, `ct1Received`,
`keysSampled`, `ekReceivedCt1Sampled`) and their `HookSat` / `withPanics` wrappers on Block `443`
(`lsProg_443 H`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1PlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement
  ls_subroutine_ok_cl_of_plain lsmpl lsρ
  withLsCl withLsCodeLoaded
)
open CryptoVerification.Cli.SpqrV1.Drop (
  chunkedStatesLocal1JumpTablePlacedAt
  chunkedStatesLocal1JumpTablePlacedExpanded
)
open CryptoVerification.Cli.SpqrV1.Drop.Placed (
  blkPl_440 blkPl_441 lsProg_440 lsProg_441
)
open CryptoVerification.Cli.SpqrV1.Drop.TopPlaced (blkPC_443 blkPl_443 lsProg_443)
open CryptoVerification.LibsignalSpqrV1 (NUM_POLYS PolyEncoder Pt States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct2Sampled EkReceivedCt1Sampled)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (Ct1Received HeaderSent KeysSampled)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (
  FiveVecGhost FourVecGhost Saved32x19Preserved
  chunkedCt1ReceivedAt chunkedCt2SampledAt chunkedEkReceivedCt1SampledAt
  chunkedHeaderSentAt chunkedKeysSampledAt
  chunkedStatesAt chunkedStatesSize
  dropGluePoly16Stack dropStack32 dropStackPoly64
  fiveVec408HeadersAt fiveVec408HeadersAt_entails_memRegion_128
  fourVec408HeadersAt fourVec408HeadersAt_entails_memRegion_104
  polyDecoderAt_entails_vecs_tail polyDecoder_post_join
  stackAt_dropStack32_split_sub32 stackAt_dropStackPoly64_split_bottom
  stack_restore_64_dropStack32
  tag_and_two_regions_entails_928
  threeVec408HeadersAt threeVec408HeadersAt_entails_memRegion_80
  twoVec408HeadersAt twoVec408HeadersAt_entails_memRegion_56
  unchunkedCt1Sent408_entails_dealloc unchunkedCt1SentEkReceivedAt
  unchunkedCt2Sent408_entails_dealloc unchunkedEkSent408_entails_dealloc
  unchunkedEkSentCt1Received408_entails_dealloc unchunkedHeaderSentAt
  unchunkedHeaderSentToEkSentCt1Received
  vecCapPtrDealloc vecPtListOf
)
open CryptoVerification.SpqrV1.Poly (
  polyArrayBytes polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.PolyDecoderPlacedBudget (drop_poly_decoder_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.PolyEncoderPlacedBudget (
  drop_poly_encoder_local1_placed
)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget (
  dropChunkedStatesLocal1PlacedVariantSpec
  enter_chunked_states_prologue_lscl
  hookSat_dealloc_withPanics
  seq_evs_step_lscl
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget (dropGluePolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.States1aBudget (
  align_pre_st deallocFreeOnlySpec savedFrame32
  sepWP_evs_dealloc sepWP_evs_nil sepWP_evs_of
  subroutine_ok_deallocFreeOnly
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section PlacedStates1BudgetAux
variable [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
  {lim : BudgetLimits} {F : ShaCompress} {H : String → Option (State → State)}

/-! ## 1. Shared `+696` PolyEncoder Tail-Call & `+88` Four-Vec Dealloc Helpers -/

private theorem tail_call_696_polyEncoder_lscl
    (henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec M A lim)))
    {s0 sk : State} {stk : M.σ} {a v_x19 tag tailOff : BitVec 64}
    {enc : PolyEncoder} {midSz tailSz : Nat}
    (hcl : LibsignalCodeLoaded lsmpl sk.mem)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr))
    (hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true)
    (hpc : sk.pc = (blkPl_443).base + 696#64)
    (hrun : sk.status = .Running)
    (hpres : Saved32x19Preserved s0 sk (s0.sp - 32#64))
    (hacp : AllocCallPreserved s0 sk)
    (hx19 : sk.readReg64 .x19 = a)
    (hmid_lt : 400 + midSz < 2 ^ 64)
    (htail_off : a + tailOff = (a + 8#64) + BitVec.ofNat 64 (400 + midSz))
    (hsum928 : 8 + (400 + midSz) + tailSz = 928) :
    SepWP (lsProg_443 H) (s0.readReg64 .lr) sk
      (((a ↦₆₄ tag) ∗ polyEncoderAt A.repAlloc (a + 8#64) enc ∗
          memRegion (a + 408#64) midSz ∗ memRegion (a + tailOff) tailSz) ∗
        chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool lim stk sk ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
        savedFrame32 s0 v_x19)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ memRegion a 928 ∗ chunkedStatesLocal1JumpTablePlacedExpanded ∗
            A.pool lim (M.stepEvents evs stk) sf ∗ stackAt s0.sp dropStackPoly64) ∧
          (sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf)) := by
  have _ := hcl
  dsimp only [withLsCl, dropGluePolyEncoderSpec, polyEncoderSize, dropGluePoly16Stack] at henc_cl
  rcases hpres with ⟨hx20_k, hx21_k, hx22_k, hx23_k, hx24_k, hx25_k, hx26_k, hx27_k, hx28_k, hsp_k, htrace_k, hvregs_k⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  dsimp only [savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
  wp_steps_lscl (lsmpl.base 441)
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call henc_cl (⟨a + 8#64, enc⟩, stk)
  have hacp_f : AllocCallPreserved s0 sf := hacp.trans (by assumption)
  have hevs_w : FreeOnlyEvs w := by assumption
  rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  have hjoin_mid : memRegion (a + 8#64) 400 ∗ memRegion (a + 408#64) midSz ⊢
      memRegion (a + 8#64) (400 + midSz) := by
    have h408 : (a + 8#64) + 400#64 = a + 408#64 := BitVec.add_assoc a 8#64 400#64
    rw [← h408, ProofLib.memRegion_split (a + 8#64) 400 midSz (Nat.le_of_lt hmid_lt)]
    exact Entails.refl _
  refine SepWP.focus_weaken hjoin_mid (by sep_focus) ?_
  have hjoin928 := tag_and_two_regions_entails_928 a tag (400 + midSz) tailSz tailOff htail_off (by omega)
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
  apply sepWP_evs_of w hevs_w
  wp_done

private theorem step_88_fourVec_tail_lscl
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec M A lim)))
    {s0 s1 : State} {st1 : M.σ} {a v_x19 tag : BitVec 64}
    {enc : PolyEncoder} {g : FourVecGhost}
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr))
    (hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (blkPl_443).base + 88#64)
    (hrun1 : s1.status = .Running)
    (hpres1 : Saved32x19Preserved s0 s1 (s0.sp - 32#64))
    (hacp1 : AllocCallPreserved s0 s1)
    (hx19_1 : s1.readReg64 .x19 = a) :
    SepWP (lsProg_443 H) (s0.readReg64 .lr) s1
      (((a ↦₆₄ tag) ∗ polyEncoderAt A.repAlloc (a + 8#64) enc ∗
          (fourVec408HeadersAt a g ∗
            vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
            vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
            vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr) ∗
          memRegion (a + 512#64) 416) ∗
        chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool lim st1 s1 ∗
        (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        savedFrame32 s0 v_x19)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ memRegion a 928 ∗ chunkedStatesLocal1JumpTablePlacedExpanded ∗
            A.pool lim (M.stepEvents evs st1) sf ∗ stackAt s0.sp dropStackPoly64) ∧
          (sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc; simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  rcases hpres1 with ⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp1
  refine seq_evs_step_lscl hcl1 (mid := (blkPl_443).base + 108#64)
    (P_mid := fun st2 sm =>
      ((a ↦₆₄ tag) ∗ polyEncoderAt A.repAlloc (a + 8#64) enc ∗
        (fourVec408HeadersAt a g ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr) ∗
        memRegion (a + 512#64) 416) ∗
      chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool lim st2 sm ∗
      (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [fourVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hc2 : (g.v2.cap == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v2.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_1]
      have hacp' : AllocCallPreserved s0 sf := hacp1.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st2 s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp2, hx19_2⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp2
    refine seq_evs_step_lscl hcl2 (mid := (blkPl_443).base + 128#64)
      (P_mid := fun st3 sm =>
        ((a ↦₆₄ tag) ∗ polyEncoderAt A.repAlloc (a + 8#64) enc ∗
          (fourVec408HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr) ∗
          memRegion (a + 512#64) 416) ∗
        chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool lim st3 sm ∗
        (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        savedFrame32 s0 v_x19)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [fourVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc3 : (g.v3.cap == 0#64) = true <;>
        simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · apply sepWP_evs_dealloc g.v3.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_2]
        have hacp' : AllocCallPreserved s0 sf := hacp2.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · intro st3 s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp3, hx19_3⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp3
      refine seq_evs_step_lscl hcl3 (mid := (blkPl_443).base + 696#64)
        (P_mid := fun st4 sm =>
          ((a ↦₆₄ tag) ∗ polyEncoderAt A.repAlloc (a + 8#64) enc ∗
            memRegion (a + 408#64) 104 ∗ memRegion (a + 512#64) 416) ∗
          chunkedStatesLocal1JumpTablePlacedExpanded ∗
          A.pool lim st4 sm ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
          savedFrame32 s0 v_x19)
        (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · have hhdr104 := fourVec408HeadersAt_entails_memRegion_104 a g
        dsimp only [fourVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hhdr104 ⊢
        by_cases hc4 : (g.v4.cap == 0#64) = true <;>
          simp only [hc4, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps
          refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · apply sepWP_evs_dealloc g.v4.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_3]
          have hacp' : AllocCallPreserved s0 sf := hacp3.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · intro st4 s4 hpc4 hrun4 hcl4 ⟨hpres4, hacp4, hx19_4⟩
        exact tail_call_696_polyEncoder_lscl henc_cl hcl4 hlr_ls hfsp_align hpc4 hrun4 hpres4 hacp4 hx19_4
          (by decide) (BitVec.add_assoc a 8#64 504#64).symm rfl

/-! ## 2. Relocatable `[LibsignalPlacement]` Variant Proofs (Part 2/2: 5 Variants) -/

/-- Variant `ct2Sampled` (`tag = 12#64` -> `+560` -> dealloc 2 Vecs -> `+696` tail-call Block `441`). -/
theorem drop_chunked_states_local1_ct2Sampled_placed_ok
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (henc : subroutine_ok (lsProg_441 H) (blkPl_441).base (dropGluePolyEncoderSpec M A lim))
    (st_v : Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.ct2Sampled st_v))) := by
  have henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec M A lim)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) henc
  simp only [withLsCodeLoaded, dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc henc; simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_prologue_lscl ‹_› (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedCt2SampledAt, spqrPolyApi]
  refine SepWP.focus_weaken (unchunkedCt2Sent408_entails_dealloc A.repAlloc a st_v.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_evs_step_lscl hcl0 (mid := (blkPl_443).base + 580#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 12#64) ∗ polyEncoderAt A.repAlloc (a + 8#64) st_v.sending_ct2 ∗
        (twoVec408HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
        memRegion (a + 464#64) 464) ∗
      chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [twoVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_0]
      have hacp' : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    refine seq_evs_step_lscl hcl1 (mid := (blkPl_443).base + 696#64)
      (P_mid := fun st2 sm =>
        ((a ↦₆₄ 12#64) ∗ polyEncoderAt A.repAlloc (a + 8#64) st_v.sending_ct2 ∗
          memRegion (a + 408#64) 56 ∗ memRegion (a + 464#64) 464) ∗
        chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool lim st2 sm ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
        savedFrame32 s0 v_x19)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · have hhdr56 := twoVec408HeadersAt_entails_memRegion_56 a g
      dsimp only [twoVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hhdr56 ⊢
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · apply sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · intro st2 s2 hpc2 hrun2 hcl2 ⟨hpres2, hacp2, hx19_2⟩
      exact tail_call_696_polyEncoder_lscl henc_cl hcl2 (by assumption) hfsp_align hpc2 hrun2 hpres2 hacp2 hx19_2
        (by decide) (BitVec.add_assoc a 8#64 456#64).symm rfl

/-- Variant `headerSent` (`tag = 4#64`, jump index `2` -> `+312` -> dealloc 3 Vecs -> `bl` Block `441` -> tail-call Block `440`). -/
theorem drop_chunked_states_local1_headerSent_placed_ok
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (henc : subroutine_ok (lsProg_441 H) (blkPl_441).base (dropGluePolyEncoderSpec M A lim))
    (hdec : subroutine_ok (lsProg_440 H) (blkPl_440).base (dropGlueSortedSetPt16Spec M A lim))
    (st_v : HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.headerSent st_v))) := by
  have henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec M A lim)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) henc
  have hdec_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 440)
      (withLsCl lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) hdec
  simp only [withLsCodeLoaded, dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc henc hdec; simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withLsCl, dropGluePolyEncoderSpec, dropGlueSortedSetPt16Spec,
    polyEncoderSize, polyArrayBytes, dropGluePoly16Stack] at henc_cl hdec_cl
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_prologue_lscl ‹_› (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedHeaderSentAt, spqrPolyApi]
  refine SepWP.focus_weaken (unchunkedEkSent408_entails_dealloc A.repAlloc a st_v.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  have hdec488 : polyDecoderAt A.repAlloc (a + 488#64) st_v.receiving_ct1 ⊢
      ∃∗ vecs : List (List Pt),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        vecPtListOf A.repAlloc (a + 488#64) vecs ∗
        memRegion (a + 872#64) 16 := by
    refine Entails.trans (polyDecoderAt_entails_vecs_tail A.repAlloc (a + 488#64) st_v.receiving_ct1) ?_
    apply Entails.sepExists_elim; intro vecs
    refine Entails.sepExists_right vecs ?_
    rw [BitVec.add_assoc a 488#64 384#64]
    exact Entails.refl _
  refine SepWP.focus_weaken hdec488 (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_evs_step_lscl hcl0 (mid := (blkPl_443).base + 332#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 4#64) ∗ polyEncoderAt A.repAlloc (a + 8#64) st_v.sending_ek ∗
        (threeVec408HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
         vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
        vecPtListOf A.repAlloc (a + 488#64) vecs ∗ memRegion (a + 872#64) 16 ∗
        memRegion (a + 888#64) 40) ∗
      chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [threeVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_0]
      have hacp' : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    refine seq_evs_step_lscl hcl1 (mid := (blkPl_443).base + 352#64)
      (P_mid := fun st2 sm =>
        ((a ↦₆₄ 4#64) ∗ polyEncoderAt A.repAlloc (a + 8#64) st_v.sending_ek ∗
          (threeVec408HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
          vecPtListOf A.repAlloc (a + 488#64) vecs ∗ memRegion (a + 872#64) 16 ∗
          memRegion (a + 888#64) 40) ∗
        chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool lim st2 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        savedFrame32 s0 v_x19)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [threeVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · apply sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · intro st2 s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      refine seq_evs_step_lscl hcl2 (mid := (blkPl_443).base + 372#64)
        (P_mid := fun st3 sm =>
          ((a ↦₆₄ 4#64) ∗ polyEncoderAt A.repAlloc (a + 8#64) st_v.sending_ek ∗
            memRegion (a + 408#64) 80 ∗
            vecPtListOf A.repAlloc (a + 488#64) vecs ∗ memRegion (a + 872#64) 16 ∗
            memRegion (a + 888#64) 40) ∗
          chunkedStatesLocal1JumpTablePlacedExpanded ∗
          A.pool lim st3 sm ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
          savedFrame32 s0 v_x19)
        (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · have hhdr80 := threeVec408HeadersAt_entails_memRegion_80 a g
        dsimp only [threeVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hhdr80 ⊢
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · apply sepWP_evs_dealloc g.v3.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_2]
          have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · intro st3 s3 hpc3 hrun3 _hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_3
        dsimp only [savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
        wp_steps_lscl (lsmpl.base 441)
        have hsplit_enc_stk : stackAt (s0.sp - 32#64) dropStack32 = stackAt s3.sp dropGluePoly16Stack := by
          rw [hsp_3]
        refine SepWP.focus_weaken (Entails.of_eq hsplit_enc_stk) (by sep_focus) ?_
        wp_call henc_cl (⟨a + 8#64, st_v.sending_ek⟩, st3)
        have hacp_4 : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
        have hevs1 : FreeOnlyEvs w := by assumption
        have hsp_sf : sf.sp = s3.sp := by assumption
        wp_steps_lscl (lsmpl.base 440)
        have hsp_eq : stackAt s3.sp dropGluePoly16Stack = stackAt (s0.sp - 32#64) dropStack32 := by
          rw [hsp_3]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x19) v_x19)
          (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
        wp_call hdec_cl (⟨a + 488#64, vecs⟩, M.stepEvents w st3)
        have hacp_f : AllocCallPreserved s0 sf_1 := hacp_4.trans (by assumption)
        have hevs2 : FreeOnlyEvs w_1 := by assumption
        rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
        rw [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
        have hjoin488 : memRegion (a + 488#64) 384 ∗ memRegion (a + 872#64) 16 ⊢
            memRegion (a + 488#64) polyDecoderSize := by
          have h872 : a + 872#64 = (a + 488#64) + 384#64 := (BitVec.add_assoc a 488#64 384#64).symm
          rw [h872]
          exact polyDecoder_post_join (a + 488#64)
        refine SepWP.focus_weaken hjoin488 (by sep_focus) ?_
        have hjoin480 : memRegion (a + 8#64) 400 ∗ memRegion (a + 408#64) 80 ⊢
            memRegion (a + 8#64) 480 := by
          have h408 : (a + 8#64) + 400#64 = a + 408#64 := BitVec.add_assoc a 8#64 400#64
          rw [← h408, show (480 : Nat) = 400 + 80 from rfl,
              ProofLib.memRegion_split (a + 8#64) 400 80 (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin480 (by sep_focus) ?_
        have hjoin880 : memRegion (a + 8#64) 480 ∗ memRegion (a + 488#64) polyDecoderSize ⊢
            memRegion (a + 8#64) 880 := by
          have h488 : (a + 8#64) + 480#64 = a + 488#64 := BitVec.add_assoc a 8#64 480#64
          rw [← h488, show (880 : Nat) = 480 + polyDecoderSize from rfl,
              ProofLib.memRegion_split (a + 8#64) 480 polyDecoderSize (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin880 (by sep_focus) ?_
        have hjoin928 := tag_and_two_regions_entails_928 a 4#64 880 40 888#64
          (BitVec.add_assoc a 8#64 880#64).symm rfl
        refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
        apply sepWP_evs_of (w ++ w_1) (hevs1.append hevs2)
        wp_done

/-- Variant `ct1Received` (`tag = 5#64`, jump index `3` -> `+68` -> dealloc 4 Vecs -> `+696` tail-call Block `441`). -/
theorem drop_chunked_states_local1_ct1Received_placed_ok
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (henc : subroutine_ok (lsProg_441 H) (blkPl_441).base (dropGluePolyEncoderSpec M A lim))
    (st_v : Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.ct1Received st_v))) := by
  have henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec M A lim)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) henc
  clear henc
  simp only [withLsCodeLoaded, dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_prologue_lscl ‹_› (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedCt1ReceivedAt, spqrPolyApi]
  refine SepWP.focus_weaken (unchunkedEkSentCt1Received408_entails_dealloc A.repAlloc a st_v.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_evs_step_lscl hcl0 (mid := (blkPl_443).base + 88#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 5#64) ∗ polyEncoderAt A.repAlloc (a + 8#64) st_v.sending_ek ∗
        (fourVec408HeadersAt a g ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr) ∗
        memRegion (a + 512#64) 416) ∗
      chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · clear hdealloc
    dsimp only [fourVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_0]
      have hacp' : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 hcl1 ⟨hpres1, hacp1, hx19_1⟩
    exact step_88_fourVec_tail_lscl hdealloc henc_cl hcl1 (by assumption) hfsp_align hpc1 hrun1 hpres1 hacp1 hx19_1

/-- Variant `keysSampled` (`tag = 3#64`, jump index `1` -> `+68` -> dealloc 4 Vecs -> `+696` tail-call Block `441`). -/
theorem drop_chunked_states_local1_keysSampled_placed_ok
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (henc : subroutine_ok (lsProg_441 H) (blkPl_441).base (dropGluePolyEncoderSpec M A lim))
    (st_v : KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.keysSampled st_v))) := by
  have henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec M A lim)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) henc
  clear henc
  simp only [withLsCodeLoaded, dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_prologue_lscl ‹_› (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedKeysSampledAt, polyEncoderSize, BitVec.ofNat_eq_ofNat, spqrPolyApi]
  have h408 : (a + 8#64) + 400#64 = a + 408#64 := BitVec.add_assoc a 8#64 400#64
  rw [h408]
  have hdealloc408 : unchunkedHeaderSentAt A.repAlloc (a + 408#64) st_v.uc ⊢
      ∃∗ g : FourVecGhost,
        fourVec408HeadersAt a g ∗
        vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr :=
    unchunkedEkSentCt1Received408_entails_dealloc A.repAlloc a (unchunkedHeaderSentToEkSentCt1Received st_v.uc)
  refine SepWP.focus_weaken hdealloc408 (by sep_focus) ?_
  wp_pull_exists; rename_i g
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_evs_step_lscl hcl0 (mid := (blkPl_443).base + 88#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 3#64) ∗ polyEncoderAt A.repAlloc (a + 8#64) st_v.sending_hdr ∗
        (fourVec408HeadersAt a g ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr) ∗
        memRegion (a + 512#64) 416) ∗
      chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · clear hdealloc
    dsimp only [fourVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_0]
      have hacp' : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 hcl1 ⟨hpres1, hacp1, hx19_1⟩
    exact step_88_fourVec_tail_lscl hdealloc henc_cl hcl1 (by assumption) hfsp_align hpc1 hrun1 hpres1 hacp1 hx19_1

/-- Variant `ekReceivedCt1Sampled` (`tag = 10#64`, jump index `8` -> `+596` -> dealloc 5 Vecs -> `+696` tail-call Block `441`). -/
theorem drop_chunked_states_local1_ekReceivedCt1Sampled_placed_ok
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (henc : subroutine_ok (lsProg_441 H) (blkPl_441).base (dropGluePolyEncoderSpec M A lim))
    (st_v : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.ekReceivedCt1Sampled st_v))) := by
  have henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec M A lim)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) henc
  simp only [withLsCodeLoaded, dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc henc; simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_prologue_lscl ‹_› (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedEkReceivedCt1SampledAt, polyEncoderSize, BitVec.ofNat_eq_ofNat, spqrPolyApi]
  have h408 : (a + 8#64) + 400#64 = a + 408#64 := BitVec.add_assoc a 8#64 400#64
  rw [h408]
  have hdealloc408 : unchunkedCt1SentEkReceivedAt A.repAlloc (a + 408#64) st_v.uc ⊢
      ∃∗ g : FiveVecGhost,
        fiveVec408HeadersAt a g ∗
        vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr :=
    unchunkedCt1Sent408_entails_dealloc A.repAlloc a
      { epoch := st_v.uc.epoch, hdr := st_v.uc.es, es := st_v.uc.ek, ct1 := st_v.uc.ct1, auth := st_v.uc.auth }
  refine SepWP.focus_weaken hdealloc408 (by sep_focus) ?_
  wp_pull_exists; rename_i g
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_evs_step_lscl hcl0 (mid := (blkPl_443).base + 616#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 10#64) ∗ polyEncoderAt A.repAlloc (a + 8#64) st_v.sending_ct1 ∗
        (fiveVec408HeadersAt a g ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
        memRegion (a + 536#64) 392) ∗
      chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [fiveVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_0]
      have hacp' : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    refine seq_evs_step_lscl hcl1 (mid := (blkPl_443).base + 636#64)
      (P_mid := fun st2 sm =>
        ((a ↦₆₄ 10#64) ∗ polyEncoderAt A.repAlloc (a + 8#64) st_v.sending_ct1 ∗
          (fiveVec408HeadersAt a g ∗
            vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
            vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
            vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
          memRegion (a + 536#64) 392) ∗
        chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool lim st2 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        savedFrame32 s0 v_x19)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [fiveVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · apply sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · intro st2 s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      refine seq_evs_step_lscl hcl2 (mid := (blkPl_443).base + 656#64)
        (P_mid := fun st3 sm =>
          ((a ↦₆₄ 10#64) ∗ polyEncoderAt A.repAlloc (a + 8#64) st_v.sending_ct1 ∗
            (fiveVec408HeadersAt a g ∗
              vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
              vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
            memRegion (a + 536#64) 392) ∗
          chunkedStatesLocal1JumpTablePlacedExpanded ∗
          A.pool lim st3 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          savedFrame32 s0 v_x19)
        (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [fiveVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · apply sepWP_evs_dealloc g.v3.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_2]
          have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · intro st3 s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_3
        refine seq_evs_step_lscl hcl3 (mid := (blkPl_443).base + 676#64)
          (P_mid := fun st4 sm =>
            ((a ↦₆₄ 10#64) ∗ polyEncoderAt A.repAlloc (a + 8#64) st_v.sending_ct1 ∗
              (fiveVec408HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
              memRegion (a + 536#64) 392) ∗
            chunkedStatesLocal1JumpTablePlacedExpanded ∗
            A.pool lim st4 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
            savedFrame32 s0 v_x19)
          (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [fiveVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
          · apply sepWP_evs_dealloc g.v4.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_3]
            have hacp' : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · intro st4 s4 hpc4 hrun4 hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hacp_4, hx19_4⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_4
          refine seq_evs_step_lscl hcl4 (mid := (blkPl_443).base + 696#64)
            (P_mid := fun st5 sm =>
              ((a ↦₆₄ 10#64) ∗ polyEncoderAt A.repAlloc (a + 8#64) st_v.sending_ct1 ∗
                memRegion (a + 408#64) 128 ∗ memRegion (a + 536#64) 392) ∗
              chunkedStatesLocal1JumpTablePlacedExpanded ∗
              A.pool lim st5 sm ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
              savedFrame32 s0 v_x19)
            (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
            ?_ ?_
          · have hhdr128 := fiveVec408HeadersAt_entails_memRegion_128 a g
            dsimp only [fiveVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hhdr128 ⊢
            by_cases hc5 : (g.v5.cap == 0#64) = true <;>
              simp only [hc5, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
            · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
              wp_steps
              refine SepWP.focus_weaken hhdr128 (by sep_focus) ?_
              refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
              refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
            · apply sepWP_evs_dealloc g.v5.cap.toNat 1
              wp_steps; wp_apply; rw [hsp_4]
              have hacp' : AllocCallPreserved s0 sf := hacp_4.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              refine SepWP.focus_weaken hhdr128 (by sep_focus) ?_
              refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
              refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
          · intro st5 s5 hpc5 hrun5 hcl5 ⟨hpres5, hacp5, hx19_5⟩
            exact tail_call_696_polyEncoder_lscl henc_cl hcl5 (by assumption) hfsp_align hpc5 hrun5 hpres5 hacp5 hx19_5
              (by decide) (BitVec.add_assoc a 8#64 528#64).symm rfl

/-! ## 3. `HookSat` & `withPanics` Per-Variant Wrappers (Part 2/2) -/

theorem drop_chunked_states_local1_ct2Sampled_placed
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.ct2Sampled st_v))) :=
  drop_chunked_states_local1_ct2Sampled_placed_ok
    (spqr_hook_ok_of_mem hdealloc) (drop_poly_encoder_local1_placed hdealloc) st_v

theorem drop_chunked_states_local1_ct2Sampled_placed_x
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.ct2Sampled st_v))) :=
  drop_chunked_states_local1_ct2Sampled_placed (hookSat_dealloc_withPanics hdealloc) st_v

theorem drop_chunked_states_local1_headerSent_placed
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.headerSent st_v))) :=
  drop_chunked_states_local1_headerSent_placed_ok
    (spqr_hook_ok_of_mem hdealloc)
    (drop_poly_encoder_local1_placed hdealloc)
    (drop_poly_decoder_placed hdealloc) st_v

theorem drop_chunked_states_local1_headerSent_placed_x
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.headerSent st_v))) :=
  drop_chunked_states_local1_headerSent_placed (hookSat_dealloc_withPanics hdealloc) st_v

theorem drop_chunked_states_local1_ct1Received_placed
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.ct1Received st_v))) :=
  drop_chunked_states_local1_ct1Received_placed_ok
    (spqr_hook_ok_of_mem hdealloc) (drop_poly_encoder_local1_placed hdealloc) st_v

theorem drop_chunked_states_local1_ct1Received_placed_x
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.ct1Received st_v))) :=
  drop_chunked_states_local1_ct1Received_placed (hookSat_dealloc_withPanics hdealloc) st_v

theorem drop_chunked_states_local1_keysSampled_placed
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.keysSampled st_v))) :=
  drop_chunked_states_local1_keysSampled_placed_ok
    (spqr_hook_ok_of_mem hdealloc) (drop_poly_encoder_local1_placed hdealloc) st_v

theorem drop_chunked_states_local1_keysSampled_placed_x
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.keysSampled st_v))) :=
  drop_chunked_states_local1_keysSampled_placed (hookSat_dealloc_withPanics hdealloc) st_v

theorem drop_chunked_states_local1_ekReceivedCt1Sampled_placed
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.ekReceivedCt1Sampled st_v))) :=
  drop_chunked_states_local1_ekReceivedCt1Sampled_placed_ok
    (spqr_hook_ok_of_mem hdealloc) (drop_poly_encoder_local1_placed hdealloc) st_v

theorem drop_chunked_states_local1_ekReceivedCt1Sampled_placed_x
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.ekReceivedCt1Sampled st_v))) :=
  drop_chunked_states_local1_ekReceivedCt1Sampled_placed (hookSat_dealloc_withPanics hdealloc) st_v

end PlacedStates1BudgetAux

end LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1PlacedBudgetAux
