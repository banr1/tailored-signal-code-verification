/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainStatesClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Drop.States2Budget
public import LibsignalBinary.Proofs.SpqrV1.Drop.States2BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Drop.Chunked
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Budget-Threaded Code-Loaded Drop Glue for `chunked::states::States` (Block `273`)

Proves `withLsCodeLoaded lsmpl` contracts under `RustCliAllocBudget M` (`FreeOnlyEvs`) for
Block `273` (`drop_glue::<spqr::v1::chunked::states::States> [local#2]`), re-exporting Blocks
`279`, `287`, `266`, and `269` from `ChainStatesClPlacedBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open CryptoGames.LibsignalSession (
  ShaCompress
)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalPlacement blkPC_273 blkPl_273 libsignalSessionLib
  lsProg_273 ls_blockPlacement_base ls_subroutine_ok_of_block lscall_blk_cl lsmpl lsρ
  sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded withMemEq
)
open CryptoVerification.LibsignalSpqrV1 (
  States spqrAuthApi spqrPolyApi
)
open CryptoVerification.RustHeap (
  allocHookStack
)
open CryptoVerification.SpqrV1.Alloc (
  spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Drop (
  DropChunkedStatesGhost Saved32x19Preserved chunkedCt1AcknowledgedAt chunkedCt1ReceivedSize
  chunkedCt1SampledAt chunkedCt2SampledAt chunkedEkReceivedCt1SampledSize
  chunkedEkSentCt1ReceivedSize chunkedHeaderReceivedAt chunkedHeaderSentSize
  chunkedKeysSampledAt_eq_ct1ReceivedAt chunkedKeysSampledToCt1Received chunkedKeysUnsampledAt
  chunkedNoHeaderReceivedAt chunkedStatesAt chunkedStatesLocal2JumpTableBytes
  chunkedStatesLocal2JumpTablePlacedAt chunkedStatesLocal2JumpTablePlacedExpanded
  chunkedStatesSize chunked_400_join dropGluePoly16Stack dropStack32 dropStackPoly64
  polyDecoder64_entails_vecs_tail polyDecoder64_post_join polyDecoder88_entails_vecs_tail
  polyDecoder88_post_join polyDecoderAt_entails_vecs_tail polyDecoder_post_join
  polyEncoder8_entails_tag_vecs_tail polyEncoderAt_entails_tag_vecs_tail
  polyEncoderAt_expose_tag polyEncoderAt_unexpose_tag polyEncoder_local2_8_post_join
  stackAt_dropStack32_split_sub32 stackAt_dropStackPoly64_split
  stackAt_dropStackPoly64_split_bottom stack_restore_64_dropStack32
  tag_and_two_regions_entails_928 threeVec8HeadersAt threeVec8HeadersAt_entails_memRegion_80
  twoVec408HeadersAt twoVec408HeadersAt_entails_memRegion_56 twoVec8HeadersAt
  twoVec8HeadersAt_entails_memRegion_56 unchunkedCt1SentAt unchunkedCt1SentSize
  unchunkedCt2Sent408_entails_dealloc unchunkedCt2Sent8_entails_dealloc
  unchunkedEkSent8_entails_dealloc unchunkedHeaderReceivedAt_eq_ekSentAt
  unchunkedKeysUnsampledAt_eq_ct2SentAt unchunkedNoHeaderReceivedAt_eq_ct2SentAt
  vecCapPtrDealloc vecGF16ListOf vecPtListOf
)
open CryptoVerification.SpqrV1.Poly (
  polyArrayBytes polyDecoderAt polyDecoderSize polyEncoderAt
)
open CryptoVerification.SpqrV1.States.Recv (
  spqrRustDeallocSym
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget (
  dropChunkedCt1ReceivedSpec dropChunkedEkReceivedCt1SampledSpec
  dropChunkedEkSentCt1ReceivedSpec dropChunkedHeaderSentSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (
  dropGluePoly16Spec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (
  dropGlueSortedSetPt16Spec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.States1aBudget (
  align_pre_st align_pre_vm deallocFreeOnlySpec savedFrame32 sepWP_evs_dealloc sepWP_evs_nil
  sepWP_evs_of sepWP_open_evs seq_evs_step subroutine_ok_deallocFreeOnly
)
open LibsignalBinary.Proofs.SpqrV1.Drop.States2BudgetAux (
  chunkedStatesLocal2JumpTablePlacedAt_eq dropChunkedStatesLocal2PlacedSpec
  dropChunkedStatesLocal2PlacedVariantSpec step_prologue2_12_placed
)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (
  dropUnchunkedCt1SentSpec
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget (
  drop_chunked_ct1_received_mem_on drop_chunked_ek_received_ct1_sampled_mem_on
  drop_chunked_ek_sent_ct1_received_mem_on drop_chunked_header_sent_mem_on
  drop_glue_poly16_mem_on drop_glue_sorted_set_pt16_mem_on
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux (
  ls_to_blockProgram subroutine_ok_withLsCodeLoaded_intro
)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ChainStatesClPlacedBudget

open Arm64 ProofLib
open ProofLib.ProgramReflection

export LibsignalBinary.Proofs.SpqrV1.Drop.States2BudgetAux (
  dropChunkedStatesLocal2PlacedSpec dropChunkedStatesLocal2PlacedVariantSpec
)
export LibsignalBinary.Proofs.SpqrV1.Drop.ChainStatesClPlacedBudgetAux (
  drop_unchunked_ct1_sent_local2_cl_placed_ok
  drop_unchunked_ct1_sent_local2_cl_blockProgram
  drop_unchunked_ct1_sent_local2_cl_on
  drop_unchunked_ct1_sent_local2_mem_on
  drop_chain_epoch_slice_local2_cl_placed_ok
  drop_chain_epoch_slice_local2_cl_blockProgram
  drop_chain_epoch_slice_local2_cl_on
  drop_chain_epoch_slice_local2_mem_on
  drop_opt_proto_spqr_chain_cl_placed_ok
  drop_opt_proto_spqr_chain_cl_blockProgram
  drop_opt_proto_spqr_chain_cl_on
  drop_opt_proto_spqr_chain_mem_on
  drop_spqr_chain_cl_placed_ok
  drop_spqr_chain_cl_blockProgram
  drop_spqr_chain_cl_on
  drop_spqr_chain_mem_on
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `withLsCodeLoaded` Prologue and Sequencing Helpers for Block `273` -/

private theorem seq_evs_step_lscl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {mid target : BitVec 64}
    {st : M.σ} {s : State} {P X1 X2 X3 : SepProp}
    {P_mid : M.σ → State → SepProp} {Q_mid Q_out : State → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs1, FreeOnlyEvs evs1 ∧ (Pm ⊢ P_mid (M.stepEvents evs1 st) sm) ∧ Q_mid sm))
    (h2 : ∀ (st1 : M.σ) (sm : State),
      sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm →
      SepWP prog target sm (P_mid st1 sm) (fun sf Pf =>
        ∃ evs2, FreeOnlyEvs evs2 ∧
          (Pf ⊢ X1 ∗ X2 ∗ A.pool lim (M.stepEvents evs2 st1) sf ∗ X3) ∧ Q_out sf)) :
    SepWP prog target s P (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧
        (Pf ⊢ X1 ∗ X2 ∗ A.pool lim (M.stepEvents evs st) sf ∗ X3) ∧ Q_out sf) := by
  apply sepWP_seq_lscl hcl (mid := mid)
  refine SepWP.mono h1 fun sm _Pm hpc hrun ⟨evs1, hevs1, hent, hQ⟩ hclm => ?_
  exact SepWP.mono (SepWP.weaken_pre hent (h2 (M.stepEvents evs1 st) sm hpc hrun hclm hQ))
    fun sf _Pf _ _ ⟨evs2, hevs2, hPf, hQo⟩ =>
      ⟨evs1 ++ evs2, hevs1.append hevs2, by
        rwa [LibsignalBinary.Heap.AllocCostModel.stepEvents_append], hQo⟩

private theorem enter_prologue2_12_lscl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {target : BitVec 64} {s0 : State} {st : M.σ} {a : BitVec 64}
    (v_fp v_lr v_x20 v_x19 : BitVec 64) {Body : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_273).base) (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = a)
    (hk : ∀ sp1 : State,
      sp1.pc = (blkPl_273).base + 12#64 →
      sp1.status = .Running →
      LibsignalCodeLoaded lsmpl sp1.mem →
      Saved32x19Preserved s0 sp1 (s0.sp - 32#64) →
      AllocCallPreserved s0 sp1 →
      sp1.readReg64 .x0 = a →
      SepWP ((blkPC_273).rebase (blkPl_273).base H) target sp1
        (Body ∗ A.pool lim st sp1 ∗ savedFrame32 s0 v_x19) post) :
    SepWP ((blkPC_273).rebase (blkPl_273).base H) target s0
      (Body ∗ A.pool lim st s0 ∗
        (((s0.sp - 32#64) ↦₆₄ v_fp) ∗ ((s0.sp - 24#64) ↦₆₄ v_lr) ∗
          ((s0.sp - 16#64) ↦₆₄ v_x20) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19))) post := by
  have h1 := step_prologue2_12_placed (H := H) s0 v_fp v_lr v_x20 v_x19
    (Body ∗ A.pool lim st s0) hpc hrun hsp_align
  apply sepWP_seq_lscl hcl (mid := (blkPl_273).base + 12#64)
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono h1 ?_)
  intro sp1 Pp1 hpc1 hrun1 ⟨hvm, hent, hpres, hacp, hx0_1⟩ hcl1
  rw [hx0] at hx0_1
  have hent' : Pp1 ⊢ Body ∗ A.pool lim st sp1 ∗ savedFrame32 s0 v_x19 := by
    rw [A.pool_of_vmPreserved hvm]
    exact Entails.trans hent (Entails.of_eq (by sep_ac_rfl))
  exact SepWP.weaken_pre hent' (hk sp1 hpc1 hrun1 hcl1 hpres hacp hx0_1)

private theorem enter_chunked_states_local2_prologue_lscl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s0 : State} {st : M.σ} {a : BitVec 64} {StatePre R : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_273).base) (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = a)
    (hk : ∀ (sp1 : State) (v_x19 : BitVec 64),
      sp1.pc = (blkPl_273).base + 12#64 →
      sp1.status = .Running →
      LibsignalCodeLoaded lsmpl sp1.mem →
      Saved32x19Preserved s0 sp1 (s0.sp - 32#64) →
      AllocCallPreserved s0 sp1 →
      sp1.readReg64 .x0 = a →
      SepWP ((blkPC_273).rebase (blkPl_273).base H) (s0.readReg64 .lr) sp1
        (StatePre ∗ chunkedStatesLocal2JumpTablePlacedExpanded ∗
          A.pool lim st sp1 ∗ stackAt (s0.sp - 32#64) dropStack32 ∗ savedFrame32 s0 v_x19)
        (fun sf Pf =>
          ∃ evs, FreeOnlyEvs evs ∧
            (Pf ⊢ memRegion a 928 ∗ chunkedStatesLocal2JumpTablePlacedExpanded ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStackPoly64) ∧
            (sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf))) :
    SepWP ((blkPC_273).rebase (blkPl_273).base H) (s0.readReg64 .lr) s0
      (StatePre ∗ chunkedStatesLocal2JumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp dropStackPoly64)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R → sf.mem ⊨
          (∃∗ evs : List AllocEvent,
            ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
            memRegion a chunkedStatesSize ∗ chunkedStatesLocal2JumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStackPoly64) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [chunkedStatesLocal2JumpTablePlacedAt_eq]
  dsimp only [chunkedStatesSize]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  apply sepWP_open_evs
  refine SepWP.weaken_pre ?_ (enter_prologue2_12_lscl v_fp v_lr v_x20 v_x19
    (Body := StatePre ∗ chunkedStatesLocal2JumpTablePlacedExpanded ∗ stackAt (s0.sp - 32#64) dropStack32)
    hcl hpc hrun hsp_align hx0
    (fun sp1 hpc1 hrun1 hcl1 hpres1 hacp1 hx0_1 =>
      SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hk sp1 v_x19 hpc1 hrun1 hcl1 hpres1 hacp1 hx0_1)))
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Block `273` Variant Proofs (`withLsCodeLoaded`) -/

private theorem drop_chunked_states_local2_keysUnsampled_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.keysUnsampled st_v))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (States2BudgetAux.drop_chunked_states_local2_keysUnsampled_placed
      (spqr_hook_ok_of_mem (prog := lsProg_273 (Rust.withPanics ext)) hdealloc) st_v)

private theorem drop_chunked_states_local2_ct1Received_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.ct1Received st_v))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec] at *
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  refine enter_chunked_states_local2_prologue_lscl hcl (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 277)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
  have hsub_raw := drop_chunked_ct1_received_mem_on (F := F)
    (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc
  dsimp only [lsProg_273, withMemEq, dropChunkedCt1ReceivedSpec] at hsub_raw
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hsub_raw (⟨a + 8#64, st_v⟩, st)
  have hacp_f : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
  have hevs_w : FreeOnlyEvs w := by assumption
  rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  dsimp only [chunkedCt1ReceivedSize]
  have hjoin928 := tag_and_two_regions_entails_928 a 5#64 504 416 512#64
    (BitVec.add_assoc a 8#64 504#64).symm rfl
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
  apply sepWP_evs_of w hevs_w
  wp_done

private theorem drop_chunked_states_local2_keysSampled_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.keysSampled st_v))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec] at *
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  refine enter_chunked_states_local2_prologue_lscl hcl (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
  rw [chunkedKeysSampledAt_eq_ct1ReceivedAt]
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 277)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
  have hsub_raw := drop_chunked_ct1_received_mem_on (F := F)
    (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc
  dsimp only [lsProg_273, withMemEq, dropChunkedCt1ReceivedSpec] at hsub_raw
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hsub_raw (⟨a + 8#64, chunkedKeysSampledToCt1Received st_v⟩, st)
  have hacp_f : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
  have hevs_w : FreeOnlyEvs w := by assumption
  rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  dsimp only [chunkedCt1ReceivedSize]
  have hjoin928 := tag_and_two_regions_entails_928 a 3#64 504 416 512#64
    (BitVec.add_assoc a 8#64 504#64).symm rfl
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
  apply sepWP_evs_of w hevs_w
  wp_done

private theorem drop_chunked_states_local2_headerSent_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.headerSent st_v))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec] at *
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  refine enter_chunked_states_local2_prologue_lscl hcl (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 276)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
  have hsub_raw := drop_chunked_header_sent_mem_on (F := F)
    (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc
  dsimp only [lsProg_273, withMemEq, dropChunkedHeaderSentSpec] at hsub_raw
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  wp_call hsub_raw (⟨a + 8#64, st_v⟩, st)
  have hacp_f : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
  have hevs_w : FreeOnlyEvs w := by assumption
  rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
  dsimp only [chunkedHeaderSentSize]
  have hjoin928 := tag_and_two_regions_entails_928 a 4#64 880 40 888#64
    (BitVec.add_assoc a 8#64 880#64).symm rfl
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
  apply sepWP_evs_of w hevs_w
  wp_done

private theorem drop_chunked_states_local2_ekSentCt1Received_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.ekSentCt1Received st_v))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec] at *
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  refine enter_chunked_states_local2_prologue_lscl hcl (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 278)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
  have hsub_raw := drop_chunked_ek_sent_ct1_received_mem_on (F := F)
    (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc
  dsimp only [lsProg_273, withMemEq, dropChunkedEkSentCt1ReceivedSpec] at hsub_raw
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hsub_raw (⟨a + 8#64, st_v⟩, st)
  have hacp_f : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
  have hevs_w : FreeOnlyEvs w := by assumption
  rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  dsimp only [chunkedEkSentCt1ReceivedSize]
  have hjoin928 := tag_and_two_regions_entails_928 a 6#64 504 416 512#64
    (BitVec.add_assoc a 8#64 504#64).symm rfl
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
  apply sepWP_evs_of w hevs_w
  wp_done

private theorem drop_chunked_states_local2_ekReceivedCt1Sampled_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.ekReceivedCt1Sampled st_v))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec] at *
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  refine enter_chunked_states_local2_prologue_lscl hcl (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 275)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
  have hsub_raw := drop_chunked_ek_received_ct1_sampled_mem_on (F := F)
    (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc
  dsimp only [lsProg_273, withMemEq, dropChunkedEkReceivedCt1SampledSpec] at hsub_raw
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hsub_raw (⟨a + 8#64, st_v⟩, st)
  have hacp_f : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
  have hevs_w : FreeOnlyEvs w := by assumption
  rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  dsimp only [chunkedEkReceivedCt1SampledSize]
  have hjoin928 := tag_and_two_regions_entails_928 a 10#64 528 392 536#64
    (BitVec.add_assoc a 8#64 528#64).symm rfl
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
  apply sepWP_evs_of w hevs_w
  wp_done

private theorem drop_chunked_states_local2_ct1Acknowledged_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.ct1Acknowledged st_v))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec] at *
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  refine enter_chunked_states_local2_prologue_lscl hcl (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedCt1AcknowledgedAt, spqrPolyApi, savedFrame32,
    chunkedStatesLocal2JumpTablePlacedExpanded]
  refine SepWP.focus_weaken (polyDecoderAt_entails_vecs_tail A.repAlloc (a + 136#64) st_v.receiving_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 279)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc1
  have hct1_raw := drop_unchunked_ct1_sent_local2_mem_on (F := F)
    (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc1
  dsimp only [lsProg_273, withMemEq, dropUnchunkedCt1SentSpec] at hct1_raw
  apply sepWP_seq_lscl hclc1 (mid := lsmpl.base 264)
  rw [← hsp_0]
  wp_call hct1_raw (⟨a + 8#64, st_v.uc⟩, st)
  have hacp_1 : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
  have hevs1 : FreeOnlyEvs w := by assumption
  have hsp_sf : sf.sp = sp1.sp := by assumption
  rw [hsp_0] at hsp_sf ⊢
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc2
  have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
    (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc2
  dsimp only [lsProg_273, withMemEq, dropGlueSortedSetPt16Spec] at hpt16_raw
  have hsp_eq : stackAt sf.sp dropStack32 = stackAt (s0.sp - 32#64) dropStack32 := by rw [hsp_sf]
  refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hpt16_raw (⟨a + 136#64, vecs⟩, M.stepEvents w st)
  have hacp_f : AllocCallPreserved s0 sf_1 := hacp_1.trans (by assumption)
  have hevs2 : FreeOnlyEvs w_1 := by assumption
  rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
  rw [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  dsimp only [polyArrayBytes, unchunkedCt1SentSize]
  refine SepWP.focus_weaken (polyDecoder_post_join (a + 136#64)) (by sep_focus) ?_
  have hjoin528 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) polyDecoderSize ⊢
      memRegion (a + 8#64) 528 := by
    have h136 : (a + 8#64) + 128#64 = a + 136#64 := BitVec.add_assoc a 8#64 128#64
    rw [← h136, show (528 : Nat) = 128 + polyDecoderSize from rfl,
        ProofLib.memRegion_split (a + 8#64) 128 polyDecoderSize (by decide)]
    exact Entails.refl _
  refine SepWP.focus_weaken hjoin528 (by sep_focus) ?_
  have hjoin928 := tag_and_two_regions_entails_928 a 11#64 528 392 536#64
    (BitVec.add_assoc a 8#64 528#64).symm rfl
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
  apply sepWP_evs_of (w ++ w_1) (hevs1.append hevs2)
  wp_done

private theorem drop_chunked_states_local2_noHeaderReceived_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.noHeaderReceived st_v))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (prog := lsProg_273 (Rust.withPanics ext)) hdealloc
  simp only [spqrRustDeallocSym] at hdealloc_raw
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  clear hdealloc_raw; simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec] at *
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_local2_prologue_lscl hcl (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedNoHeaderReceivedAt, spqrPolyApi]
  rw [unchunkedNoHeaderReceivedAt_eq_ct2SentAt]
  refine SepWP.focus_weaken
    (unchunkedCt2Sent8_entails_dealloc A.repAlloc a { epoch := st_v.uc.epoch, auth := st_v.uc.auth })
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.focus_weaken (polyDecoder64_entails_vecs_tail A.repAlloc a st_v.receiving_hdr) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_evs_step_lscl hcl0 (mid := (blkPl_273).base + 240#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 7#64) ∗
        (twoVec8HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
        vecPtListOf A.repAlloc (a + 64#64) vecs ∗ memRegion (a + 448#64) 16 ∗
        memRegion (a + 464#64) 464) ∗
      chunkedStatesLocal2JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [twoVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_0]
      have hacp' : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    refine seq_evs_step_lscl hcl1 (mid := (blkPl_273).base + 260#64)
      (P_mid := fun st2 sm =>
        ((a ↦₆₄ 7#64) ∗ memRegion (a + 8#64) 56 ∗
          vecPtListOf A.repAlloc (a + 64#64) vecs ∗ memRegion (a + 448#64) 16 ∗
          memRegion (a + 464#64) 464) ∗
        chunkedStatesLocal2JumpTablePlacedExpanded ∗
        A.pool lim st2 sm ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
        savedFrame32 s0 v_x19)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · have hhdr56 := twoVec8HeadersAt_entails_memRegion_56 a g
      dsimp only [twoVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hhdr56 ⊢
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
    · intro st2 s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      dsimp only [savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
      apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 264)
      wp_steps
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
      have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
        (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc
      dsimp only [lsProg_273, withMemEq, dropGlueSortedSetPt16Spec] at hpt16_raw
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
      wp_call hpt16_raw (⟨a + 64#64, vecs⟩, st2)
      have hacp_f : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
      have hevs_w : FreeOnlyEvs w := by assumption
      rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
      dsimp only [polyArrayBytes]
      refine SepWP.focus_weaken (polyDecoder64_post_join a) (by sep_focus) ?_
      have hjoin456 : memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) polyDecoderSize ⊢
          memRegion (a + 8#64) 456 := by
        have h64 : (a + 8#64) + 56#64 = a + 64#64 := BitVec.add_assoc a 8#64 56#64
        rw [← h64, show (456 : Nat) = 56 + polyDecoderSize from rfl,
            ProofLib.memRegion_split (a + 8#64) 56 polyDecoderSize (by decide)]
        exact Entails.refl _
      refine SepWP.focus_weaken hjoin456 (by sep_focus) ?_
      have hjoin928 := tag_and_two_regions_entails_928 a 7#64 456 464 464#64
        (BitVec.add_assoc a 8#64 456#64).symm rfl
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
      apply sepWP_evs_of w hevs_w
      wp_done

private theorem drop_chunked_states_local2_headerReceived_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.headerReceived st_v))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (prog := lsProg_273 (Rust.withPanics ext)) hdealloc
  simp only [spqrRustDeallocSym] at hdealloc_raw
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  clear hdealloc_raw; simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec] at *
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_local2_prologue_lscl hcl (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedHeaderReceivedAt, spqrPolyApi]
  rw [unchunkedHeaderReceivedAt_eq_ekSentAt]
  refine SepWP.focus_weaken
    (unchunkedEkSent8_entails_dealloc A.repAlloc a { epoch := st_v.uc.epoch, auth := st_v.uc.auth, dk := st_v.uc.hdr })
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.focus_weaken (polyDecoder88_entails_vecs_tail A.repAlloc a st_v.receiving_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_evs_step_lscl hcl0 (mid := (blkPl_273).base + 296#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 8#64) ∗
        (threeVec8HeadersAt a g ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
        vecPtListOf A.repAlloc (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗
        memRegion (a + 488#64) 440) ∗
      chunkedStatesLocal2JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [threeVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_0]
      have hacp' : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    refine seq_evs_step_lscl hcl1 (mid := (blkPl_273).base + 316#64)
      (P_mid := fun st2 sm =>
        ((a ↦₆₄ 8#64) ∗
          (threeVec8HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
          vecPtListOf A.repAlloc (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗
          memRegion (a + 488#64) 440) ∗
        chunkedStatesLocal2JumpTablePlacedExpanded ∗
        A.pool lim st2 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        savedFrame32 s0 v_x19)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [threeVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · apply sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · intro st2 s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      refine seq_evs_step_lscl hcl2 (mid := (blkPl_273).base + 336#64)
        (P_mid := fun st3 sm =>
          ((a ↦₆₄ 8#64) ∗ memRegion (a + 8#64) 80 ∗
            vecPtListOf A.repAlloc (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗
            memRegion (a + 488#64) 440) ∗
          chunkedStatesLocal2JumpTablePlacedExpanded ∗
          A.pool lim st3 sm ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
          savedFrame32 s0 v_x19)
        (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · have hhdr80 := threeVec8HeadersAt_entails_memRegion_80 a g
        dsimp only [threeVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hhdr80 ⊢
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
      · intro st3 s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_3
        dsimp only [savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
        apply sepWP_seq_lscl hcl3 (mid := lsmpl.base 264)
        wp_steps
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
        have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
          (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc
        dsimp only [lsProg_273, withMemEq, dropGlueSortedSetPt16Spec] at hpt16_raw
        refine SepWP.focus_weaken
          (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x19) v_x19)
          (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
        wp_call hpt16_raw (⟨a + 88#64, vecs⟩, st3)
        have hacp_f : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
        have hevs_w : FreeOnlyEvs w := by assumption
        rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
        dsimp only [polyArrayBytes]
        refine SepWP.focus_weaken (polyDecoder88_post_join a) (by sep_focus) ?_
        have hjoin480 : memRegion (a + 8#64) 80 ∗ memRegion (a + 88#64) polyDecoderSize ⊢
            memRegion (a + 8#64) 480 := by
          have h88 : (a + 8#64) + 80#64 = a + 88#64 := BitVec.add_assoc a 8#64 80#64
          rw [← h88, show (480 : Nat) = 80 + polyDecoderSize from rfl,
              ProofLib.memRegion_split (a + 8#64) 80 polyDecoderSize (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin480 (by sep_focus) ?_
        have hjoin928 := tag_and_two_regions_entails_928 a 8#64 480 440 488#64
          (BitVec.add_assoc a 8#64 480#64).symm rfl
        refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
        apply sepWP_evs_of w hevs_w
        wp_done

private theorem drop_chunked_states_local2_ct1Sampled_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.ct1Sampled st_v))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec] at *
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_local2_prologue_lscl hcl (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedCt1SampledAt, spqrPolyApi]
  refine SepWP.focus_weaken (polyEncoderAt_expose_tag A.repAlloc a st_v.sending_ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i tag_w; wp_focus_pure; intro hw
  refine seq_evs_step_lscl hcl0 (mid := (blkPl_273).base + 188#64)
    (P_mid := fun st1 sm =>
      (polyEncoderAt A.repAlloc a st_v.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (a + 400#64) st_v.uc ∗
        polyDecoderAt A.repAlloc (a + 528#64) st_v.receiving_ek) ∗
      chunkedStatesLocal2JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · rcases hw with rfl | rfl
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      dsimp only [savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
      wp_steps
      refine SepWP.focus_weaken (polyEncoderAt_unexpose_tag A.repAlloc a 0#64 st_v.sending_ct1) (by sep_focus) ?_
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      dsimp only [savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
      wp_steps
      refine SepWP.focus_weaken (polyEncoderAt_unexpose_tag A.repAlloc a 1#64 st_v.sending_ct1) (by sep_focus) ?_
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    dsimp only [savedFrame32]
    refine SepWP.focus_weaken (polyEncoderAt_entails_tag_vecs_tail A.repAlloc a st_v.sending_ct1) (by sep_focus) ?_
    wp_pull_exists; rename_i tag enc_vecs; wp_focus_pure; intro henc_len
    refine SepWP.focus_weaken (polyDecoderAt_entails_vecs_tail A.repAlloc (a + 528#64) st_v.receiving_ek) (by sep_focus) ?_
    wp_pull_exists; rename_i dec_vecs; wp_focus_pure; intro hdec_len
    apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 279)
    wp_steps
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc1
    have hct1_raw := drop_unchunked_ct1_sent_local2_mem_on (F := F)
      (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc1
    dsimp only [lsProg_273, withMemEq, dropUnchunkedCt1SentSpec] at hct1_raw
    apply sepWP_seq_lscl hclc1 (mid := lsmpl.base 265)
    rw [← hsp_1]
    wp_call hct1_raw (⟨a + 400#64, st_v.uc⟩, st1)
    have hacp_2 : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
    have hevs1 : FreeOnlyEvs w := by assumption
    have hsp_sf : sf.sp = s1.sp := by assumption
    wp_steps
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc2
    have hpoly16_raw := drop_glue_poly16_mem_on
      (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc2
    dsimp only [lsProg_273, withMemEq, dropGluePoly16Spec] at hpoly16_raw
    apply sepWP_seq_lscl hclc2 (mid := lsmpl.base 264)
    have hsplit_enc_stk : stackAt s1.sp dropStack32 = stackAt sf.sp dropGluePoly16Stack := by
      rw [hsp_sf]
    refine SepWP.focus_weaken (Entails.of_eq hsplit_enc_stk) (by sep_focus) ?_
    wp_call hpoly16_raw (⟨a + 8#64, enc_vecs⟩, M.stepEvents w st1)
    have hacp_3 : AllocCallPreserved s0 sf_1 := hacp_2.trans (by assumption)
    have hevs2 : FreeOnlyEvs w_1 := by assumption
    have hsp_sf1 : sf_1.sp = sf.sp := by assumption
    rw [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    wp_steps
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc3
    have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
      (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc3
    dsimp only [lsProg_273, withMemEq, dropGlueSortedSetPt16Spec] at hpt16_raw
    have hsp_eq : stackAt sf.sp dropGluePoly16Stack = stackAt (s0.sp - 32#64) dropStack32 := by
      rw [hsp_sf, hsp_1]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x19) v_x19)
      (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
    wp_call hpt16_raw (⟨a + 528#64, dec_vecs⟩, M.stepEvents (w ++ w_1) st1)
    have hacp_f : AllocCallPreserved s0 sf_2 := hacp_3.trans (by assumption)
    have hevs3 : FreeOnlyEvs w_2 := by assumption
    rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
    rw [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
    dsimp only [polyArrayBytes, unchunkedCt1SentSize]
    refine SepWP.focus_weaken (polyDecoder_post_join (a + 528#64)) (by sep_focus) ?_
    refine SepWP.focus_weaken (chunked_400_join a tag 128 528 rfl (by decide)) (by sep_focus) ?_
    have hjoin928 : memRegion a 528 ∗ memRegion (a + 528#64) polyDecoderSize ⊢ memRegion a 928 := by
      rw [show (928 : Nat) = 528 + polyDecoderSize from rfl,
          ProofLib.memRegion_split a 528 polyDecoderSize (by decide)]
      exact Entails.refl _
    refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
    apply sepWP_evs_of ((w ++ w_1) ++ w_2) ((hevs1.append hevs2).append hevs3)
    wp_done

private theorem drop_chunked_states_local2_ct2Sampled_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.ct2Sampled st_v))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (prog := lsProg_273 (Rust.withPanics ext)) hdealloc
  simp only [spqrRustDeallocSym] at hdealloc_raw
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  clear hdealloc_raw; simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec] at *
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_local2_prologue_lscl hcl (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0 hcl0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedCt2SampledAt, spqrPolyApi]
  refine SepWP.focus_weaken (unchunkedCt2Sent408_entails_dealloc A.repAlloc a st_v.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.focus_weaken (polyEncoder8_entails_tag_vecs_tail A.repAlloc a st_v.sending_ct2) (by sep_focus) ?_
  wp_pull_exists; rename_i tag vecs; wp_focus_pure; intro hvecs_len
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_evs_step_lscl hcl0 (mid := (blkPl_273).base + 372#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 12#64) ∗
        ((a + 8#64) ↦₆₄ tag) ∗ vecGF16ListOf A.repAlloc (a + 16#64) vecs ∗ memRegion (a + 400#64) 8 ∗
        (twoVec408HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
        memRegion (a + 464#64) 464) ∗
      chunkedStatesLocal2JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [twoVec408HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_0]
      have hacp' : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    refine seq_evs_step_lscl hcl1 (mid := (blkPl_273).base + 392#64)
      (P_mid := fun st2 sm =>
        ((a ↦₆₄ 12#64) ∗
          ((a + 8#64) ↦₆₄ tag) ∗ vecGF16ListOf A.repAlloc (a + 16#64) vecs ∗ memRegion (a + 400#64) 8 ∗
          memRegion (a + 408#64) 56 ∗
          memRegion (a + 464#64) 464) ∗
        chunkedStatesLocal2JumpTablePlacedExpanded ∗
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
    · intro st2 s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      dsimp only [savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
      apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 265)
      wp_steps
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
      have hpoly16_raw := drop_glue_poly16_mem_on
        (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hclc
      dsimp only [lsProg_273, withMemEq, dropGluePoly16Spec] at hpoly16_raw
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
      wp_call hpoly16_raw (⟨a + 16#64, vecs⟩, st2)
      have hacp_f : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
      have hevs_w : FreeOnlyEvs w := by assumption
      rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
      dsimp only [polyArrayBytes]
      refine SepWP.focus_weaken (polyEncoder_local2_8_post_join a tag) (by sep_focus) ?_
      have hjoin456 : memRegion (a + 8#64) 400 ∗ memRegion (a + 408#64) 56 ⊢
          memRegion (a + 8#64) 456 := by
        have h408 : (a + 8#64) + 400#64 = a + 408#64 := BitVec.add_assoc a 8#64 400#64
        rw [← h408, show (456 : Nat) = 400 + 56 from rfl,
            ProofLib.memRegion_split (a + 8#64) 400 56 (by decide)]
        exact Entails.refl _
      refine SepWP.focus_weaken hjoin456 (by sep_focus) ?_
      have hjoin928 := tag_and_two_regions_entails_928 a 12#64 456 464 464#64
        (BitVec.add_assoc a 8#64 456#64).symm rfl
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
      apply sepWP_evs_of w hevs_w
      wp_done

/-! ## Top-Level Block `273` Contract -/

theorem drop_chunked_states_local2_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (lsmpl.base 273)
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedSpec M A lim F)) := by
  rw [← ls_blockPlacement_base (i := 273)]
  refine subroutine_ok_outcome_intro fun ⟨⟨a, st_v⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  cases st_v with
  | keysUnsampled s =>
    exact (drop_chunked_states_local2_keysUnsampled_cl hdealloc s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
  | keysSampled s =>
    exact (drop_chunked_states_local2_keysSampled_cl hdealloc s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
  | headerSent s =>
    exact (drop_chunked_states_local2_headerSent_cl hdealloc s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Received s =>
    exact (drop_chunked_states_local2_ct1Received_cl hdealloc s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
  | ekSentCt1Received s =>
    exact (drop_chunked_states_local2_ekSentCt1Received_cl hdealloc s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
  | noHeaderReceived s =>
    exact (drop_chunked_states_local2_noHeaderReceived_cl hdealloc s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
  | headerReceived s =>
    exact (drop_chunked_states_local2_headerReceived_cl hdealloc s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Sampled s =>
    exact (drop_chunked_states_local2_ct1Sampled_cl hdealloc s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
  | ekReceivedCt1Sampled s =>
    exact (drop_chunked_states_local2_ekReceivedCt1Sampled_cl hdealloc s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Acknowledged s =>
    exact (drop_chunked_states_local2_ct1Acknowledged_cl hdealloc s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct2Sampled s =>
    exact (drop_chunked_states_local2_ct2Sampled_cl hdealloc s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout

theorem drop_chunked_states_local2_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 273 (Rust.withPanics ext)) (lsmpl.base 273)
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedSpec M A lim F)) :=
  ls_to_blockProgram (drop_chunked_states_local2_cl_placed_ok hdealloc)

theorem drop_chunked_states_local2_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 273)
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedSpec M A lim F)) :=
  ls_subroutine_ok_of_block (drop_chunked_states_local2_cl_placed_ok hdealloc) hidx

theorem drop_chunked_states_local2_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 273)
      (withMemEq m (dropChunkedStatesLocal2PlacedSpec M A lim F)) :=
  lscall_blk_cl (drop_chunked_states_local2_cl_placed_ok hdealloc) hcl hidx

end LibsignalBinary.Proofs.SpqrV1.Drop.ChainStatesClPlacedBudget
