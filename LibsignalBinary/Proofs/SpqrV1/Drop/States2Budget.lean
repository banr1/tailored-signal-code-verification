/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.States2BudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyDecoder
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Drop Glue for `spqr::v1::chunked::states::States [local#2]` (Block `273`)

Proves the six tail-call and call-sequence variant contracts (`ct1Received`, `keysSampled`,
`headerSent`, `ekSentCt1Received`, `ekReceivedCt1Sampled`, `ct1Acknowledged`) and the full
dispatch contract `drop_chunked_states_local2_placed_ok` for Block `273` under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkPC_273 blkPl_273 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Drop (
  chunkedCt1AcknowledgedAt chunkedCt1ReceivedSize
  chunkedEkReceivedCt1SampledSize chunkedEkSentCt1ReceivedSize
  chunkedHeaderSentSize chunkedKeysSampledAt_eq_ct1ReceivedAt
  chunkedKeysSampledToCt1Received chunkedStatesAt
  chunkedStatesLocal2JumpTablePlacedExpanded
  dropStack32
  polyDecoderAt_entails_vecs_tail polyDecoder_post_join
  stackAt_dropStackPoly64_split_bottom stack_restore_64_dropStack32
  tag_and_two_regions_entails_928 unchunkedCt1SentSize
)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes polyDecoderSize)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FreeOnlyEvs
  RustCliAllocBudget rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget (
  dropChunkedCt1ReceivedSpec dropChunkedEkReceivedCt1SampledSpec
  dropChunkedEkSentCt1ReceivedSpec dropChunkedHeaderSentSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.States1aBudget (savedFrame32 sepWP_evs_of)
open LibsignalBinary.Proofs.SpqrV1.Drop.States2BudgetAux (enter_chunked_states_local2_prologue)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (dropUnchunkedCt1SentSpec)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.States2Budget

open Arm64 ProofLib
open ProofLib.ProgramReflection

export LibsignalBinary.Proofs.SpqrV1.Drop.States2BudgetAux (
  dropChunkedStatesLocal2PlacedSpec dropChunkedStatesLocal2PlacedVariantSpec
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section PlacedStates2Budget
variable [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
  {lim : BudgetLimits} {F : ShaCompress} {H : String → Option (State → State)}

/-! ## Re-Exposed Multi-Segment Variants from `States2BudgetAux` -/

theorem drop_chunked_states_local2_keysUnsampled_placed
    (hdealloc : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.keysUnsampled st_v)) :=
  States2BudgetAux.drop_chunked_states_local2_keysUnsampled_placed hdealloc st_v

theorem drop_chunked_states_local2_noHeaderReceived_placed
    (hdealloc : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hpt16_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.noHeaderReceived st_v)) :=
  States2BudgetAux.drop_chunked_states_local2_noHeaderReceived_placed hdealloc hpt16_raw st_v

theorem drop_chunked_states_local2_headerReceived_placed
    (hdealloc : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hpt16_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.headerReceived st_v)) :=
  States2BudgetAux.drop_chunked_states_local2_headerReceived_placed hdealloc hpt16_raw st_v

theorem drop_chunked_states_local2_ct1Sampled_placed
    (hct1_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 279) (dropUnchunkedCt1SentSpec M A lim F))
    (hpoly16_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 265) (dropGluePoly16Spec M A lim))
    (hpt16_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.ct1Sampled st_v)) :=
  States2BudgetAux.drop_chunked_states_local2_ct1Sampled_placed hct1_raw hpoly16_raw hpt16_raw st_v

theorem drop_chunked_states_local2_ct2Sampled_placed
    (hdealloc : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hpoly16_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 265) (dropGluePoly16Spec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.ct2Sampled st_v)) :=
  States2BudgetAux.drop_chunked_states_local2_ct2Sampled_placed hdealloc hpoly16_raw st_v

/-! ## Tail-Call and Call-Sequence Variant Proofs -/

/-- Variant `ct1Received` (`tag = 5#64`, jump index `3` -> tail-call Block `277`). -/
theorem drop_chunked_states_local2_ct1Received_placed
    (hsub_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 277) (dropChunkedCt1ReceivedSpec M A lim F))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.ct1Received st_v)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  refine enter_chunked_states_local2_prologue (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
  wp_steps
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

/-- Variant `keysSampled` (`tag = 3#64`, jump index `1` -> tail-call Block `277`). -/
theorem drop_chunked_states_local2_keysSampled_placed
    (hsub_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 277) (dropChunkedCt1ReceivedSpec M A lim F))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.keysSampled st_v)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  refine enter_chunked_states_local2_prologue (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
  rw [chunkedKeysSampledAt_eq_ct1ReceivedAt]
  wp_steps
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

/-- Variant `headerSent` (`tag = 4#64`, jump index `2` -> tail-call Block `276`). -/
theorem drop_chunked_states_local2_headerSent_placed
    (hsub_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 276) (dropChunkedHeaderSentSpec M A lim F))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.headerSent st_v)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  refine enter_chunked_states_local2_prologue (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
  wp_steps
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

/-- Variant `ekSentCt1Received` (`tag = 6#64`, jump index `4` -> tail-call Block `278`). -/
theorem drop_chunked_states_local2_ekSentCt1Received_placed
    (hsub_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 278) (dropChunkedEkSentCt1ReceivedSpec M A lim F))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.ekSentCt1Received st_v)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  refine enter_chunked_states_local2_prologue (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
  wp_steps
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

/-- Variant `ekReceivedCt1Sampled` (`tag = 10#64`, jump index `8` -> tail-call Block `275`). -/
theorem drop_chunked_states_local2_ekReceivedCt1Sampled_placed
    (hsub_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 275) (dropChunkedEkReceivedCt1SampledSpec M A lim F))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.ekReceivedCt1Sampled st_v)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  refine enter_chunked_states_local2_prologue (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, savedFrame32, chunkedStatesLocal2JumpTablePlacedExpanded]
  wp_steps
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

/-- Variant `ct1Acknowledged` (`tag = 11#64`, jump index `9` -> `+100` -> `bl` Block `279` -> tail-call Block `264`). -/
theorem drop_chunked_states_local2_ct1Acknowledged_placed
    (hct1_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 279) (dropUnchunkedCt1SentSpec M A lim F))
    (hpt16_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec M A lim (.ct1Acknowledged st_v)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  refine enter_chunked_states_local2_prologue (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedCt1AcknowledgedAt, spqrPolyApi, savedFrame32,
    chunkedStatesLocal2JumpTablePlacedExpanded]
  refine SepWP.focus_weaken (polyDecoderAt_entails_vecs_tail A.repAlloc (a + 136#64) st_v.receiving_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  wp_steps
  rw [← hsp_0]
  wp_call hct1_raw (⟨a + 8#64, st_v.uc⟩, st)
  have hacp_1 : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
  have hevs1 : FreeOnlyEvs w := by assumption
  have hsp_sf : sf.sp = sp1.sp := by assumption
  rw [hsp_0] at hsp_sf ⊢
  wp_steps
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

/-! ## Top-Level Relocatable Contract (`drop_chunked_states_local2_placed_ok`) -/

theorem drop_chunked_states_local2_placed_ok
    (hdealloc : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hpt16 : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim))
    (hpoly16 : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 265) (dropGluePoly16Spec M A lim))
    (hek_ct1 : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 275) (dropChunkedEkReceivedCt1SampledSpec M A lim F))
    (hhdr : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 276) (dropChunkedHeaderSentSpec M A lim F))
    (hct1_recv : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 277) (dropChunkedCt1ReceivedSpec M A lim F))
    (hek_sent : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 278) (dropChunkedEkSentCt1ReceivedSpec M A lim F))
    (hct1_sent : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsmpl.base 279) (dropUnchunkedCt1SentSpec M A lim F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedSpec M A lim F) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨a, st_v⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  cases st_v with
  | keysUnsampled s =>
    exact (drop_chunked_states_local2_keysUnsampled_placed hdealloc s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | keysSampled s =>
    exact (drop_chunked_states_local2_keysSampled_placed hct1_recv s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | headerSent s =>
    exact (drop_chunked_states_local2_headerSent_placed hhdr s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ct1Received s =>
    exact (drop_chunked_states_local2_ct1Received_placed hct1_recv s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ekSentCt1Received s =>
    exact (drop_chunked_states_local2_ekSentCt1Received_placed hek_sent s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | noHeaderReceived s =>
    exact (drop_chunked_states_local2_noHeaderReceived_placed hdealloc hpt16 s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | headerReceived s =>
    exact (drop_chunked_states_local2_headerReceived_placed hdealloc hpt16 s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ct1Sampled s =>
    exact (drop_chunked_states_local2_ct1Sampled_placed hct1_sent hpoly16 hpt16 s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ekReceivedCt1Sampled s =>
    exact (drop_chunked_states_local2_ekReceivedCt1Sampled_placed hek_ct1 s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ct1Acknowledged s =>
    exact (drop_chunked_states_local2_ct1Acknowledged_placed hct1_sent hpt16 s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ct2Sampled s =>
    exact (drop_chunked_states_local2_ct2Sampled_placed hdealloc hpoly16 s).mono_outcome
      (a, st) R s0 hpc hrun hpre hsp (fun _ hout => hout)

end PlacedStates2Budget

end LibsignalBinary.Proofs.SpqrV1.Drop.States2Budget
