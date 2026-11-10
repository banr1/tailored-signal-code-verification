/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1PlacedBudgetAux
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Chunked `States` Drop Glue (Block `443`, Top-Level)

Assembles the 11-variant relocatable contracts (`drop_chunked_states_local1_placed_ok`) and
`LibsignalRoLoaded`-discharged jump-table-free contracts (`ro_drop_chunked_states_local1_placed*`)
on Block `443` (`lsProg_443 H`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  IsLsBlockProg LibsignalPlacement LibsignalRoLoaded
  extract_withLsCodeLoaded ls_subroutine_ok_cl_of_block ls_subroutine_ok_of_block
  lsmpl lsρ withLsCl withLsCodeLoaded
)
open CryptoVerification.Cli.SpqrV1.Drop (
  chunkedStatesLocal1JumpTablePlacedAt
  chunkedStatesLocal1JumpTable_lsro_cli_intro
  withLsRoLoaded
)
open CryptoVerification.Cli.SpqrV1.Drop.Placed (
  blkPl_440 blkPl_441 blkPl_444 lsProg_440 lsProg_441 lsProg_444
)
open CryptoVerification.Cli.SpqrV1.Drop.TopPlaced (blkPl_443 lsProg_443)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (
  DropChunkedStatesGhost chunkedStatesAt chunkedStatesSize dropStackPoly64
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.PolyDecoderPlacedBudget (drop_poly_decoder_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.PolyEncoderPlacedBudget (
  drop_poly_encoder_local1_placed
)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.UnchunkedPlacedBudget (
  drop_unchunked_ct1_sent_local1_placed
)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget (
  dropChunkedStatesLocal1PlacedSpec
  dropChunkedStatesLocal1PlacedVariantSpec
  drop_chunked_states_local1_ct1Acknowledged_placed
  drop_chunked_states_local1_ct1Acknowledged_placed_ok
  drop_chunked_states_local1_ct1Acknowledged_placed_x
  drop_chunked_states_local1_ct1Sampled_placed
  drop_chunked_states_local1_ct1Sampled_placed_ok
  drop_chunked_states_local1_ct1Sampled_placed_x
  drop_chunked_states_local1_ekSentCt1Received_placed
  drop_chunked_states_local1_ekSentCt1Received_placed_ok
  drop_chunked_states_local1_ekSentCt1Received_placed_x
  drop_chunked_states_local1_headerReceived_placed
  drop_chunked_states_local1_headerReceived_placed_ok
  drop_chunked_states_local1_headerReceived_placed_x
  drop_chunked_states_local1_keysUnsampled_placed
  drop_chunked_states_local1_keysUnsampled_placed_ok
  drop_chunked_states_local1_keysUnsampled_placed_x
  drop_chunked_states_local1_noHeaderReceived_placed
  drop_chunked_states_local1_noHeaderReceived_placed_ok
  drop_chunked_states_local1_noHeaderReceived_placed_x
  hookSat_dealloc_withPanics
)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1PlacedBudgetAux (
  drop_chunked_states_local1_ct1Received_placed
  drop_chunked_states_local1_ct1Received_placed_ok
  drop_chunked_states_local1_ct1Received_placed_x
  drop_chunked_states_local1_ct2Sampled_placed
  drop_chunked_states_local1_ct2Sampled_placed_ok
  drop_chunked_states_local1_ct2Sampled_placed_x
  drop_chunked_states_local1_ekReceivedCt1Sampled_placed
  drop_chunked_states_local1_ekReceivedCt1Sampled_placed_ok
  drop_chunked_states_local1_ekReceivedCt1Sampled_placed_x
  drop_chunked_states_local1_headerSent_placed
  drop_chunked_states_local1_headerSent_placed_ok
  drop_chunked_states_local1_headerSent_placed_x
  drop_chunked_states_local1_keysSampled_placed
  drop_chunked_states_local1_keysSampled_placed_ok
  drop_chunked_states_local1_keysSampled_placed_x
)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget (dropGluePolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (dropUnchunkedCt1SentSpec)

export CryptoVerification.Cli.SpqrV1.Drop (withLsRoLoaded)

export LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget (
  dropChunkedStatesLocal1PlacedSpec
  dropChunkedStatesLocal1PlacedVariantSpec
  drop_chunked_states_local1_ct1Acknowledged_placed
  drop_chunked_states_local1_ct1Acknowledged_placed_ok
  drop_chunked_states_local1_ct1Acknowledged_placed_x
  drop_chunked_states_local1_ct1Sampled_placed
  drop_chunked_states_local1_ct1Sampled_placed_ok
  drop_chunked_states_local1_ct1Sampled_placed_x
  drop_chunked_states_local1_ekSentCt1Received_placed
  drop_chunked_states_local1_ekSentCt1Received_placed_ok
  drop_chunked_states_local1_ekSentCt1Received_placed_x
  drop_chunked_states_local1_headerReceived_placed
  drop_chunked_states_local1_headerReceived_placed_ok
  drop_chunked_states_local1_headerReceived_placed_x
  drop_chunked_states_local1_keysUnsampled_placed
  drop_chunked_states_local1_keysUnsampled_placed_ok
  drop_chunked_states_local1_keysUnsampled_placed_x
  drop_chunked_states_local1_noHeaderReceived_placed
  drop_chunked_states_local1_noHeaderReceived_placed_ok
  drop_chunked_states_local1_noHeaderReceived_placed_x
)

export LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1PlacedBudgetAux (
  drop_chunked_states_local1_ct1Received_placed
  drop_chunked_states_local1_ct1Received_placed_ok
  drop_chunked_states_local1_ct1Received_placed_x
  drop_chunked_states_local1_ct2Sampled_placed
  drop_chunked_states_local1_ct2Sampled_placed_ok
  drop_chunked_states_local1_ct2Sampled_placed_x
  drop_chunked_states_local1_ekReceivedCt1Sampled_placed
  drop_chunked_states_local1_ekReceivedCt1Sampled_placed_ok
  drop_chunked_states_local1_ekReceivedCt1Sampled_placed_x
  drop_chunked_states_local1_headerSent_placed
  drop_chunked_states_local1_headerSent_placed_ok
  drop_chunked_states_local1_headerSent_placed_x
  drop_chunked_states_local1_keysSampled_placed
  drop_chunked_states_local1_keysSampled_placed_ok
  drop_chunked_states_local1_keysSampled_placed_x
)

/-! ## 1. Combined Top-Level `Block 443` Contracts -/

theorem drop_chunked_states_local1_placed_ok
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdec : subroutine_ok (lsProg_440 H) (blkPl_440).base (dropGlueSortedSetPt16Spec M A lim))
    (henc : subroutine_ok (lsProg_441 H) (blkPl_441).base (dropGluePolyEncoderSpec M A lim))
    (hct1_sent : subroutine_ok (lsProg_444 H) (blkPl_444).base (dropUnchunkedCt1SentSpec M A lim F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedSpec M A lim F)) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨a, st_v⟩, st_m⟩ R s0 hpc hrun hpre hsp => ?_
  cases st_v with
  | keysUnsampled s =>
    exact (drop_chunked_states_local1_keysUnsampled_placed_ok hdealloc s).mono_outcome
      (a, st_m) R s0 hpc hrun hpre hsp fun _ hout => hout
  | keysSampled s =>
    exact (drop_chunked_states_local1_keysSampled_placed_ok hdealloc henc s).mono_outcome
      (a, st_m) R s0 hpc hrun hpre hsp fun _ hout => hout
  | headerSent s =>
    exact (drop_chunked_states_local1_headerSent_placed_ok hdealloc henc hdec s).mono_outcome
      (a, st_m) R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Received s =>
    exact (drop_chunked_states_local1_ct1Received_placed_ok hdealloc henc s).mono_outcome
      (a, st_m) R s0 hpc hrun hpre hsp fun _ hout => hout
  | ekSentCt1Received s =>
    exact (drop_chunked_states_local1_ekSentCt1Received_placed_ok hdealloc hdec s).mono_outcome
      (a, st_m) R s0 hpc hrun hpre hsp fun _ hout => hout
  | noHeaderReceived s =>
    exact (drop_chunked_states_local1_noHeaderReceived_placed_ok hdealloc hdec s).mono_outcome
      (a, st_m) R s0 hpc hrun hpre hsp fun _ hout => hout
  | headerReceived s =>
    exact (drop_chunked_states_local1_headerReceived_placed_ok hdealloc hdec s).mono_outcome
      (a, st_m) R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Sampled s =>
    exact (drop_chunked_states_local1_ct1Sampled_placed_ok hct1_sent henc hdec s).mono_outcome
      (a, st_m) R s0 hpc hrun hpre hsp fun _ hout => hout
  | ekReceivedCt1Sampled s =>
    exact (drop_chunked_states_local1_ekReceivedCt1Sampled_placed_ok hdealloc henc s).mono_outcome
      (a, st_m) R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Acknowledged s =>
    exact (drop_chunked_states_local1_ct1Acknowledged_placed_ok hct1_sent hdec s).mono_outcome
      (a, st_m) R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct2Sampled s =>
    exact (drop_chunked_states_local1_ct2Sampled_placed_ok hdealloc henc s).mono_outcome
      (a, st_m) R s0 hpc hrun hpre hsp fun _ hout => hout

theorem drop_chunked_states_local1_placed
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedSpec M A lim F)) :=
  drop_chunked_states_local1_placed_ok
    (spqr_hook_ok_of_mem hdealloc)
    (drop_poly_decoder_placed hdealloc)
    (drop_poly_encoder_local1_placed hdealloc)
    (drop_unchunked_ct1_sent_local1_placed hdealloc)

theorem drop_chunked_states_local1_placed_x
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedSpec M A lim F)) :=
  drop_chunked_states_local1_placed (hookSat_dealloc_withPanics hdealloc)

theorem drop_chunked_states_local1_placed_lscl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsCodeLoaded lsmpl
        (dropChunkedStatesLocal1PlacedSpec M A lim F)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (drop_chunked_states_local1_placed hdealloc) hi

theorem drop_chunked_states_local1_placed_cl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsCl lsmpl
        (dropChunkedStatesLocal1PlacedSpec M A lim F)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (drop_chunked_states_local1_placed hdealloc) hi

/-! ## 2. `LibsignalRoLoaded` Jump-Table-Discharged Contracts (`ro_*` / `*_ro_*`) -/

/-- Jump-table-free budget-threaded specification for `States` drop glue (`Block 443`). -/
def dropChunkedStatesLocal1CleanPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (DropChunkedStatesGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      chunkedStatesAt A.repAlloc x.a x.st ∗
      A.pool lim st s ∗ stackAt s.sp dropStackPoly64
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a chunkedStatesSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStackPoly64

/-- Jump-table-discharged `[LibsignalPlacement]` budget-threaded specification for `States` drop
    glue (`Block 443`), requiring only `LibsignalRoLoaded lsmpl s0.mem` instead of an explicit
    `.rodata` jump-table atom. -/
abbrev dropChunkedStatesLocal1RoPlacedSpec
    [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) : Spec (DropChunkedStatesGhost F × M.σ) :=
  withLsRoLoaded lsmpl (dropChunkedStatesLocal1CleanPlacedSpec M A lim F)

theorem subroutine_ok_drop_states_ro_of_placed
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1RoPlacedSpec M A lim F)) := by
  refine subroutine_ok_mono h (fun x R s0 hp => ?_) (fun x R s0 sf hq => ?_)
  · obtain ⟨hcl, hp1⟩ := extract_withLsCodeLoaded hp
    dsimp only [dropChunkedStatesLocal1RoPlacedSpec, withLsRoLoaded] at hp1
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp1
    obtain ⟨hro, hp2⟩ := hp1
    have hp3 := chunkedStatesLocal1JumpTable_lsro_cli_intro hro hp2
    dsimp only [withLsCodeLoaded, dropChunkedStatesLocal1PlacedSpec,
      dropChunkedStatesLocal1CleanPlacedSpec, chunkedStatesLocal1JumpTablePlacedAt] at hp3 ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp3⟩
  · dsimp only [withLsCodeLoaded, dropChunkedStatesLocal1PlacedSpec,
      dropChunkedStatesLocal1RoPlacedSpec, withLsRoLoaded,
      dropChunkedStatesLocal1CleanPlacedSpec] at hq ⊢
    have hent_post :
        (∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
          memRegion x.1.a chunkedStatesSize ∗
          chunkedStatesLocal1JumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs x.2) sf ∗ stackAt s0.sp dropStackPoly64) ∗ R ⊢
        chunkedStatesLocal1JumpTablePlacedAt ∗
        ((∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
          memRegion x.1.a chunkedStatesSize ∗
          A.pool lim (M.stepEvents evs x.2) sf ∗ stackAt s0.sp dropStackPoly64) ∗ R) := by
      rw [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro evs
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right evs (Entails.refl _))))
      exact Entails.of_eq (by sep_ac_rfl)
    exact Satisfies.of_sep_right (Satisfies.mono hent_post hq)

theorem ro_drop_chunked_states_local1_placed_ok
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdec : subroutine_ok (lsProg_440 H) (blkPl_440).base (dropGlueSortedSetPt16Spec M A lim))
    (henc : subroutine_ok (lsProg_441 H) (blkPl_441).base (dropGluePolyEncoderSpec M A lim))
    (hct1_sent : subroutine_ok (lsProg_444 H) (blkPl_444).base (dropUnchunkedCt1SentSpec M A lim F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1RoPlacedSpec M A lim F)) :=
  subroutine_ok_drop_states_ro_of_placed
    (drop_chunked_states_local1_placed_ok hdealloc hdec henc hct1_sent)

theorem ro_drop_chunked_states_local1_placed
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1RoPlacedSpec M A lim F)) :=
  subroutine_ok_drop_states_ro_of_placed (drop_chunked_states_local1_placed hdealloc)

theorem ro_drop_chunked_states_local1_placed_x
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1RoPlacedSpec M A lim F)) :=
  ro_drop_chunked_states_local1_placed (hookSat_dealloc_withPanics hdealloc)

theorem ro_drop_chunked_states_local1_placed_lscl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1RoPlacedSpec M A lim F)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (ro_drop_chunked_states_local1_placed hdealloc) hi

theorem ro_drop_chunked_states_local1_placed_cl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsCl lsmpl (dropChunkedStatesLocal1RoPlacedSpec M A lim F)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (ro_drop_chunked_states_local1_placed hdealloc) hi

theorem drop_chunked_states_local1_ro_placed_ok
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdec : subroutine_ok (lsProg_440 H) (blkPl_440).base (dropGlueSortedSetPt16Spec M A lim))
    (henc : subroutine_ok (lsProg_441 H) (blkPl_441).base (dropGluePolyEncoderSpec M A lim))
    (hct1_sent : subroutine_ok (lsProg_444 H) (blkPl_444).base (dropUnchunkedCt1SentSpec M A lim F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1RoPlacedSpec M A lim F)) :=
  ro_drop_chunked_states_local1_placed_ok hdealloc hdec henc hct1_sent

theorem drop_chunked_states_local1_ro_placed
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1RoPlacedSpec M A lim F)) :=
  ro_drop_chunked_states_local1_placed hdealloc

theorem drop_chunked_states_local1_ro_placed_x
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1RoPlacedSpec M A lim F)) :=
  ro_drop_chunked_states_local1_placed_x hdealloc

theorem drop_chunked_states_local1_ro_placed_lscl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1RoPlacedSpec M A lim F)) :=
  ro_drop_chunked_states_local1_placed_lscl hdealloc hi

theorem drop_chunked_states_local1_ro_placed_cl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsCl lsmpl (dropChunkedStatesLocal1RoPlacedSpec M A lim F)) :=
  ro_drop_chunked_states_local1_placed_cl hdealloc hi

theorem ro_outer_drop_chunked_states_local1_placed_lscl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl
          (dropChunkedStatesLocal1CleanPlacedSpec M A lim F))) := by
  refine subroutine_ok_mono
    (ro_drop_chunked_states_local1_placed_lscl hdealloc hi)
    (fun _ _ _ hp => Satisfies.mono (Entails.of_eq (by
      dsimp only [withLsCodeLoaded, dropChunkedStatesLocal1RoPlacedSpec, withLsRoLoaded]
      sep_ac_rfl)) hp)
    (fun _ _ _ _ hq => hq)

end LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1PlacedBudget
