/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlaced

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Budget-Threaded Relocatable Contracts and Bridges

Re-exports canonical `PolyNextChunkEnv` budget specifications from `DefsBudget` and provides
`withLsCodeLoaded` `.rodata` contracts, cross-block caller contracts (`PolyNextChunkBlockOkX`,
`PolyNextChunkCallerOkX`), `.rodata` discharge lemmas, and envelope monotonicity bridges for
Block `416`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget

open Arm64 ProofLib
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalPlacement blkPC_416 blkPl_416
  extract_withLsCodeLoaded instIsLsBlockProg_416 libsignalSessionLib lsmpl withLsCodeLoaded
)
open CryptoVerification.LibsignalSpqrV1 (PolyEncoder)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded keys_ls_subroutine_ok_of_block_cro
  withLsCodeRoLoaded
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt chunkSize polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.NextChunk (
  PolyNextChunkGhost completePointsPolysPlacedAt polyNextChunkStack
  rodata_completePointsPolys_placed
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)

export LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget (
  nextChunkPrologueEvents
  NextChunkPrologueEnv
  nextChunkPrologueEnv_nonempty
  nextChunkEpilogueEvents
  NextChunkEpilogueEnv
  nextChunkEpilogueEnv_nonempty
  nextChunkEpilogueEvents_freeOnly
  computeAtScratchCap
  computeAtEvents
  computeAtEvents_satisfies_callEnv
  NextChunkPolysLoopEnv
  nextChunkPolysLoopEnv_nonempty
  NextChunkPolysTailByLenEnv
  nextChunkPolysTailByLenEnv_nonempty
  nextChunkFirstSlowIdx
  isPrecomputedBasisLen
  RepeatSeqEnv
  repeatSeqEnv_nonempty
  nextChunkBlockAEvents
  LagrangeSumStepEnv
  lagrangeSumStepEnv_nonempty
  FallbackBasisStepEnv
  fallbackBasisStepEnv_nonempty
  PointsToPolysIterEnv
  pointsToPolysIterEnv_nonempty
  PointsToPolysLoopEnv
  pointsToPolysLoopEnv_nonempty
  PolyNextChunkEnv
  polyNextChunkEnv_nonempty
  polyNextChunkPlacedSpecOfEnv
  polyNextChunkPlacedSpec
  polyNextChunkRodataPlacedSpecOfEnv
  polyNextChunkRodataPlacedSpec
  PolyNextChunkPlacedOkExtOfEnv
  PolyNextChunkPlacedOkExt
  PolyNextChunkRodataPlacedOkExtOfEnv
  PolyNextChunkRodataPlacedOkExt
)

/-! ## 1. `withLsCodeLoaded` `.rodata` & Cross-Block Caller Contract Abbreviations -/

/-- Parametric-envelope relocatable `[LibsignalPlacement]` contract for Block `416` with explicit
    `completePointsPolysPlacedAt` wrapped with `withLsCodeLoaded lsmpl` (matching
    `RodataPlaced.PolyNextChunkRodataPlacedOkExt`). -/
def PolyNextChunkRodataCodeLoadedOkExtOfEnv [LibsignalPlacement]
    (Env : PolyNextChunkGhost → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
    (blkPl_416).base
    (withLsCodeLoaded lsmpl (polyNextChunkRodataPlacedSpecOfEnv Env M A lim))

/-- Canonical `withLsCodeLoaded` relocatable `.rodata` contract for Block `416`. -/
abbrev PolyNextChunkRodataCodeLoadedOkExt [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  PolyNextChunkRodataCodeLoadedOkExtOfEnv PolyNextChunkEnv M A lim ext

/-- Parametric-envelope relocatable `[LibsignalPlacement]` contract on
    `libsignalSessionLib.blockProgram lsmpl 416 (Rust.withPanics ext)` at `lsmpl.base 416`. -/
def PolyNextChunkBlockOkXOfEnv [LibsignalPlacement]
    (Env : PolyNextChunkGhost → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 416 (Rust.withPanics ext))
    (lsmpl.base 416)
    (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpecOfEnv Env M A lim))

/-- Canonical `blockProgram 416` relocatable contract for `<PolyEncoder as Encoder>::next_chunk`. -/
abbrev PolyNextChunkBlockOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  PolyNextChunkBlockOkXOfEnv PolyNextChunkEnv M A lim ext

/-- Parametric-envelope cross-block caller contract for Block `416` (`lsmpl.base 416`) on an
    arbitrary caller program `callerProg` (e.g. `spqrSendPlacedProg ext`). -/
def PolyNextChunkCallerOkXOfEnv [LibsignalPlacement]
    (callerProg : Program)
    (Env : PolyNextChunkGhost → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  subroutine_ok callerProg (lsmpl.base 416)
    (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpecOfEnv Env M A lim))

/-- Canonical cross-block caller contract for Block `416` (`lsmpl.base 416`) on `callerProg`. -/
abbrev PolyNextChunkCallerOkX [LibsignalPlacement]
    (callerProg : Program)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  PolyNextChunkCallerOkXOfEnv callerProg PolyNextChunkEnv M A lim

/-! ## 2. `.rodata` Discharge, Cross-Block Transport & Envelope Weakening Bridges -/

/-- Discharge `completePointsPolysPlacedAt` from `LibsignalCodeRoLoaded` to convert
    `PolyNextChunkRodataCodeLoadedOkExtOfEnv` into `PolyNextChunkPlacedOkExtOfEnv`. -/
theorem polyNextChunkPlacedOkExt_of_rodata_codeLoaded [LibsignalPlacement]
    {Env : PolyNextChunkGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hro_ok : PolyNextChunkRodataCodeLoadedOkExtOfEnv Env M A lim ext) :
    PolyNextChunkPlacedOkExtOfEnv Env M A lim ext := by
  refine subroutine_ok_mono hro_ok (fun ⟨x, st⟩ R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hp
  dsimp only [polyNextChunkPlacedSpecOfEnv] at hpre
  dsimp only [withLsCodeLoaded, polyNextChunkRodataPlacedSpecOfEnv]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  refine ⟨hpre.1, ?_⟩
  have hro_pre := rodata_completePointsPolys_placed hro hpre.2
  rwa [show (memRegion x.outA chunkSize ∗
        polyEncoderAt A.repAlloc x.encA x.enc ∗
        completePointsPolysPlacedAt ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim st s0 ∗ stackAt s0.sp polyNextChunkStack) ∗ R =
      completePointsPolysPlacedAt ∗
        ((memRegion x.outA chunkSize ∗
          polyEncoderAt A.repAlloc x.encA x.enc ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool lim st s0 ∗ stackAt s0.sp polyNextChunkStack) ∗ R) by ac_rfl]

/-- Discharge `completePointsPolysPlacedAt` from `PolyNextChunkRodataPlacedOkExtOfEnv` into
    `PolyNextChunkPlacedOkExtOfEnv`. -/
theorem polyNextChunkPlacedOkExt_of_rodata [LibsignalPlacement]
    {Env : PolyNextChunkGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hro_ok : PolyNextChunkRodataPlacedOkExtOfEnv Env M A lim ext) :
    PolyNextChunkPlacedOkExtOfEnv Env M A lim ext := by
  refine subroutine_ok_mono hro_ok (fun ⟨x, st⟩ R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  obtain ⟨hcro, hpre⟩ := extract_withLsCodeRoLoaded hp
  dsimp only [polyNextChunkPlacedSpecOfEnv] at hpre
  dsimp only [withLsCodeRoLoaded, polyNextChunkRodataPlacedSpecOfEnv]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcro, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  refine ⟨hpre.1, ?_⟩
  have hro_pre := rodata_completePointsPolys_placed hcro.2 hpre.2
  rwa [show (memRegion x.outA chunkSize ∗
        polyEncoderAt A.repAlloc x.encA x.enc ∗
        completePointsPolysPlacedAt ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim st s0 ∗ stackAt s0.sp polyNextChunkStack) ∗ R =
      completePointsPolysPlacedAt ∗
        ((memRegion x.outA chunkSize ∗
          polyEncoderAt A.repAlloc x.encA x.enc ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool lim st s0 ∗ stackAt s0.sp polyNextChunkStack) ∗ R) by ac_rfl]

/-- Transport `PolyNextChunkPlacedOkExtOfEnv` onto `libsignalSessionLib.blockProgram lsmpl 416`. -/
theorem polyNextChunkBlockOkX_of_placedOkExt [LibsignalPlacement]
    {Env : PolyNextChunkGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hok : PolyNextChunkPlacedOkExtOfEnv Env M A lim ext) :
    PolyNextChunkBlockOkXOfEnv Env M A lim ext := by
  unfold PolyNextChunkBlockOkXOfEnv PolyNextChunkPlacedOkExtOfEnv at *
  exact (instIsLsBlockProg_416 (Rust.withPanics ext)).eq_blockProgram ▸ hok

/-- Transport `PolyNextChunkPlacedOkExtOfEnv` across blocks to any `[IsLsBlockProg callerProg i]`
    caller (`i < 619`, e.g. `spqrSendPlacedProg ext` at Block `427` or `124`). -/
theorem polyNextChunkCallerOkX_of_placedOkExt [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {Env : PolyNextChunkGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hok : PolyNextChunkPlacedOkExtOfEnv Env M A lim ext)
    (hi : i < 619 := by decide) :
    PolyNextChunkCallerOkXOfEnv callerProg Env M A lim :=
  keys_ls_subroutine_ok_of_block_cro (callerProg := callerProg) (j := 416) hok hi

/-- Envelope weakening for `polyNextChunkPlacedSpecOfEnv`: if `Env₁ x ⊆ Env₂ x` pointwise, any
    subroutine meeting `Env₁` also meets `Env₂` (`FitsEnv` contravariant, `post` covariant). -/
theorem subroutine_ok_polyNextChunkPlacedSpecOfEnv_mono [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {Env₁ Env₂ : PolyNextChunkGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hsub : ∀ x evs, Env₁ x evs → Env₂ x evs)
    (hok : subroutine_ok prog entry (polyNextChunkPlacedSpecOfEnv Env₁ M A lim)) :
    subroutine_ok prog entry (polyNextChunkPlacedSpecOfEnv Env₂ M A lim) := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · dsimp only [polyNextChunkPlacedSpecOfEnv] at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, FitsEnv.mono (hsub x) hp.1.2.2.2⟩, hp.2⟩
  · dsimp only [polyNextChunkPlacedSpecOfEnv] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hsub x evs hq.1.1, hq.1.2⟩, hq.2⟩

/-- Envelope weakening for `PolyNextChunkPlacedOkExtOfEnv`. -/
theorem polyNextChunkPlacedOkExtOfEnv_mono [LibsignalPlacement]
    {Env₁ Env₂ : PolyNextChunkGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hsub : ∀ x evs, Env₁ x evs → Env₂ x evs)
    (hok : PolyNextChunkPlacedOkExtOfEnv Env₁ M A lim ext) :
    PolyNextChunkPlacedOkExtOfEnv Env₂ M A lim ext := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hcro, hpre⟩ := extract_withLsCodeRoLoaded hp
    dsimp only [polyNextChunkPlacedSpecOfEnv] at hpre
    dsimp only [withLsCodeRoLoaded, polyNextChunkPlacedSpecOfEnv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, FitsEnv.mono (hsub x) hpre.1.2.2.2⟩, hpre.2⟩
  · dsimp only [withLsCodeRoLoaded, polyNextChunkPlacedSpecOfEnv] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hsub x evs hq.1.1, hq.1.2⟩, hq.2⟩

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
