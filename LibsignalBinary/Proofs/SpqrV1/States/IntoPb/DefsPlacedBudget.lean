/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Relocatable Budget Specifications and Stack/RO Bridges for `<States>::into_pb` (Block `334`)

Re-exports relocatable `RustCliAllocBudget M` specifications and prologue/epilogue lemmas from
`DefsBudget`, defines naming aliases aligned with `DefsPlaced`, and proves `withLsCodeLoaded`
stack-framing and `.rodata`-discharge bridges.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.States.IntoPb
  (StatesIntoPbGhost lsro_statesIntoPbJumpTablePlacedAt statesIntoPbJumpTablePlacedAt
   statesIntoPbStack statesIntoPbStackX)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (StatesIntoPbEnv StatesIntoPbPlacedOkExt StatesIntoPbPlacedOkX
   StatesIntoPbPlacedRoFreeOkX statesIntoPbPlacedRoFreeSpecX
   statesIntoPbPlacedRoFreeSpecXOfEnv
   statesIntoPbPlacedRoFreeSpecXOfEnv_of_placedSpecXOfEnv
   statesIntoPbPlacedSpec statesIntoPbPlacedSpecOfEnv
   statesIntoPbPlacedSpecX statesIntoPbPlacedSpecXOfEnv
   statesIntoPbPlacedSpecXOfEnv_of_statesIntoPbPlacedSpecOfEnv
   statesIntoPbPlacedSpecX_of_statesIntoPbPlacedSpec)

/-! ## 1. Re-Exports from `DefsPlaced` and `DefsBudget` -/

export CryptoVerification.SpqrV1.States.IntoPb
  (statesIntoPbJumpTablePlacedAt lsro_statesIntoPbJumpTablePlacedAt)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (nonFreeCount SpqrBoundedEvs StatesIntoPbEnv statesIntoPbPlacedSpecOfEnv statesIntoPbPlacedSpec)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (statesIntoPbVariantPlacedSpecOfEnv statesIntoPbVariantPlacedSpec
   statesIntoPbPlacedSpecXOfEnv statesIntoPbPlacedSpecX StatesIntoPbPlacedOkX)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (statesIntoPbPlacedRoFreeSpecXOfEnv statesIntoPbPlacedRoFreeSpecX
   StatesIntoPbPlacedOkExt StatesIntoPbPlacedRoFreeOkX StatesIntoPbAllocPlacedBudget)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (statesIntoPbPlacedSpecXOfEnv_of_statesIntoPbPlacedSpecOfEnv
   statesIntoPbPlacedSpecX_of_statesIntoPbPlacedSpec
   statesIntoPbPlacedRoFreeSpecXOfEnv_of_placedSpecXOfEnv)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (states_into_pb_prologue_placed sepWPp_of_states_into_pb_exit_placed
   sepWPp_of_states_into_pb_exit_cl_placed states_into_pb_prologue_60_placed
   states_into_pb_epilogue_placed)

/-! ## 2. Naming Aliases Matching `DefsPlaced.lean` -/

abbrev statesIntoPbPlacedRoSpecXOfEnv := @statesIntoPbPlacedSpecXOfEnv

abbrev statesIntoPbPlacedRoSpecX := @statesIntoPbPlacedSpecX

abbrev statesIntoPbPlacedInnerSpecXOfEnv := @statesIntoPbPlacedRoFreeSpecXOfEnv

abbrev statesIntoPbPlacedInnerSpecX := @statesIntoPbPlacedRoFreeSpecX

abbrev statesIntoPbPlacedRoSpecX_of_statesIntoPbPlacedSpec :=
  @statesIntoPbPlacedSpecX_of_statesIntoPbPlacedSpec

/-! ## 3. `withLsCodeLoaded` Stack-Framing Lifts and `Ok` Bridges -/

/-- Frame the unused bottom stack region (`statesIntoPbStack -> statesIntoPbStackX`) underneath
    `withLsCodeLoaded lsmpl`. -/
theorem withLsCodeLoaded_statesIntoPbPlacedSpecXOfEnv_of_statesIntoPbPlacedSpecOfEnv
    [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecOfEnv M A lim F Env))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F Env)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hle : statesIntoPbStack ≤ statesIntoPbStackX := by decide
  have hsplit : stackAt s0.sp statesIntoPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 statesIntoPbStackX)
        (statesIntoPbStackX - statesIntoPbStack) ∗
        stackAt s0.sp statesIntoPbStack := by
    have h1 := stackAt_split_bottom s0.sp statesIntoPbStack
      (statesIntoPbStackX - statesIntoPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 statesIntoPbStackX)
      (statesIntoPbStackX - statesIntoPbStack) ∗ R
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecOfEnv M A lim F Env)).pre (x, st) s0 ∗ R' := by
    dsimp only [withLsCodeLoaded, statesIntoPbPlacedSpecXOfEnv,
      statesIntoPbPlacedSpecOfEnv, R'] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, statesIntoPbPlacedSpecXOfEnv,
      statesIntoPbPlacedSpecOfEnv, R'] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem withLsCodeLoaded_statesIntoPbPlacedSpecX_of_statesIntoPbPlacedSpec
    [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec M A lim F))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecX M A lim F)) :=
  withLsCodeLoaded_statesIntoPbPlacedSpecXOfEnv_of_statesIntoPbPlacedSpecOfEnv h

theorem statesIntoPbPlacedRoFreeSpecX_of_placedSpecX [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecX M A lim F))) :
    subroutine_ok P addr (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoFreeSpecX M A lim F)) :=
  statesIntoPbPlacedRoFreeSpecXOfEnv_of_placedSpecXOfEnv h

/-- Lift `StatesIntoPbPlacedOkExt` (`statesIntoPbStack`) to `StatesIntoPbPlacedOkX`
    (`statesIntoPbStackX`, explicit `statesIntoPbJumpTablePlacedAt`). -/
theorem statesIntoPbPlacedOkX_of_statesIntoPbPlacedOkExt [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (h : StatesIntoPbPlacedOkExt M A lim F ext) :
    StatesIntoPbPlacedOkX M A lim F ext := by
  have h1 := withLsCodeLoaded_statesIntoPbPlacedSpecX_of_statesIntoPbPlacedSpec h
  have hprog : (blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext) =
      CryptoVerification.libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext) :=
    (inferInstance : IsLsBlockProg
      ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      334 (Rust.withPanics ext)).eq_blockProgram
  have hbase : (blkPl_334).base = lsmpl.base 334 := rfl
  rw [hprog, hbase] at h1
  exact h1

/-- Lift `StatesIntoPbPlacedOkExt` (`statesIntoPbStack`, explicit `statesIntoPbJumpTablePlacedAt`)
    to `StatesIntoPbPlacedRoFreeOkX` (`statesIntoPbStackX`, `.rodata`-free via `withLsCodeRoLoaded`). -/
theorem statesIntoPbPlacedRoFreeOkX_of_statesIntoPbPlacedOkExt [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (h : StatesIntoPbPlacedOkExt M A lim F ext) :
    StatesIntoPbPlacedRoFreeOkX M A lim F ext :=
  statesIntoPbPlacedRoFreeSpecX_of_placedSpecX
    (withLsCodeLoaded_statesIntoPbPlacedSpecX_of_statesIntoPbPlacedSpec h)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
