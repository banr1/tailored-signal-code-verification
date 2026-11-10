/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Drop.DropCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlacedBudget
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs

/-!
# Budget-Threaded Code-Loaded `[LibsignalPlacement]` Verification of `spqr::decode_state` (`Block 325`)

Instantiates `decodeState_cl_placed_ok_ofEnv` and `decodeState_cl_placed_ok` with
`canonicalV1InnerHeap`, wiring budget-threaded code-loaded own-block callee contracts into
`spqr_decode_state_cl_ofEnv` and `spqr_decode_state_cl`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement
   blkPC_261 blkPC_263 blkPC_267 blkPC_270 blkPC_290 blkPC_291 blkPC_356
   blkPl_261 blkPl_263 blkPl_267 blkPl_270 blkPl_290 blkPl_291 blkPl_356
   libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib
   ls_subroutine_ok_cl_of_block ls_subroutine_ok_of_block lsmpl lsρ
   withLsCl withLsCodeLoaded)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (keys_ls_subroutine_ok_of_block_cro sessionMemcpySpec withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Drop
  (dropStack96 optProtoInnerStateJumpTablePlacedAt optProtoInnerStateSize protoPqRatchetStateSize)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (blkPC_294 blkPC_299 blkPl_294 blkPl_299
   v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost canonicalV1InnerHeap decodeStatePlacedEntry decodeStatePlacedProg
   dropOptProtoInnerStateStack of_cap_inner_ok of_drop_inner_canonical
   optProtoInnerStateAt_canonical_eq_drop protoPqRatchetStateAt_canonical_eq_drop)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (bytesMerge3RawBudgetSpec skipField3BudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (growOneStrideFullSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget (v1StateMergePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv chainParamsMergeSpec epochDirectionMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStatePlacedOk DecodeStatePlacedOkOfEnv DecodeStatePlacedOkX
   decodeStatePlacedSpecX dropOptProtoInnerStatePlacedSpec dropProtoPqRatchetStatePlacedSpec
   spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlaced DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlacedBudget
  (decodeState_cl_placed_ok decodeState_cl_placed_ok_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup

/-! ## 1. Canonical Representation Bridges for `Drop` Specifications under `withLsCl` -/

/-- Lift `subroutine_ok` for `withLsCl lsmpl (ProtoTopBudget.dropOptProtoInnerStatePlacedSpec M A lim)`
to `withLsCl lsmpl (SpecsPlacedBudget.dropOptProtoInnerStatePlacedSpec canonicalV1InnerHeap A lim)`. -/
theorem dropOptProtoInnerState_canonical_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 267)
      (withLsCl lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropOptProtoInnerStatePlacedSpec M A lim))) :
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec canonicalV1InnerHeap A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨a, opt⟩, st⟩ R s0 hpc hrun hpre halign => ?_
  dsimp only [withLsCl, dropOptProtoInnerStatePlacedSpec, v1StateJumpTablesPlacedAt] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [optProtoInnerStateAt_canonical_eq_drop, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hm⟩
  let R' := v1StateMergeJumpTablePlacedExpanded ∗ R
  have hpre' : s0.mem ⊨
      (withLsCl lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropOptProtoInnerStatePlacedSpec M A lim)).pre
        (⟨a, opt⟩, st) s0 ∗ R' := by
    dsimp only [withLsCl,
      LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropOptProtoInnerStatePlacedSpec,
      optProtoInnerStateSize, dropStack96, dropOptProtoInnerStateStack, R']
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, Satisfies.mono (Entails.of_eq ?_) hm⟩
    ac_rfl
  refine (hdrop.to_outcome (⟨a, opt⟩, st) R' s0 hpc hrun hpre' halign).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, Satisfies.mono ?_ hpost⟩
    dsimp only [withLsCl,
      LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropOptProtoInnerStatePlacedSpec,
      dropOptProtoInnerStatePlacedSpec, v1StateJumpTablesPlacedAt,
      optProtoInnerStateSize, dropStack96, dropOptProtoInnerStateStack, R']
    rw [sepConj_assoc, sepConj_assoc]
    refine sepConj_mono_right ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro evs
    have hfront :
        (⌜sf.trace = s0.trace ∧ LibsignalBinary.Heap.AllocCallPreserved s0 sf ∧
            LibsignalBinary.Heap.FreeOnlyEvs evs⌝ ∗
          memRegion a 224 ∗
          optProtoInnerStateJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp 4192) ∗
          (v1StateMergeJumpTablePlacedExpanded ∗ R) =
        ⌜sf.trace = s0.trace ∧ LibsignalBinary.Heap.AllocCallPreserved s0 sf ∧
            LibsignalBinary.Heap.FreeOnlyEvs evs⌝ ∗
          ((memRegion a 224 ∗
            (v1StateMergeJumpTablePlacedExpanded ∗ optProtoInnerStateJumpTablePlacedAt) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp 4192) ∗ R) := by ac_rfl
    rw [hfront]
    apply Entails.pure_left; rintro ⟨htr, _, hfree⟩
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_right evs ?_
    conv_rhs => rw [sepConj_assoc]
    exact Entails.pure_right (And.intro htr hfree) (Entails.of_eq (by ac_rfl))
  · dsimp only [withLsCl,
      LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropOptProtoInnerStatePlacedSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCl,
      LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropOptProtoInnerStatePlacedSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-- Lift `subroutine_ok` for `withLsCl lsmpl (ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec M A lim)`
to `withLsCl lsmpl (SpecsPlacedBudget.dropProtoPqRatchetStatePlacedSpec canonicalV1InnerHeap A lim)`. -/
theorem dropProtoPqRatchetState_canonical_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 270)
      (withLsCl lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec M A lim))) :
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 270)
      (withLsCl lsmpl (dropProtoPqRatchetStatePlacedSpec canonicalV1InnerHeap A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨a, pqr⟩, st⟩ R s0 hpc hrun hpre halign => ?_
  dsimp only [withLsCl, dropProtoPqRatchetStatePlacedSpec, v1StateJumpTablesPlacedAt] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [protoPqRatchetStateAt_canonical_eq_drop, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hm⟩
  let R' := v1StateMergeJumpTablePlacedExpanded ∗ R
  have hpre' : s0.mem ⊨
      (withLsCl lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec M A lim)).pre
        (⟨a, pqr⟩, st) s0 ∗ R' := by
    dsimp only [withLsCl,
      LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec,
      protoPqRatchetStateSize, dropStack96, dropOptProtoInnerStateStack, R']
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, Satisfies.mono (Entails.of_eq ?_) hm⟩
    ac_rfl
  refine (hdrop.to_outcome (⟨a, pqr⟩, st) R' s0 hpc hrun hpre' halign).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, Satisfies.mono ?_ hpost⟩
    dsimp only [withLsCl,
      LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec,
      dropProtoPqRatchetStatePlacedSpec, v1StateJumpTablesPlacedAt,
      protoPqRatchetStateSize, dropStack96, dropOptProtoInnerStateStack, R']
    rw [sepConj_assoc, sepConj_assoc]
    refine sepConj_mono_right ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro evs
    have hfront :
        (⌜sf.trace = s0.trace ∧ LibsignalBinary.Heap.AllocCallPreserved s0 sf ∧
            LibsignalBinary.Heap.FreeOnlyEvs evs⌝ ∗
          memRegion a 352 ∗
          optProtoInnerStateJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp 4192) ∗
          (v1StateMergeJumpTablePlacedExpanded ∗ R) =
        ⌜sf.trace = s0.trace ∧ LibsignalBinary.Heap.AllocCallPreserved s0 sf ∧
            LibsignalBinary.Heap.FreeOnlyEvs evs⌝ ∗
          ((memRegion a 352 ∗
            (v1StateMergeJumpTablePlacedExpanded ∗ optProtoInnerStateJumpTablePlacedAt) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp 4192) ∗ R) := by ac_rfl
    rw [hfront]
    apply Entails.pure_left; rintro ⟨htr, _, hfree⟩
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_right evs ?_
    conv_rhs => rw [sepConj_assoc]
    exact Entails.pure_right (And.intro htr hfree) (Entails.of_eq (by ac_rfl))
  · dsimp only [withLsCl,
      LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCl,
      LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-! ## 2. Canonical `DecodeStateCalleeContractsClPlaced` & `DecodeStateCalleeContractsClPlacedX` Assembly -/

/-- Assemble `DecodeStateCalleeContractsClPlaced canonicalV1InnerHeap A lim ext` from callee
contracts on `Block 325`. -/
theorem mkDecodeStateCalleeContractsClPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved (libcMemcpySpec hookStack)))
    (hsession_memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved (sessionMemcpySpec hookStack)))
    (hfrom : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hpush : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hvarint : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hskip : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim)))
    (hcp : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A lim)))
    (hgrow : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 356) (withLsCodeLoaded lsmpl (growOneStrideFullSpec M A lim 112 8)))
    (hdrop_inner : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 267)
      (withLsCl lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropOptProtoInnerStatePlacedSpec M A lim)))
    (hdrop_pqr : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 270)
      (withLsCl lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec M A lim))) :
    DecodeStateCalleeContractsClPlaced canonicalV1InnerHeap A lim ext where
  of_drop_inner := of_drop_inner_canonical A.repAlloc
  of_cap_inner := of_cap_inner_ok A.repAlloc
  dealloc := hdealloc
  memcpy := hmemcpy
  session_memcpy := hsession_memcpy
  decodeErrorFrom := hfrom
  decodeErrorPush := hpush
  decodeVarint2 := hvarint
  skipField3 := hskip
  chainParamsMerge := hcp
  growOneChainEpoch := hgrow
  dropOptProtoInnerState := dropOptProtoInnerState_canonical_cl_placed_ok hdrop_inner
  dropProtoPqRatchetState := dropProtoPqRatchetState_canonical_cl_placed_ok hdrop_pqr

private theorem ls_subroutine_ok_of_blockProgram_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeLoaded lsmpl spec) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (hcallee_prog := ⟨rfl, hext_j⟩)
    (bi := 619) (bj := 619) hcallee hi hj hj_unmut

private theorem ls_subroutine_ok_cl_of_blockProgram_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCl lsmpl spec) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg) (hcallee_prog := ⟨rfl, hext_j⟩)
    (bi := 619) (bj := 619) hcallee hi hj hj_unmut

private theorem ls_subroutine_ok_cro_of_blockProgram_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  keys_ls_subroutine_ok_of_block_cro (callerProg := callerProg) (hcallee_prog := ⟨rfl, hext_j⟩)
    (bi := 619) (bj := 619) hcallee hi hj hj_unmut

/-- Assemble `DecodeStateCalleeContractsClPlacedX canonicalV1InnerHeap A lim ext` from own-block
code-loaded contracts on `libsignalSessionLib.blockProgram lsmpl <j> (Rust.withPanics ext)`. -/
theorem mkDecodeStateCalleeContractsClPlacedX_of_blocks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved (libcMemcpySpec hookStack)))
    (hsession_memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved (sessionMemcpySpec hookStack)))
    (hfrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hpush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hvarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hskip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim)))
    (hcp : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A lim)))
    (hgrow : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 356 (Rust.withPanics ext))
      (lsmpl.base 356) (withLsCodeLoaded lsmpl (growOneStrideFullSpec M A lim 112 8)))
    (hdrop_inner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropOptProtoInnerStatePlacedSpec M A lim)))
    (hdrop_pqr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hbytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hed : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A lim)))
    (hv1 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim))) :
    DecodeStateCalleeContractsClPlacedX canonicalV1InnerHeap A lim ext where
  toDecodeStateCalleeContractsClPlaced :=
    mkDecodeStateCalleeContractsClPlaced hdealloc hmemcpy hsession_memcpy
      (ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_261).rebase (blkPl_261).base (fun _ => none))) hfrom)
      (ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (CryptoVerification.RecordCodecs.Placed.blkPC_257).rebase
          (CryptoVerification.RecordCodecs.Placed.blkPl_257).base (fun _ => none))) hpush)
      (ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_291).rebase (blkPl_291).base (fun _ => none))) hvarint)
      (ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_263).rebase (blkPl_263).base (fun _ => none))) hskip)
      (ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_294).rebase (blkPl_294).base (fun _ => none))) hcp)
      (ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_356).rebase (blkPl_356).base (fun _ => none))) hgrow)
      (ls_subroutine_ok_cl_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_267).rebase (blkPl_267).base (fun _ => none))) hdrop_inner)
      (ls_subroutine_ok_cl_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_270).rebase (blkPl_270).base (fun _ => none))) hdrop_pqr)
  bytesMerge3 :=
    ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (blkPC_290).rebase (blkPl_290).base (fun _ => none))) hbytes
  epochDirectionMerge :=
    ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (blkPC_299).rebase (blkPl_299).base (fun _ => none))) hed
  v1StateMerge :=
    ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog :=
        (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_298).rebase
          (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_298).base (fun _ => none))) hv1

/-! ## 3. Own-Block Code-Loaded Theorems (`spqr_decode_state_cl_ok_x{_ofEnv,}` & `spqr_decode_state_cl{_ofEnv,}`) -/

/-- Envelope-parameterized own-block code-loaded `spqr::decode_state` (`Block 325`) theorem on
`decodeStatePlacedProg ext` (`DecodeStatePlacedOkOfEnv canonicalV1InnerHeap A lim PreEnv PostEnv ext`),
taking own-block code-loaded contracts for all cross-block callees. -/
theorem spqr_decode_state_cl_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hpre_imp : ∀ x evs, DecodeStateEnv x evs → PreEnv x evs)
    (hpost_imp : ∀ x evs, DecodeStateEnv x evs → PostEnv x evs)
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved (libcMemcpySpec hookStack)))
    (hsession_memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved (sessionMemcpySpec hookStack)))
    (hfrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hpush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hvarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hskip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim)))
    (hcp : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A lim)))
    (hgrow : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 356 (Rust.withPanics ext))
      (lsmpl.base 356) (withLsCodeLoaded lsmpl (growOneStrideFullSpec M A lim 112 8)))
    (hdrop_inner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropOptProtoInnerStatePlacedSpec M A lim)))
    (hdrop_pqr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hbytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hed : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A lim)))
    (hv1 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim))) :
    DecodeStatePlacedOkOfEnv canonicalV1InnerHeap A lim PreEnv PostEnv ext :=
  decodeState_cl_placed_ok_ofEnv hpre_imp hpost_imp
    (mkDecodeStateCalleeContractsClPlacedX_of_blocks hdealloc hmemcpy hsession_memcpy
      hfrom hpush hvarint hskip hcp hgrow hdrop_inner hdrop_pqr hbytes hed hv1)

/-- Own-block code-loaded `spqr::decode_state` (`Block 325`) theorem on `decodeStatePlacedProg ext`
(`DecodeStatePlacedOkX canonicalV1InnerHeap A lim ext`), taking own-block code-loaded contracts for
all cross-block callees. -/
theorem spqr_decode_state_cl_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved (libcMemcpySpec hookStack)))
    (hsession_memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved (sessionMemcpySpec hookStack)))
    (hfrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hpush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hvarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hskip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim)))
    (hcp : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A lim)))
    (hgrow : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 356 (Rust.withPanics ext))
      (lsmpl.base 356) (withLsCodeLoaded lsmpl (growOneStrideFullSpec M A lim 112 8)))
    (hdrop_inner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropOptProtoInnerStatePlacedSpec M A lim)))
    (hdrop_pqr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hbytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hed : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A lim)))
    (hv1 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim))) :
    DecodeStatePlacedOkX canonicalV1InnerHeap A lim ext :=
  decodeState_cl_placed_ok
    (mkDecodeStateCalleeContractsClPlacedX_of_blocks hdealloc hmemcpy hsession_memcpy
      hfrom hpush hvarint hskip hcp hgrow hdrop_inner hdrop_pqr hbytes hed hv1)

/-- Envelope-parameterized own-block code-loaded `spqr::decode_state` (`Block 325`) theorem on
`libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext)`. -/
theorem spqr_decode_state_cl_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hpre_imp : ∀ x evs, DecodeStateEnv x evs → PreEnv x evs)
    (hpost_imp : ∀ x evs, DecodeStateEnv x evs → PostEnv x evs)
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved (libcMemcpySpec hookStack)))
    (hsession_memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved (sessionMemcpySpec hookStack)))
    (hfrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hpush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hvarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hskip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim)))
    (hcp : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A lim)))
    (hgrow : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 356 (Rust.withPanics ext))
      (lsmpl.base 356) (withLsCodeLoaded lsmpl (growOneStrideFullSpec M A lim 112 8)))
    (hdrop_inner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropOptProtoInnerStatePlacedSpec M A lim)))
    (hdrop_pqr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hbytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hed : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A lim)))
    (hv1 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim PreEnv PostEnv)) := by
  have hok := spqr_decode_state_cl_ok_x_ofEnv hpre_imp hpost_imp hdealloc hmemcpy hsession_memcpy
    hfrom hpush hvarint hskip hcp hgrow hdrop_inner hdrop_pqr hbytes hed hv1
  dsimp only [DecodeStatePlacedOkOfEnv, decodeStatePlacedProg, decodeStatePlacedEntry] at hok
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))] at hok
  exact hok

/-- Own-block code-loaded `spqr::decode_state` (`Block 325`) theorem on
`libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext)`. -/
theorem spqr_decode_state_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved (libcMemcpySpec hookStack)))
    (hsession_memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved (sessionMemcpySpec hookStack)))
    (hfrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hpush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hvarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hskip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim)))
    (hcp : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A lim)))
    (hgrow : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 356 (Rust.withPanics ext))
      (lsmpl.base 356) (withLsCodeLoaded lsmpl (growOneStrideFullSpec M A lim 112 8)))
    (hdrop_inner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropOptProtoInnerStatePlacedSpec M A lim)))
    (hdrop_pqr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget.dropProtoPqRatchetStatePlacedSpec M A lim)))
    (hbytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hed : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A lim)))
    (hv1 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX canonicalV1InnerHeap A lim)) :=
  spqr_decode_state_cl_ofEnv (fun _ _ h => h) (fun _ _ h => h) hdealloc hmemcpy hsession_memcpy
    hfrom hpush hvarint hskip hcp hgrow hdrop_inner hdrop_pqr hbytes hed hv1

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlacedBudget
