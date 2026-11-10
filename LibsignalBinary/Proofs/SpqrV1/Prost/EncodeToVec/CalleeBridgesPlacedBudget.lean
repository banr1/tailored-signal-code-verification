/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.EncodedLenCodeSym
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLenBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# `PqRatchetState::encode_to_vec` (Block `426`): Budget-Threaded Placed Callee Bridges

Cross-block `[LibsignalPlacement]` transfer lemmas (`withStepInv` and `withStepInvVm`), placed
`VmPreserved` `encoded_len` bridges (Blocks `399`, `405`, `406`), and placed allocator/`memcpy`/varint
bridges into Block `426`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesPlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved allocMemcpyVmSpec
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPC_405 blkPl_405
   extract_withLsCodeLoaded libsignalMutatedBlocks ls_blockPlacement_ρ ls_externAt?_of_mem
   ls_hook_ok_of_mem ls_subroutine_ok_of_block lsMemcpySym lsmpl lsρ
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStack doReserveStackX sessionShimSpec)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open CryptoVerification.SpqrV1.ProtoRepr
  (EpochEncodedLenFits epochEncodedLen_entry_pinned_ok epochEncodedLenStack
   unchunkedEncodedLenStack v1StateJtSymLocal2)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (blkPC_426 blkPl_426 encodeToVecCalleeStackOf stackAt_callee_eq_unchunkedEncodedLen
   subroutine_ok_withStepInv withStepInv)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
   subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec noAllocShimSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (chainEncodedLenPinnedSpec epochEncodedLenPinnedSpec ls_subroutine_ok_plain_vmPreserved
   withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBudget
  (chainEncodedLen_local2_pinned_placed_ok_ext chainEncodedLen_local2_pinned_placed_ok_hooks)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateBudget
  (V1StateEncodedLenLocal2PinnedPlacedOkExt)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
  (encode_varint4_fit_placed_ok encode_varint4_fit_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (subroutine_ok_withStepInv_lscl subroutine_ok_withStepInvVm_lscl withStepInvVm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeVarintExactSpecOf epochEncLenStackSpecOf etvMemcpyRegionSpec
   rustAllocStackSpecOf shimStackSpecOf subroutine_ok_rustAllocStackSpecOf_of_budget
   subroutine_ok_rustAllocStackSpecOf_of_noOom subroutine_ok_shimStackSpecOf_of_rustAllocShimVm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (leafEncLen16Spec leafEncLen48Spec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

/-! ## 1. Cross-Block `subroutine_ok` Transfer into `Block 426` -/

/-- Transfer a plain block `j` `subroutine_ok` into `withStepInv s0 spec` on `Block 426`. -/
theorem etv_subroutine_ok_placed_of_plain [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee_prog : IsLsBlockProg calleeProg j H]
    {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) spec)
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base j)
      (withStepInv s0 spec) :=
  subroutine_ok_withStepInv_lscl hcl0
    (ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain hcallee)
      (by decide) hj hj_unmut)

/-- Transfer a `withLsCodeLoaded lsmpl spec` block `j` `subroutine_ok` into `withStepInv s0 spec`
on `Block 426`. -/
theorem etv_subroutine_ok_placed_of_lscl [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee_prog : IsLsBlockProg calleeProg j H]
    {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) (withLsCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base j)
      (withStepInv s0 spec) :=
  subroutine_ok_withStepInv_lscl hcl0
    (ls_subroutine_ok_of_block hcallee (by decide) hj hj_unmut)

/-- Transfer a plain block `j` `subroutine_ok` into `withStepInvVm s0 spec` on `Block 426`. -/
theorem etv_subroutine_ok_vm_placed_of_plain [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee_prog : IsLsBlockProg calleeProg j H]
    {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) spec)
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base j)
      (withStepInvVm s0 spec) :=
  subroutine_ok_withStepInvVm_lscl hcl0
    (ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain hcallee)
      (by decide) hj hj_unmut)

/-- Transfer a `withLsCodeLoaded lsmpl spec` block `j` `subroutine_ok` into `withStepInvVm s0 spec`
on `Block 426`. -/
theorem etv_subroutine_ok_vm_placed_of_lscl [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee_prog : IsLsBlockProg calleeProg j H]
    {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) (withLsCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base j)
      (withStepInvVm s0 spec) :=
  subroutine_ok_withStepInvVm_lscl hcl0
    (ls_subroutine_ok_of_block hcallee (by decide) hj hj_unmut)

/-! ## 2. Placed `encoded_len` Callee Bridges (`VmPreserved`) -/

theorem etv_chainEncodedLen_placed_ok_hooks [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 406)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)) :=
  etv_subroutine_ok_placed_of_lscl hcl0 (chainEncodedLen_local2_pinned_placed_ok_hooks A H)

theorem etv_chainEncodedLen_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (lsmpl.base 406)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)) :=
  etv_subroutine_ok_placed_of_lscl hcl0 (chainEncodedLen_local2_pinned_placed_ok_ext A ext)

theorem etv_v1StateEncodedLen_placed_ok_hooks [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hv1 : subroutine_ok ((blkPC_405).rebase (blkPl_405).base H) (blkPl_405).base
      (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A (lsρ v1StateJtSymLocal2)))) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 405)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (lsρ v1StateJtSymLocal2))) :=
  etv_subroutine_ok_placed_of_lscl hcl0 hv1

theorem etv_v1StateEncodedLen_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hv1 : V1StateEncodedLenLocal2PinnedPlacedOkExt A ext) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (lsmpl.base 405)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (lsρ v1StateJtSymLocal2))) :=
  etv_subroutine_ok_placed_of_lscl hcl0 hv1

theorem etv_epochEncodedLen_placed_ok_hooks [inst : LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 399)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)) := by
  have hep_blk : subroutine_ok ((CryptoVerification.blkPC_399).rebase (CryptoVerification.blkPl_399).base H)
      (CryptoVerification.blkPl_399).base (epochEncodedLenPinnedSpec A) :=
    ls_subroutine_ok_plain_vmPreserved (i := 399) (by decide +kernel)
      (hok := epochEncodedLen_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr ⟨rfl, rfl⟩⟩))
  have hep : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 399) (withLsCodeLoaded lsmpl (epochEncodedLenPinnedSpec A)) :=
    ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain hep_blk)
      (by decide) (by decide) (by decide)
  apply subroutine_ok_withStepInv_lscl hcl0
  refine subroutine_ok_outcome_intro fun ⟨a, g, ep⟩ R s hpc hrun hpre hal => ?_
  obtain ⟨hcl_s, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [epochEncLenStackSpecOf] at hpre
  rw [stackAt_callee_eq_unchunkedEncodedLen hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (160 + resStack)
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfit⟩, hm⟩
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl (epochEncodedLenPinnedSpec A)).pre
      ⟨a, g, ep⟩ s ∗ (F_rem ∗ R) := by
    dsimp only [withLsCodeLoaded, epochEncodedLenPinnedSpec, withVmPreserved,
      CryptoVerification.SpqrV1.ProtoRepr.epochEncodedLenPinnedSpec, EpochEncodedLenFits]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl_s, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono
      (Entails.of_eq (by dsimp [F_rem, epochEncodedLenStack, unchunkedEncodedLenStack]; sep_ac_rfl)) hm
  refine hep.mono_outcome ⟨a, g, ep⟩ (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, epochEncodedLenPinnedSpec, withVmPreserved,
      CryptoVerification.SpqrV1.ProtoRepr.epochEncodedLenPinnedSpec,
      epochEncLenStackSpecOf] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0f, htrf⟩, hmemf⟩
    rw [stackAt_callee_eq_unchunkedEncodedLen hres s.sp]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hvm, hx0f, htrf⟩, ?_⟩
    exact Satisfies.mono
      (Entails.of_eq (by dsimp [F_rem, epochEncodedLenStack, unchunkedEncodedLenStack]; sep_ac_rfl))
      hmemf
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem etv_epochEncodedLen_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (lsmpl.base 399)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)) :=
  etv_epochEncodedLen_placed_ok_hooks hres A (Rust.withPanics ext) s0 hcl0

/-! ## 3. Placed Allocator & `memcpy` Hook Bridges -/

theorem etv_handle_alloc_error_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) :
    ((blkPC_426).rebase (blkPl_426).base H).externAt?
      ((blkPl_426).ρ spqrHandleErrorSym) = some Rust.panicked :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.etv_handle_alloc_error_placed h_panic

theorem etv_shim_placed_ok [LibsignalPlacement] {resStack : Nat}
    {H : String → Option (State → State)}
    (hshim_sat : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (s0 : State) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ spqrRustNoAllocShimSym)
      (withStepInv s0 (shimStackSpecOf resStack)) := by
  rw [ls_blockPlacement_ρ]
  have hshim : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec :=
    ls_hook_ok_of_mem hshim_sat
  apply subroutine_ok_withStepInv s0
  refine subroutine_ok_outcome_intro fun u R s hpc hrun hpre hal => ?_
  dsimp only [shimStackSpecOf] at hpre
  have hpre' : s.mem ⊨
      noAllocShimSpec.pre u s ∗ (stackAt s.sp (encodeToVecCalleeStackOf resStack) ∗ R) := by
    dsimp only [noAllocShimSpec, noAllocShimBudgetSpec]
    rw [emp_sepConj]
    exact hpre
  refine hshim.mono_outcome u (stackAt s.sp (encodeToVecCalleeStackOf resStack) ∗ R)
    s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [noAllocShimSpec, noAllocShimBudgetSpec, shimStackSpecOf] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.2, hpost.1.1⟩, hpost.2⟩
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem etv_shim_placed_ok_of_vm [LibsignalPlacement] {resStack : Nat}
    {H : String → Option (State → State)}
    (hshim_sat : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (s0 : State) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ spqrRustNoAllocShimSym)
      (withStepInv s0 (shimStackSpecOf resStack)) := by
  rw [ls_blockPlacement_ρ]
  exact subroutine_ok_withStepInv s0
    (subroutine_ok_shimStackSpecOf_of_rustAllocShimVm resStack (ls_hook_ok_of_mem hshim_sat))

theorem stackAt_callee_eq_allocHook_placed {resStack : Nat}
    (hlow : allocHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hhigh : encodeToVecCalleeStackOf resStack < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack))
        (encodeToVecCalleeStackOf resStack - allocHookStack) ∗
        stackAt sp1 allocHookStack :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.stackAt_callee_eq_allocHook_placed hlow hhigh sp1

theorem etv_rustAlloc_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hlow : allocHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hhigh : encodeToVecCalleeStackOf resStack < 2 ^ 64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (halloc_sat : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (s0 : State) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ spqrRustAllocSym)
      (withStepInv s0 (rustAllocStackSpecOf resStack A lim)) := by
  rw [ls_blockPlacement_ρ]
  exact subroutine_ok_withStepInv s0
    (subroutine_ok_rustAllocStackSpecOf_of_budget hlow (Nat.le_of_lt hhigh)
      (ls_hook_ok_of_mem halloc_sat))

theorem etv_rustAlloc_placed_ok_of_noOom [LibsignalPlacement] {resStack : Nat}
    (hlow : allocHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hhigh : encodeToVecCalleeStackOf resStack < 2 ^ 64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (halloc_sat : HookSat H spqrRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (s0 : State) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ spqrRustAllocSym)
      (withStepInv s0 (rustAllocStackSpecOf resStack A lim)) := by
  rw [ls_blockPlacement_ρ]
  exact subroutine_ok_withStepInv s0
    (subroutine_ok_rustAllocStackSpecOf_of_noOom hlow (Nat.le_of_lt hhigh)
      (ls_hook_ok_of_mem halloc_sat))

theorem etv_memcpy_placed_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hmc_sat : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy")
      etvMemcpyRegionSpec := by
  rw [ls_blockPlacement_ρ]
  exact ls_hook_ok_of_mem hmc_sat

theorem etv_memcpy_placed_ok_of_allocVm [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hmc_sat : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy")
      etvMemcpyRegionSpec := by
  rw [ls_blockPlacement_ρ]
  exact subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm (ls_hook_ok_of_mem hmc_sat)

/-! ## 4. Placed `encode_varint [local#4]` (`Block 292`) & Leaf `encoded_len` Bridges -/

theorem etv_encodeVarint_exact_of_fit_placed {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hfit_ok : subroutine_ok prog call_pc (withStepInv s0 (encodeVarintFitSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)) :=
  CalleeBridgesBudget.etv_encodeVarint_exact_of_fit hres hfit_ok

theorem etv_encodeVarint_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStack A lim)) :=
  etv_encodeVarint_exact_of_fit_placed (by decide)
    (etv_subroutine_ok_placed_of_lscl hcl0
      (encode_varint4_fit_placed_ok h_panic hshim halloc hrealloc))

theorem etv_encodeVarint_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStackX A lim)) :=
  etv_encodeVarint_exact_of_fit_placed (by decide)
    (etv_subroutine_ok_placed_of_lscl hcl0
      (encode_varint4_fit_placed_ok_x h_panic hshim halloc hrealloc))

theorem etv_leafEncLen16_withStepInv_placed {G M : Type}
    {reprAt : G → BitVec 64 → M → SepProp} {encLen : M → Nat}
    {prog : Program} {call_pc : BitVec 64} {s0 : State}
    (hok : subroutine_ok prog call_pc (leafEncLen16Spec reprAt encLen)) :
    subroutine_ok prog call_pc (withStepInv s0 (leafEncLen16Spec reprAt encLen)) :=
  CalleeBridgesBudget.etv_leafEncLen16_withStepInv hok

theorem etv_leafEncLen48_withStepInv_placed {G M : Type}
    {reprAt : G → BitVec 64 → M → SepProp} {encLen : M → Nat}
    {prog : Program} {call_pc : BitVec 64} {s0 : State}
    (hok : subroutine_ok prog call_pc (leafEncLen48Spec reprAt encLen)) :
    subroutine_ok prog call_pc (withStepInv s0 (leafEncLen48Spec reprAt encLen)) :=
  CalleeBridgesBudget.etv_leafEncLen48_withStepInv hok

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesPlacedBudget
