/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneBudget
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Callees
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeedTopBudget
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget

/-!
# Budget-Threaded Relocatable Callee Bundle for `SessionRecord::deserialize`

Defines and discharges the budget-threaded relocatable callee bundles `DeserializeCalleesPlaced` and
`DeserializeCalleesPlacedX` under `[LibsignalPlacement]` and `RustCliAllocBudget M`, covering
`decode_varint_slice` (block `76`), `int32::merge` (block `8`), `bytes::merge` (block `7`), and
`RawVec<Chain>::grow_one` (block `43`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.CalleesBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalHooks LibsignalPlacement lsmpl withLsCodeLoaded
  blkPC_7 blkPl_7 blkPC_8 blkPl_8 blkPC_43 blkPl_43 blkPC_76 blkPl_76
  lsRustNoAllocShimSym lsRustAllocSym lsRustReallocSym lsRustDeallocSym lsMemcpySym
  ls_hook_ok_of_mem ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain
)
open CryptoVerification.LibsignalTripleRatchet (
  decodeErrorHookStack framelessMemcpySpec noAllocShimSpec
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  subroutine_ok_withLsCl_of_plain subroutine_ok_withLsCl_of_withLsCodeLoaded
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (growOneSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneBudget (grow_one_placed_ok_of_noop)
open LibsignalBinary.Proofs.E2E.Record.DeserializeSeedTopBudget (PlacedDeserializeHooks)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget (
  bytes_merge_placed_ok_x
  hookSat_noAllocShimBudget_of_withVmPreserved
  hookSat_sessionShimBudget_of_withVmPreserved
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  vmPreserved_hookNoop
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserveBudget (do_reserve_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget (bytesVtableDrop_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget (bytesFromVec_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (
  DecodeVarintSlicePlacedOk DecodeVarintSlicePlacedOkX
  Int32MergePlacedOk Int32MergePlacedOkX
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (
  BytesMergePlacedOk BytesMergePlacedOkX
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget (
  bmMemcpy_placed_of_frameless bmShim_placed_of_base
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1Budget (
  bytes_merge_placed_ok_of_contracts
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudget (
  int32_merge_placed_ok int32_merge_placed_ok_x
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudgetAux (
  decode_varint_slow_placed_ok_with_stack_of_hooks
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget (
  decode_error_from_placed_ok decode_varint_slice_placed_ok decode_varint_slice_placed_ok_x
)

/-! ## Relocatable Callee Bundles -/

/-- Relocatable budget-threaded callee bundle for `SessionRecord::deserialize` at `(M, A, lim)`
with base `decodeErrorHookStack` profile (`decode_varint_slice`, `int32::merge`, `bytes::merge`,
and `RawVec<Chain>::grow_one`). -/
def DeserializeCalleesPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  DecodeVarintSlicePlacedOk A lim H ∧
    Int32MergePlacedOk A lim H ∧
    BytesMergePlacedOk A lim H ∧
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneSpec M A lim))

/-- Extended-stack (`decodeErrorHookStackX`) counterpart of `DeserializeCalleesPlaced`. -/
def DeserializeCalleesPlacedX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  DecodeVarintSlicePlacedOkX A lim H ∧
    Int32MergePlacedOkX A lim H ∧
    BytesMergePlacedOkX A lim H ∧
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneSpec M A lim))

/-! ## External Hook Bridges -/

theorem hookSat_withVmPreserved_noAllocShim_of_noop {H : String → Option (State → State)}
    {sym : String} (h : H sym = some hookNoop) :
    HookSat H sym (withVmPreserved noAllocShimSpec) :=
  hookSat_withVmPreserved
    ⟨hookNoop, h, hookNoop_ok fun _ _ _ hm => by simpa [noAllocShimSpec, hookNoop, retHook] using hm⟩
    fun f hf s => by cases h.symm.trans hf; exact vmPreserved_hookNoop s

theorem hookSat_sessionShimBudget_of_noop {H : String → Option (State → State)}
    {sym : String} (h : H sym = some hookNoop) :
    HookSat H sym sessionShimBudgetSpec :=
  hookSat_sessionShimBudget_of_withVmPreserved (hookSat_withVmPreserved_noAllocShim_of_noop h)

theorem hookSat_framelessMemcpy_of_allocMemcpyVm {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym allocMemcpyVmSpec) :
    HookSat H sym (withVmPreserved framelessMemcpySpec) := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  have hpre' : s0.mem ⊨ allocMemcpyVmSpec.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [withVmPreserved, framelessMemcpySpec, memcpyRegionSpec,
      allocMemcpyVmSpec] at hpre ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
    have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
    have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
      rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_bv, hlt⟩, by rwa [sepConj_assoc]⟩
  rcases hsat (dst, src, bs) R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [allocMemcpyVmSpec, withVmPreserved, framelessMemcpySpec,
      memcpyRegionSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0, hacp, hvm⟩, hm⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hacp.2.1⟩, by rwa [← sepConj_assoc]⟩
  · exact Or.inr hrest

/-! ## `bytes::merge` and Callee Bundle Discharge -/

/-- Relocatable `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#1]` (Block `7`)
meets `bytesMergePlacedSpec A lim` under `withVmPreserved`-lifted shim and `memcpy` hooks. -/
theorem bytes_merge_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym (withVmPreserved framelessMemcpySpec)) :
    BytesMergePlacedOk A lim H := by
  have hshim_s := hookSat_sessionShimBudget_of_withVmPreserved hshim
  have hshim_n := hookSat_noAllocShimBudget_of_withVmPreserved hshim
  exact bytes_merge_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (decode_error_from_placed_ok hshim_s halloc))
    (bmMemcpy_placed_of_frameless (ls_hook_ok_of_mem hmc))
    (bmShim_placed_of_base (ls_hook_ok_of_mem hshim_s))
    (subroutine_ok_withLsCl_of_plain (ls_hook_ok_of_mem halloc))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (decode_varint_slow_placed_ok_with_stack_of_hooks
        (errStack := decodeErrorHookStack) hshim_s halloc))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (decode_varint_slice_placed_ok hshim_s halloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (do_reserve_placed_ok hshim_n halloc hrealloc))
    (fun tmpPtr v =>
      subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok (callerProg := (blkPC_7).rebase (blkPl_7).base H) (i := 7)
          hdealloc (by decide) tmpPtr v v.length))

theorem bytes_merge_placed_ok_of_allocMemcpyVm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : H lsRustNoAllocShimSym = some hookNoop)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    BytesMergePlacedOk A lim H :=
  bytes_merge_placed_ok
    (hookSat_withVmPreserved_noAllocShim_of_noop hshim) halloc hrealloc hdealloc
    (hookSat_framelessMemcpy_of_allocMemcpyVm hmc)

theorem bytes_merge_placed_ok_x_of_allocMemcpyVm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : H lsRustNoAllocShimSym = some hookNoop)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    BytesMergePlacedOkX A lim H :=
  bytes_merge_placed_ok_x
    (hookSat_withVmPreserved_noAllocShim_of_noop hshim) halloc hrealloc hdealloc
    (hookSat_framelessMemcpy_of_allocMemcpyVm hmc)

/-- Discharges `DeserializeCalleesPlaced M A lim H` from explicit `allocMemcpyVmSpec` hook
hypotheses. -/
theorem deserializeCallees_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : H lsRustNoAllocShimSym = some hookNoop)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    DeserializeCalleesPlaced M A lim H :=
  have hshim_s := hookSat_sessionShimBudget_of_noop hshim
  ⟨decode_varint_slice_placed_ok hshim_s halloc,
    int32_merge_placed_ok hshim_s halloc,
    bytes_merge_placed_ok_of_allocMemcpyVm hshim halloc hrealloc hdealloc hmc,
    grow_one_placed_ok_of_noop hshim halloc hrealloc⟩

theorem deserializeCallees_placed_ok_of_frameless [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : H lsRustNoAllocShimSym = some hookNoop)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym (withVmPreserved framelessMemcpySpec)) :
    DeserializeCalleesPlaced M A lim H :=
  have hshim_s := hookSat_sessionShimBudget_of_noop hshim
  ⟨decode_varint_slice_placed_ok hshim_s halloc,
    int32_merge_placed_ok hshim_s halloc,
    bytes_merge_placed_ok (hookSat_withVmPreserved_noAllocShim_of_noop hshim)
      halloc hrealloc hdealloc hmc,
    grow_one_placed_ok_of_noop hshim halloc hrealloc⟩

/-- Discharges `DeserializeCalleesPlaced M A lim H` from `PlacedDeserializeHooks M A H`. -/
theorem deserializeCallees_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} (lim : BudgetLimits)
    {H : String → Option (State → State)}
    (hH : PlacedDeserializeHooks M A H) :
    DeserializeCalleesPlaced M A lim H :=
  deserializeCallees_placed_ok hH.shim (hH.alloc lim) (hH.realloc lim) (hH.dealloc lim) hH.memcpy

theorem deserializeCallees_placed_x_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : H lsRustNoAllocShimSym = some hookNoop)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    DeserializeCalleesPlacedX M A lim H :=
  have hshim_s := hookSat_sessionShimBudget_of_noop hshim
  ⟨decode_varint_slice_placed_ok_x hshim_s halloc,
    int32_merge_placed_ok_x hshim_s halloc,
    bytes_merge_placed_ok_x_of_allocMemcpyVm hshim halloc hrealloc hdealloc hmc,
    grow_one_placed_ok_of_noop hshim halloc hrealloc⟩

theorem deserializeCallees_placed_x_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} (lim : BudgetLimits)
    {H : String → Option (State → State)}
    (hH : PlacedDeserializeHooks M A H) :
    DeserializeCalleesPlacedX M A lim H :=
  deserializeCallees_placed_x_ok hH.shim (hH.alloc lim) (hH.realloc lim) (hH.dealloc lim) hH.memcpy

end LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.CalleesBudget
