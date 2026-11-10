/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2ClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
import LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget
import LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget
import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget

/-!
# `prost::encoding::bytes::merge [local#3]` (Block `290`): Budget-Threaded Code-Loaded Verification

Discharges the `withLsCodeLoaded` callee contracts of `bytes_merge_3_placed_ok_of_contracts` using
`decodeVarint2_cl_placed_ok` (Block `291`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofClPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsmpl
   blkPC_290 blkPl_290
   ls_subroutine_ok_cl_of_plain ls_subroutine_ok_cl_of_block ls_hook_ok_of_mem
   lsMemcpySym lsRustNoAllocShimSym lsRustAllocSym lsRustReallocSym
   lsRustDeallocSym lsHandleErrorSym)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost subroutine_ok_withLsCl_of_plain subroutine_ok_withLsCl_of_withLsCodeLoaded)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (do_reserve_7_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget
  (bytesMerge3ProtoRawSpec bytesMerge3RawSpec bytesMerge3RawSpecOfEnv2
   bytes_merge_3_placed_ok_of_contracts bytes_merge_3_proto_placed_ok_of_contracts
   subroutine_ok_bytesMerge3OfEnv2_of_spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2ClPlacedBudget
  (decodeVarint2_cl_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec
   subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget
   subroutine_ok_noAllocShim_of_sessionShimBudget)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget (bytesVtableDrop_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget (bytesFromVec_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (BytesMergeEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
  (decode_error_from_placed_ok)

private theorem hookSat_noAllocShim_of_sessionShimBudget
    {H : String → Option (State → State)} {name : String}
    (h : HookSat H name sessionShimBudgetSpec) :
    HookSat H name noAllocShimBudgetSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
      noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

/-- Code-loaded `HookSat` verification of `bytes::merge [local#3]` (Block `290`) under
`[LibsignalPlacement]` with zero cross-block hypotheses. -/
theorem bytes_merge_3_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (blkPl_290).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)) :=
  bytes_merge_3_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (decode_error_from_placed_ok hshim halloc))
    (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget (ls_hook_ok_of_mem hmc))
    (subroutine_ok_noAllocShim_of_sessionShimBudget (ls_hook_ok_of_mem hshim))
    (subroutine_ok_withLsCl_of_plain (ls_hook_ok_of_mem halloc))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_290).rebase (blkPl_290).base H) (j := 291)
      (decodeVarint2_cl_placed_ok hshim halloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (do_reserve_7_placed_ok hpanic_raw (hookSat_noAllocShim_of_sessionShimBudget hshim)
        halloc hrealloc))
    (fun tmpPtr v =>
      subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok hdealloc (by decide) tmpPtr v v.length))

/-- Envelope-parameterized code-loaded `HookSat` verification of `bytes::merge [local#3]`
(Block `290`). -/
theorem bytes_merge_3_cl_placed_ok_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {PreEnv PostEnv : BytesMergeGhost → List AllocEvent → Prop}
    (hPre : ∀ x evs, BytesMergeEnv x evs → PreEnv x evs)
    (hPost : ∀ x evs, BytesMergeEnv x evs → PostEnv x evs)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (blkPl_290).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecOfEnv2 A lim PreEnv PostEnv)) :=
  subroutine_ok_bytesMerge3OfEnv2_of_spec hPre hPost
    (bytes_merge_3_cl_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_raw)

/-- `Proto.mergeBytes` form of `bytes_merge_3_cl_placed_ok`. -/
theorem bytes_merge_3_proto_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (blkPl_290).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A lim)) :=
  bytes_merge_3_proto_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (decode_error_from_placed_ok hshim halloc))
    (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget (ls_hook_ok_of_mem hmc))
    (subroutine_ok_noAllocShim_of_sessionShimBudget (ls_hook_ok_of_mem hshim))
    (subroutine_ok_withLsCl_of_plain (ls_hook_ok_of_mem halloc))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_290).rebase (blkPl_290).base H) (j := 291)
      (decodeVarint2_cl_placed_ok hshim halloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (do_reserve_7_placed_ok hpanic_raw (hookSat_noAllocShim_of_sessionShimBudget hshim)
        halloc hrealloc))
    (fun tmpPtr v =>
      subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok hdealloc (by decide) tmpPtr v v.length))

end LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofClPlacedBudget
