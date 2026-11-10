/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5Placed
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`): Shared `RustCliAllocBudget` Helpers for Arms 7, 8, and 9

Re-exports `StatesIntoPbAllocPlacedBudget` and `RustAlloc`-generic `vecU8` / `Ct1Sent` /
`EkReceivedCt1Sampled` helpers from `Part5.lean`, and provides `[LibsignalPlacement]` Block `334`
hook projections and non-null branch simplification eliminating the `+1700` / `+884` OOM panic blocks
under `FitsEvents`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.SpqrV1.Alloc
  (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Poly.DecoderPb (spqrRustDeallocSym)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (StatesIntoPbAllocPlacedBudget)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec noAllocShimBudgetSpec
   subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget
   subroutine_ok_noAllocShim_of_sessionShimBudget)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
   subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
   subroutine_ok_sessionShimBudget_of_rustAllocShimVm)

/-! ## 1. Allocator Hook Bundle and Re-Exports of `RustAlloc`-Generic `Part5` Helpers -/

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget (StatesIntoPbAllocPlacedBudget)

abbrev StatesIntoPbAllocPlaced := @StatesIntoPbAllocPlacedBudget

abbrev ofNat_lt_2pow63_msb_zero :=
  @CryptoVerification.SpqrV1.States.IntoPb.ofNat_lt_2pow63_msb_zero
abbrev ofNat_lt_2pow63_and_highBit_zero :=
  @CryptoVerification.SpqrV1.States.IntoPb.ofNat_lt_2pow63_and_highBit_zero
abbrev ofNat_lt_2pow63_lsr63_zero :=
  @CryptoVerification.SpqrV1.States.IntoPb.ofNat_lt_2pow63_lsr63_zero
abbrev ofNat_beq_zero_false' :=
  @CryptoVerification.SpqrV1.States.IntoPb.ofNat_beq_zero_false'
abbrev ofNat_ne_zero_true :=
  @CryptoVerification.SpqrV1.States.IntoPb.ofNat_ne_zero_true
abbrev vecU8CloneTail :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8CloneTail
abbrev vecU8_expose_clone :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8_expose_clone
abbrev pointsToBytes_entails_memRegion' :=
  @CryptoVerification.SpqrV1.States.IntoPb.pointsToBytes_entails_memRegion'
abbrev vecU8CloneTail_entails_dealloc :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8CloneTail_entails_dealloc
abbrev sepWPp_pure_mid :=
  @CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.sepWPp_pure_mid
abbrev seq_clean :=
  @CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean
abbrev vecU8Buf_nil_intro' :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8Buf_nil_intro'
abbrev vecU8Buf_of_exact_alloc' :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8Buf_of_exact_alloc'
abbrev vecU8_of_header_buf :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8_of_header_buf
abbrev vecU8Heap_nil_intro :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8Heap_nil_intro
abbrev vecU8Heap_of_exact_alloc :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8Heap_of_exact_alloc
abbrev memRegion_1424_split_epilogue :=
  @CryptoVerification.SpqrV1.States.IntoPb.memRegion_1424_split_epilogue
abbrev unchunkedCt1SentEkReceived_expose_clone :=
  @CryptoVerification.SpqrV1.States.IntoPb.unchunkedCt1SentEkReceived_expose_clone
abbrev chunkedEkReceivedCt1Sampled_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.chunkedEkReceivedCt1Sampled_expose
abbrev stA_ekReceivedCt1Sampled_entails_928 :=
  @CryptoVerification.SpqrV1.States.IntoPb.stA_ekReceivedCt1Sampled_entails_928
abbrev ekReceivedScratchCells :=
  @CryptoVerification.SpqrV1.States.IntoPb.ekReceivedScratchCells
abbrev memRegion_ekReceived_scratch_split :=
  @CryptoVerification.SpqrV1.States.IntoPb.memRegion_ekReceived_scratch_split
abbrev ekReceivedScratchCells_entails_memRegions :=
  @CryptoVerification.SpqrV1.States.IntoPb.ekReceivedScratchCells_entails_memRegions
abbrev outWords28_entails_ekReceivedCt1Sampled :=
  @CryptoVerification.SpqrV1.States.IntoPb.outWords28_entails_ekReceivedCt1Sampled

/-! ## 2. Placed Block-`334` Budget Hook Projections & Non-Null Branch Elimination -/

theorem alloc_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false) :=
  hA.alloc_ok

theorem allocNoOom_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
  subroutine_ok_allocNoOom_of_budget hA.alloc_ok

theorem dealloc_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  hA.dealloc_ok

theorem shimVm_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec :=
  hA.shim_ok

theorem sessionShim_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimBudgetSpec :=
  subroutine_ok_sessionShimBudget_of_rustAllocShimVm hA.shim_ok

theorem noAllocShim_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) noAllocShimBudgetSpec :=
  subroutine_ok_noAllocShim_of_sessionShimBudget (sessionShim_ok_placed hA)

theorem memcpyVm_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec :=
  hA.memcpy_ok

theorem sessionMemcpyRegion_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec :=
  subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm hA.memcpy_ok

theorem framelessMemcpy_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec :=
  subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget (sessionMemcpyRegion_ok_placed hA)

/-- Under `FitsEvents`, `rustCliAllocNoOomSpec` guarantees `ptr ≠ 0#64`, ruling out the OOM
    panic branches at `+1700` and `+884` in Block `334`. -/
theorem states_into_pb_no_oom_placed {ptr : BitVec 64} (h : ptr ≠ 0#64) :
    (ptr == 0#64) = false ∧ (ptr != 0#64) = true :=
  ⟨beq_eq_false_iff_ne.mpr h, bne_iff_ne.mpr h⟩

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
