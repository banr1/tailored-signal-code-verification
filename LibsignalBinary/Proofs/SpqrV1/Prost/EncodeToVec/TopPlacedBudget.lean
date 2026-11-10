/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1SentPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBudget
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Unconditional `[LibsignalPlacement]` Closure for `PqRatchetState::encode_to_vec` (`Block 426`)

Discharges all 7 sub-message encoder callee contracts (`ChainParams`, `EpochDirection`,
`Authenticator`, `PolynomialEncoder`, `PolynomialDecoder`, `EkSentCt1Received`, `Ct1Sent`) on
`FinalPlacedBudget` to establish unconditional `[LibsignalPlacement]` contracts for `Block 426`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.TopPlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open CryptoVerification
  (LibsignalPlacement extract_withLsCodeLoaded lsMemcpySym
   ls_subroutine_ok_of_block lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (StepInv blkPC_426 blkPl_426 withStepInv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withLsRoLoaded)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget (authEncodePinnedSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeChainParamsExactSpecOf encodeEpochDirectionExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
  (etv_polyDecoderEncode_budget_exact_of_spec etv_polyEncoderEncode_budget_exact_of_spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
  (pqRatchetStateEncodeToVecNoOomSpecOf pqRatchetStateEncodeToVecPinnedNoOomSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (subroutine_ok_withStepInv_lscl)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalPlacedBudget
  (PqRatchetStateEncodeToVecPinnedPlacedOkExt PqRatchetStateEncodeToVecPlacedOkExt
   pqRatchetStateEncodeToVec_noOom_placed_ok_of_contracts
   pqRatchetStateEncodeToVec_pinned_noOom_placed_ok_of_contracts
   pqRatchetStateEncodeToVec_pinned_placed_ok_of_contracts
   pqRatchetStateEncodeToVec_placed_ok_of_contracts
   pqRatchetStateEncodeToVec_ro_noOom_placed_ok_of_contracts
   pqRatchetStateEncodeToVec_ro_pinned_noOom_placed_ok_of_contracts
   pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_contracts
   pqRatchetStateEncodeToVec_ro_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget
  (encodePolyDecoderExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactPlacedBudget
  (encode_polyDecoder_2_exact_pinned_placed_ok_of_memcpy
   encode_polyDecoder_2_exact_pinned_placed_ok_of_memcpy_x)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
  (encodePolyEncoderExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedBudget
  (encode_polyEncoder_2_exact_pinned_placed_ok_of_memcpy
   encode_polyEncoder_2_exact_pinned_placed_ok_of_memcpy_x)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.ProofPlacedBudget
  (pqRatchetStateEncodeToVecRoNoOomPlacedSpecOf
   pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf
   pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf
   pqRatchetStateEncodeToVecRoPlacedSpecOf
   pqRatchetStateEncodeToVec_noOom_placed_ok_of_pinned
   pqRatchetStateEncodeToVec_placed_ok_of_pinned
   pqRatchetStateEncodeToVec_ro_noOom_placed_ok_of_pinned
   pqRatchetStateEncodeToVec_ro_placed_ok_of_pinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvCt1SentBudgetExactSpecOf etvEkSentCt1ReceivedBudgetExactSpecOf
   etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (encodeChainParamsSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBudget
  (encode_chainParams_2_placed_ok encode_chainParams_2_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
  (encodeEpochDirectionPinnedSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBudget
  (encode_epochDirection_2_pinned_placed_ok encode_epochDirection_2_pinned_placed_ok_x)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

/-! ## 1. Exact-Capacity Sub-Message Callee Discharges (`Block 426` → Blocks `313`–`319`) -/

private theorem lift_withLsCodeLoaded_bridge [LibsignalPlacement] {α β : Type}
    {prog : Program} {entry : BitVec 64} {spec1 : Spec α} {spec2 : Spec β}
    (hbr : ∀ s0 : State, subroutine_ok prog entry (withStepInv s0 spec1) →
      subroutine_ok prog entry (withStepInv s0 spec2))
    (hok : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec1)) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec2) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have h1 : subroutine_ok prog entry (withStepInv s0 spec1) :=
    subroutine_ok_withStepInv_lscl hcl0 hok
  have h2 := hbr s0 h1
  have hpre2 : s0.mem ⊨ (withStepInv s0 spec2).pre x s0 ∗ R := by
    dsimp only [withStepInv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨StepInv.refl s0, hpre⟩
  exact h2.mono_outcome x R s0 hpc hrun hpre2 hsp fun _ hout => hout

theorem etv_encodeChainParams_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hcp_ok : subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (encodeChainParamsSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf resStack A lim)) :=
  FinalPlacedBudget.etv_encodeChainParams_exact_of_lscl hres hcp_ok

theorem etv_encodeChainParams_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A lim)) :=
  etv_encodeChainParams_exact_of_lscl (by decide)
    (ls_subroutine_ok_of_block (encode_chainParams_2_placed_ok h_panic hshim halloc hrealloc))

theorem etv_encodeChainParams_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A lim)) :=
  etv_encodeChainParams_exact_of_lscl (by decide)
    (ls_subroutine_ok_of_block (encode_chainParams_2_placed_ok_x h_panic hshim halloc hrealloc))

theorem etv_encodeEpochDirection_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hed_ok : subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf resStack A lim)) :=
  FinalPlacedBudget.etv_encodeEpochDirection_exact_of_lscl hres hed_ok

theorem etv_encodeEpochDirection_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A lim)) :=
  etv_encodeEpochDirection_exact_of_lscl (by decide)
    (ls_subroutine_ok_of_block
      (encode_epochDirection_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc))

theorem etv_encodeEpochDirection_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A lim)) :=
  etv_encodeEpochDirection_exact_of_lscl (by decide)
    (ls_subroutine_ok_of_block
      (encode_epochDirection_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc))

theorem etv_authEncode_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hauth_ok : subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf resStack A lim)) :=
  FinalPlacedBudget.etv_authEncode_exact_of_lscl hres hauth_ok

theorem etv_authEncode_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStack A lim)) :=
  LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlacedBudget.etv_authEncode_exact_placed_ok
    h_panic hshim halloc hrealloc hmc

theorem etv_authEncode_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStackX A lim)) :=
  LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlacedBudget.etv_authEncode_exact_placed_ok_x
    h_panic hshim halloc hrealloc hmc

theorem etv_polyEncoderEncode_budget_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpe_ok : subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf resStack A lim)) :=
  lift_withLsCodeLoaded_bridge
    (fun _ => etv_polyEncoderEncode_budget_exact_of_spec (resStack := resStack)) hpe_ok

theorem etv_polyEncoderEncode_budget_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStack A lim)) :=
  etv_polyEncoderEncode_budget_exact_of_lscl
    (ls_subroutine_ok_of_block (encode_polyEncoder_2_exact_pinned_placed_ok_of_memcpy hmc))

theorem etv_polyEncoderEncode_budget_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStackX A lim)) :=
  etv_polyEncoderEncode_budget_exact_of_lscl
    (ls_subroutine_ok_of_block (encode_polyEncoder_2_exact_pinned_placed_ok_of_memcpy_x hmc))

theorem etv_polyEncoderEncode_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (_h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStack A lim)) :=
  etv_polyEncoderEncode_budget_exact_placed_ok hmc

theorem etv_polyEncoderEncode_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (_h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStackX A lim)) :=
  etv_polyEncoderEncode_budget_exact_placed_ok_x hmc

theorem etv_polyDecoderEncode_budget_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpd_ok : subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf resStack A lim)) :=
  lift_withLsCodeLoaded_bridge
    (fun _ => etv_polyDecoderEncode_budget_exact_of_spec (resStack := resStack)) hpd_ok

theorem etv_polyDecoderEncode_budget_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStack A lim)) :=
  etv_polyDecoderEncode_budget_exact_of_lscl
    (ls_subroutine_ok_of_block (encode_polyDecoder_2_exact_pinned_placed_ok_of_memcpy hmc))

theorem etv_polyDecoderEncode_budget_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStackX A lim)) :=
  etv_polyDecoderEncode_budget_exact_of_lscl
    (ls_subroutine_ok_of_block (encode_polyDecoder_2_exact_pinned_placed_ok_of_memcpy_x hmc))

theorem etv_polyDecoderEncode_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (_h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStack A lim)) :=
  etv_polyDecoderEncode_budget_exact_placed_ok hmc

theorem etv_polyDecoderEncode_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (_h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStackX A lim)) :=
  etv_polyDecoderEncode_budget_exact_placed_ok_x hmc

theorem etv_ekSentCt1ReceivedEncode_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStack A lim)) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedBudget.etv_ekSentCt1ReceivedEncode_exact_placed_ok
    h_panic hshim halloc hrealloc hmc

theorem etv_ekSentCt1ReceivedEncode_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStackX A lim)) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedBudget.etv_ekSentCt1ReceivedEncode_exact_placed_ok_x
    h_panic hshim halloc hrealloc hmc

theorem etv_ct1SentEncode_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStack A lim)) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1SentPlacedBudget.etv_ct1SentEncode_exact_placed_ok
    h_panic hshim halloc hrealloc hmc

theorem etv_ct1SentEncode_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStackX A lim)) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1SentPlacedBudget.etv_ct1SentEncode_exact_placed_ok_x
    h_panic hshim halloc hrealloc hmc

/-! ## 2. Unconditional Top-Level `[LibsignalPlacement]` Closure (`Block 426`) -/

theorem pqRatchetStateEncodeToVec_ro_pinned_noOom_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf doReserveStack A lim)) :=
  pqRatchetStateEncodeToVec_ro_pinned_noOom_placed_ok_of_contracts
    h_panic hshim halloc hrealloc hmc
    (etv_encodeChainParams_exact_placed_ok h_panic hshim halloc hrealloc)
    (etv_encodeEpochDirection_exact_placed_ok h_panic hshim halloc hrealloc hmc)
    (etv_authEncode_exact_placed_ok h_panic hshim halloc hrealloc hmc)
    (etv_polyEncoderEncode_budget_exact_placed_ok hmc)
    (etv_polyDecoderEncode_budget_exact_placed_ok hmc)
    (etv_ekSentCt1ReceivedEncode_placed_ok h_panic hshim halloc hrealloc hmc)
    (etv_ct1SentEncode_placed_ok h_panic hshim halloc hrealloc hmc)

theorem pqRatchetStateEncodeToVec_ro_noOom_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoNoOomPlacedSpecOf doReserveStack A lim)) :=
  pqRatchetStateEncodeToVec_ro_noOom_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_ro_pinned_noOom_placed_ok_ext h_panic hshim halloc hrealloc hmc)

theorem pqRatchetStateEncodeToVec_ro_pinned_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf doReserveStack A lim)) :=
  pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_contracts
    h_panic hshim halloc hrealloc hmc
    (etv_encodeChainParams_exact_placed_ok h_panic hshim halloc hrealloc)
    (etv_encodeEpochDirection_exact_placed_ok h_panic hshim halloc hrealloc hmc)
    (etv_authEncode_exact_placed_ok h_panic hshim halloc hrealloc hmc)
    (etv_polyEncoderEncode_budget_exact_placed_ok hmc)
    (etv_polyDecoderEncode_budget_exact_placed_ok hmc)
    (etv_ekSentCt1ReceivedEncode_placed_ok h_panic hshim halloc hrealloc hmc)
    (etv_ct1SentEncode_placed_ok h_panic hshim halloc hrealloc hmc)

theorem pqRatchetStateEncodeToVec_ro_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPlacedSpecOf doReserveStack A lim)) :=
  pqRatchetStateEncodeToVec_ro_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_ro_pinned_placed_ok_ext h_panic hshim halloc hrealloc hmc)

theorem pqRatchetStateEncodeToVec_pinned_noOom_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl
        (pqRatchetStateEncodeToVecPinnedNoOomSpecOf doReserveStackX A lim))) :=
  pqRatchetStateEncodeToVec_pinned_noOom_placed_ok_of_contracts
    h_panic hshim halloc hrealloc hmc
    (etv_encodeChainParams_exact_placed_ok_x h_panic hshim halloc hrealloc)
    (etv_encodeEpochDirection_exact_placed_ok_x h_panic hshim halloc hrealloc hmc)
    (etv_authEncode_exact_placed_ok_x h_panic hshim halloc hrealloc hmc)
    (etv_polyEncoderEncode_budget_exact_placed_ok_x hmc)
    (etv_polyDecoderEncode_budget_exact_placed_ok_x hmc)
    (etv_ekSentCt1ReceivedEncode_placed_ok_x h_panic hshim halloc hrealloc hmc)
    (etv_ct1SentEncode_placed_ok_x h_panic hshim halloc hrealloc hmc)

theorem pqRatchetStateEncodeToVec_noOom_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl
        (pqRatchetStateEncodeToVecNoOomSpecOf doReserveStackX A lim))) :=
  pqRatchetStateEncodeToVec_noOom_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_pinned_noOom_placed_ok_ext h_panic hshim halloc hrealloc hmc)

theorem pqRatchetStateEncodeToVec_pinned_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    PqRatchetStateEncodeToVecPinnedPlacedOkExt A lim ext :=
  pqRatchetStateEncodeToVec_pinned_placed_ok_of_contracts
    h_panic hshim halloc hrealloc hmc
    (etv_encodeChainParams_exact_placed_ok_x h_panic hshim halloc hrealloc)
    (etv_encodeEpochDirection_exact_placed_ok_x h_panic hshim halloc hrealloc hmc)
    (etv_authEncode_exact_placed_ok_x h_panic hshim halloc hrealloc hmc)
    (etv_polyEncoderEncode_budget_exact_placed_ok_x hmc)
    (etv_polyDecoderEncode_budget_exact_placed_ok_x hmc)
    (etv_ekSentCt1ReceivedEncode_placed_ok_x h_panic hshim halloc hrealloc hmc)
    (etv_ct1SentEncode_placed_ok_x h_panic hshim halloc hrealloc hmc)

theorem pqRatchetStateEncodeToVec_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    PqRatchetStateEncodeToVecPlacedOkExt A lim ext :=
  pqRatchetStateEncodeToVec_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_pinned_placed_ok_ext h_panic hshim halloc hrealloc hmc)

theorem pqRatchetStateEncodeToVec_pinned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    PqRatchetStateEncodeToVecPinnedPlacedOkExt A lim ext :=
  pqRatchetStateEncodeToVec_pinned_placed_ok_ext h_panic hshim halloc hrealloc hmc

theorem pqRatchetStateEncodeToVec_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    PqRatchetStateEncodeToVecPlacedOkExt A lim ext :=
  pqRatchetStateEncodeToVec_placed_ok_ext h_panic hshim halloc hrealloc hmc

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.TopPlacedBudget
