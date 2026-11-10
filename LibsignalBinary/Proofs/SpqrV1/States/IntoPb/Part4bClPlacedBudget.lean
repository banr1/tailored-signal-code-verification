/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bPlacedBudget
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersX
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Arm 6 (`States.headerReceived`) with `withLsCodeLoaded`

Re-exports `HeaderReceivedEnv` and the `withLsCodeLoaded` Block `334` contracts for Arm 6
(`States.headerReceived`, tag `8`) from `Part4bPlacedBudget`, and lifts them to `withLsCl`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bClPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalPlacement lsmpl lsρ withLsCl withLsCodeLoaded
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  subroutine_ok_withLsCl_of_withLsCodeLoaded
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  subroutine_ok_withLsCodeLoaded_of_withLsCl
)
open CryptoVerification.LibsignalSpqrV1 (spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (HeaderReceived)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget (
  statesIntoPbVariantPlacedSpecOfEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bPlacedBudget (
  HeaderReceivedEnv statesIntoPbHeaderReceivedPlacedSpec
  states_into_pb_headerReceived_of_env_cl_placed
  states_into_pb_headerReceived_env_cl_placed
  states_into_pb_headerReceived_cl_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

/-! ## 1. Re-Exports from `Part4bPlacedBudget` -/

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bPlacedBudget (
  HeaderReceivedEnv statesIntoPbHeaderReceivedPlacedSpec
)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bPlacedBudget (
  states_into_pb_headerReceived_of_env_cl_placed
  states_into_pb_headerReceived_env_cl_placed
  states_into_pb_headerReceived_cl_placed
)

/-! ## 2. `withLsCl` Relocatable Arm 6 Wrappers -/

/-- Envelope-parametric `withLsCl` relocatable `subroutine_ok` for `<States>::into_pb`
    (Block `334`) on `.headerReceived s` (Arm 6, tag `8`). -/
theorem states_into_pb_headerReceived_of_env_withLsCl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCl lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : HeaderReceived spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, HeaderReceivedEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCl lsmpl (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.headerReceived s) Env)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded
    (states_into_pb_headerReceived_of_env_cl_placed
      (subroutine_ok_withLsCodeLoaded_of_withLsCl hdec_cl) hmemcpy_raw s hEnv)

/-- Tight `HeaderReceivedEnv` `withLsCl` relocatable `subroutine_ok` for `<States>::into_pb`
    (Block `334`) on `.headerReceived s` (Arm 6, tag `8`). -/
theorem states_into_pb_headerReceived_env_withLsCl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCl lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCl lsmpl (statesIntoPbHeaderReceivedPlacedSpec M A lim F s)) :=
  states_into_pb_headerReceived_of_env_withLsCl_placed hdec_cl hmemcpy_raw s (fun _ h => h)

/-- Verifies `<States>::into_pb`
    (Block `334`) on `.headerReceived s` (Arm 6, tag `8`). -/
theorem states_into_pb_headerReceived_withLsCl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCl lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCl lsmpl (statesIntoPbHeaderReceivedPlacedSpec M A lim F s)) :=
  states_into_pb_headerReceived_env_withLsCl_placed hdec_cl hmemcpy_raw s

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bClPlacedBudget
