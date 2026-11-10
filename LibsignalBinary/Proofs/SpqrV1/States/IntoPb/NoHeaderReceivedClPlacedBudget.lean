/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersX
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<States>::into_pb` (Block `334`) — Arm 5 (`States.noHeaderReceived`) with `withLsCodeLoaded`

Re-exports `NoHeaderReceivedEnv` and `withLsCodeLoaded` relocatable contracts for Arm 5
(`States.noHeaderReceived`, tag `7`) from `Part4aPlacedBudget`, and lifts them to `withLsCl`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlacedBudget

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
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (NoHeaderReceived)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget (
  statesIntoPbVariantPlacedSpecOfEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget (
  NoHeaderReceivedEnv statesIntoPbNoHeaderReceivedPlacedSpec
  statesIntoPb_seq_sepWP_cl_vm call_memcpy_keep_relocate_cl_placed
  states_into_pb_noHeaderReceived_of_env_cl_placed
  states_into_pb_noHeaderReceived_env_cl_placed
  states_into_pb_noHeaderReceived_cl_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

/-! ## 1. Re-Exports from `Part4aPlacedBudget` -/

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget (
  NoHeaderReceivedEnv statesIntoPbNoHeaderReceivedPlacedSpec
  statesIntoPb_seq_sepWP_cl_vm call_memcpy_keep_relocate_cl_placed
)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget (
  states_into_pb_noHeaderReceived_of_env_cl_placed
  states_into_pb_noHeaderReceived_env_cl_placed
  states_into_pb_noHeaderReceived_cl_placed
)

/-! ## 2. `withLsCl` Relocatable Arm 5 Contracts -/

/-- Envelope-parametric `withLsCl` relocatable `subroutine_ok` for `<States>::into_pb`
    (Block `334`) on `.noHeaderReceived s` (Arm 5, tag `7`). -/
theorem states_into_pb_noHeaderReceived_of_env_withLsCl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCl lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, NoHeaderReceivedEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCl lsmpl (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.noHeaderReceived s) Env)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded
    (states_into_pb_noHeaderReceived_of_env_cl_placed
      (subroutine_ok_withLsCodeLoaded_of_withLsCl hdec_cl) hmemcpy_raw s hEnv)

/-- Tight `NoHeaderReceivedEnv` `withLsCl` relocatable `subroutine_ok` for `<States>::into_pb`
    (Block `334`) on `.noHeaderReceived s` (Arm 5, tag `7`). -/
theorem states_into_pb_noHeaderReceived_env_withLsCl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCl lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCl lsmpl (statesIntoPbNoHeaderReceivedPlacedSpec M A lim F s)) :=
  states_into_pb_noHeaderReceived_of_env_withLsCl_placed hdec_cl hmemcpy_raw s (fun _ h => h)

/-- Complete `withLsCl` budget-threaded relocatable proof of `<States>::into_pb`
    (Block `334`) on `.noHeaderReceived s` (Arm 5, tag `7`). -/
theorem states_into_pb_noHeaderReceived_withLsCl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCl lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCl lsmpl (statesIntoPbNoHeaderReceivedPlacedSpec M A lim F s)) :=
  states_into_pb_noHeaderReceived_env_withLsCl_placed hdec_cl hmemcpy_raw s

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlacedBudget
