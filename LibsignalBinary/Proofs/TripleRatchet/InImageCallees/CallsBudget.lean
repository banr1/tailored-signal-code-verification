/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PrivateKeySerializeBudget
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplayBudget

/-!
# Budget-Threaded Cross-Block Call-Site Lemmas for In-Image Callees

Relocatable `[LibsignalPlacement]` call-site lemmas for `PublicKey::try_from`,
`ServiceId::parse_from_service_id_string`, `PrivateKey::serialize`, and
`<ProtocolAddress as Display>::fmt` under `RustCliAllocBudget` and `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget

open Arm64 ProofLib
open CryptoVerification (
  IsLsBlockProg LibsignalPlacement blkPC_252 blkPl_252 libsignalMutatedBlocks
  lsFmtWriteSym lsRustAllocSym lsRustNoAllocShimSym ls_subroutine_ok_of_block lsmpl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget rustCliAllocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv fmtWriteBudgetEnvSpec)
open LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget (
  pkTryFromPlacedBudgetSpec pkTryFrom_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget (
  addrDisplayEnvSpec parseSidCodeBudgetSpec parseSidCodeStackBudgetSpec
  privSerializeSpec privSerializeSpecX
  uuidTryParseBudgetSpec uuidTryParseCodeBudgetSpec uuidTryParseStackBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget (
  parseSid_placed_ok_of_code parseSid_placed_ok_of_contract
  parseSid_placed_ok_of_contract_stack parseSid_placed_ok_of_plain_contract_stack
)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PrivateKeySerializeBudget (
  privSerialize_placed_ok privSerialize_placed_ok_of_vm
  privSerialize_placed_ok_x privSerialize_placed_ok_x_of_vm
)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplayBudget (
  addrDisplay_placed_ok
)

/-- Relocatable `PublicKey::try_from` (Block `211`, `VmPreserved`-strengthened) lifted to any
caller block `prog`. -/
theorem pk_try_from_placed_ok_at [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 211) (withLsCodeLoaded lsmpl pkTryFromPlacedBudgetSpec) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (pkTryFrom_placed_ok H)) (_hi := hi)

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) lifted to any caller block
`prog` from `huuid` on Block `252`. -/
theorem parse_sid_placed_ok_at_of_contract [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base (uuidTryParseBudgetSpec uuidTryParse))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec uuidTryParse)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (parseSid_placed_ok_of_contract H huuid) (_hi := hi)

/-- Relocatable stack-framed `ServiceId::parse_from_service_id_string` (Block `206`) lifted to any
caller block `prog` from `huuid` on Block `252`. -/
theorem parse_sid_placed_ok_at_of_contract_stack [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H] (hookStack : Nat := 0)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base (withLsCodeLoaded lsmpl (uuidTryParseStackBudgetSpec hookStack)))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackBudgetSpec hookStack)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (parseSid_placed_ok_of_contract_stack H hookStack huuid) (_hi := hi)

/-- Relocatable stack-framed `ServiceId::parse_from_service_id_string` (Block `206`) lifted to any
caller block `prog` from plain `uuidTryParseStackBudgetSpec hookStack` on Block `252`. -/
theorem parse_sid_placed_ok_at_of_plain_contract_stack [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H] (hookStack : Nat := 0)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base (uuidTryParseStackBudgetSpec hookStack))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackBudgetSpec hookStack)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (parseSid_placed_ok_of_plain_contract_stack H hookStack huuid) (_hi := hi)

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) lifted to any caller block
`prog` from `withLsCodeLoaded lsmpl (uuidTryParseCodeBudgetSpec uuidTryParse)` on Block `252`. -/
theorem parse_sid_placed_ok_at_of_code [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base (withLsCodeLoaded lsmpl (uuidTryParseCodeBudgetSpec uuidTryParse)))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec uuidTryParse)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (parseSid_placed_ok_of_code H huuid) (_hi := hi)

/-- Relocatable `PrivateKey::serialize` (Block `208`) lifted to any caller block `prog`. -/
theorem priv_serialize_placed_ok_at [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 208)
      (withLsCodeLoaded lsmpl (privSerializeSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (privSerialize_placed_ok hshim halloc))
    (_hi := hi)

/-- Relocatable `PrivateKey::serialize` (`privSerializeSpecX M A lim`, Block `208`) lifted to any
caller block `prog`. -/
theorem priv_serialize_placed_ok_at_x [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 208)
      (withLsCodeLoaded lsmpl (privSerializeSpecX M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (privSerialize_placed_ok_x hshim halloc))
    (_hi := hi)

theorem priv_serialize_placed_ok_at_of_vm [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 208)
      (withLsCodeLoaded lsmpl (privSerializeSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (privSerialize_placed_ok_of_vm hshim halloc))
    (_hi := hi)

theorem priv_serialize_placed_ok_at_x_of_vm [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 208)
      (withLsCodeLoaded lsmpl (privSerializeSpecX M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (privSerialize_placed_ok_x_of_vm hshim halloc))
    (_hi := hi)

/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`) lifted to any caller block
`prog` (unifies with `addrDisplaySpec M A lim` when `Env = FmtWriteEnv`). -/
theorem addr_display_placed_ok_at [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : List AllocEvent → Prop} {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hW : HookSat H lsFmtWriteSym (fmtWriteBudgetEnvSpec M A lim Env))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 215)
      (withLsCodeLoaded lsmpl (addrDisplayEnvSpec M A lim Env)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (addrDisplay_placed_ok hW))
    (_hi := hi)

end LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget
