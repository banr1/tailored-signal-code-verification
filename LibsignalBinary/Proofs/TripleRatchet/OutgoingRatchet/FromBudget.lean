/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case1Budget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2Budget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case3Budget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case4Budget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget

/-!
# Budget-Threaded Relocatable `OutgoingTripleRatchet::from_session_state`

Combines `Case1Budget`–`Case4Budget` into `otrFrom_placed_ok_of_contracts` and
`otrFrom_placed_ok` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.FromBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalPlacement blkPC_19 blkPC_201 blkPC_29 blkPC_5
  blkPl_19 blkPl_201 blkPl_29 blkPl_5
  lsRustDeallocSym ls_hook_ok_of_mem lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet (withLsRoLoaded)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropSpeSpec remoteIdentityKeyPlacedSpec
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case1Budget (
  otrFrom_case1_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2Budget (
  deserializePlacedBudgetSpec deserialize_vm_placed_ok otrFrom_case2_placed_ok_of_contracts
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case3Budget (
  otrFrom_case3_placed_ok_of_contracts
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case4Budget (
  otrFrom_case4_placed_ok_of_contracts
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget (
  otrFromPlacedSpec subroutine_ok_of_cases4_placed
)

/-- Relocatable `[LibsignalPlacement]` `OTR::from_session_state` under `RustCliAllocBudget M`,
given subroutine contracts for `dealloc`, `PublicKey::deserialize`,
`SessionState::remote_identity_key`, and `drop_in_place<SignalProtocolError>`. -/
theorem otrFrom_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_19).rebase (blkPl_19).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdeser : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base deserializePlacedBudgetSpec)
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A.repAlloc)))
    (hdropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec M A lim))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromPlacedSpec M A lim) := by
  apply subroutine_ok_of_cases4_placed
    (P₁ := fun x => x.st.senderChain = none)
    (P₂ := fun x => ∃ sc, x.st.senderChain = some sc ∧ 256 ≤ x.st.version.toNat)
    (P₃ := fun x => ∃ sc, x.st.senderChain = some sc ∧
      ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = none)
    (P₄ := fun x => ∃ sc rem, x.st.senderChain = some sc ∧
      ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = some rem)
  · intro x
    cases hsc : x.st.senderChain with
    | none => exact Or.inl rfl
    | some sc =>
      by_cases hver : 256 ≤ x.st.version.toNat
      · exact Or.inr (Or.inl ⟨sc, rfl, hver⟩)
      · cases hrem : x.st.remoteIdentity with
        | none => exact Or.inr (Or.inr (Or.inl ⟨sc, rfl, hver, rfl⟩))
        | some rem => exact Or.inr (Or.inr (Or.inr ⟨sc, rem, rfl, hver, rfl⟩))
  · exact otrFrom_case1_placed_ok
  · exact otrFrom_case2_placed_ok_of_contracts hdealloc hdeser
  · exact otrFrom_case3_placed_ok_of_contracts hdealloc hdeser hremIk
  · exact otrFrom_case4_placed_ok_of_contracts hdeser hremIk hdropSpe

/-- Relocatable `[LibsignalPlacement]` `OTR::from_session_state` under `RustCliAllocBudget M`,
discharging `dealloc` from `HookSat` and `PublicKey::deserialize` from
`deserialize_vm_placed_ok`. -/
theorem otrFrom_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A.repAlloc)))
    (hdropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec M A lim))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromPlacedSpec M A lim) :=
  otrFrom_placed_ok_of_contracts
    (ls_hook_ok_of_mem h_dealloc)
    (deserialize_vm_placed_ok H)
    hremIk hdropSpe

end LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.FromBudget
