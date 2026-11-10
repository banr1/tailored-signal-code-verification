/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case1BudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2BudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case3BudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case4BudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudgetFd

/-!
# `FdsGe3Closed`-Threaded Relocatable `OutgoingTripleRatchet::from_session_state`

Combines `Case1BudgetFd`–`Case4BudgetFd` into `otrFrom_placed_ok_fd`, preserving `FdsGe3Closed`
under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.FromBudgetFd

open Arm64 ProofLib
open CryptoVerification (
  LibsignalPlacement blkPC_19 blkPC_201 blkPC_211 blkPC_29 blkPC_5
  blkPl_19 blkPl_201 blkPl_211 blkPl_29 blkPl_5
  lsRustDeallocSym ls_hook_ok_of_mem lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet (withLsRoLoaded)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropSpeSpec remoteIdentityKeyPlacedSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudgetFd (
  drop_spe_placed_ok_fd
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case1BudgetFd (
  otrFrom_case1_placed_ok_fd
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2Budget (
  deserializePlacedBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2BudgetFd (
  otrFrom_case2_placed_ok_of_contracts_fd
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case3Budget (
  pkTryFromOkPlacedBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case3BudgetFd (
  otrFrom_case3_placed_ok_of_contracts_fd
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case4BudgetFd (
  otrFrom_case4_placed_ok_of_contracts_fd
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudgetFd (
  otrFromPlacedSpecFd subroutine_ok_of_cases4_placed_fd
)

theorem otrFrom_placed_ok_of_contracts_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_19).rebase (blkPl_19).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdeser : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base (withFdsGe3Closed deserializePlacedBudgetSpec))
    (hpkTryFrom : subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base (withLsCodeLoaded lsmpl (withFdsGe3Closed pkTryFromOkPlacedBudgetSpec)))
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (withFdsGe3Closed (remoteIdentityKeyPlacedSpec A.repAlloc))))
    (hdropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (withFdsGe3Closed (dropSpeSpec M A lim)))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromPlacedSpecFd M A lim) := by
  apply subroutine_ok_of_cases4_placed_fd
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
  · exact otrFrom_case1_placed_ok_fd
  · exact otrFrom_case2_placed_ok_of_contracts_fd hdealloc hdeser
  · exact otrFrom_case3_placed_ok_of_contracts_fd hdealloc hdeser hpkTryFrom hremIk
  · exact otrFrom_case4_placed_ok_of_contracts_fd hdeser hpkTryFrom hremIk hdropSpe

/-- Relocatable `[LibsignalPlacement]` `OTR::from_session_state` under `RustCliAllocBudget M`
preserving `FdsGe3Closed`, discharging `dealloc` and `dropSpe` from
`HookSat H lsRustDeallocSym`. -/
theorem otrFrom_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hdeser : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base (withFdsGe3Closed deserializePlacedBudgetSpec))
    (hpkTryFrom : subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base (withLsCodeLoaded lsmpl (withFdsGe3Closed pkTryFromOkPlacedBudgetSpec)))
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (withFdsGe3Closed (remoteIdentityKeyPlacedSpec A.repAlloc)))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromPlacedSpecFd M A lim) :=
  otrFrom_placed_ok_of_contracts_fd
    (ls_hook_ok_of_mem h_dealloc)
    hdeser hpkTryFrom hremIk
    (((CryptoVerification.LibsignalTripleRatchet.Getters.instIsLsBlockProg_5 H).eq_blockProgram.trans
        (CryptoVerification.instIsLsBlockProg_5 H).eq_blockProgram.symm) ▸
      drop_spe_placed_ok_fd h_dealloc)

end LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.FromBudgetFd
