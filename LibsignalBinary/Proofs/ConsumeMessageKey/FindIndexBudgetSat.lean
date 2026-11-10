/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudgetSat -- proof-setup: allow-public-import

/-!
# `HookSat`-backed `black_box` Sibling of `ConsumeMessageKey/FindIndexBudget`

Weakens `h_bb : H lsBlackBoxU8Sym = some blackBoxHook` to
`h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat` for budget-threaded Block `26`
(`find_receiver_chain_index_placed_ok_sat`) and Block `24`
(`find_receiver_chain_index_placed_ok_at_cmk_sat`), keeping token-identical conclusions.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexBudgetSat

open Arm64 ProofLib
open CryptoVerification
  (LibsignalPlacement blkPC_24 blkPC_26 blkPl_24 blkPl_26 extract_withLsCodeLoaded lsBlackBoxU8Sym
   ls_subroutine_ok_of_block lsmpl withLsCodeLoaded)
open LibsignalBinary.Heap (AllocCostModel RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
  (FindIndexPlacedOk findIndexPlacedSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (blackBoxSpecSat)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget
  (findPlacedAllocSpec findPlacedSpec)

/-- `HookSat` `black_box` sibling of `FindIndexBudget.find_receiver_chain_index_placed_ok`
(`FindIndexBudget.lean:44`), with a token-identical conclusion. -/
theorem find_receiver_chain_index_placed_ok_sat [LibsignalPlacement] {M : AllocCostModel}
    {H : String → Option (State → State)} (A : RustCliAllocBudget M)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_26).rebase (blkPl_26).base H) (blkPl_26).base
      (withLsCodeLoaded lsmpl (findPlacedSpec A)) :=
  LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudgetSat.find_receiver_chain_index_placed_ok_sat
    A h_bb

/-- `HookSat` `black_box` sibling of `FindIndexBudget.find_receiver_chain_index_placed_ok_at_cmk`
(`FindIndexBudget.lean:53`), with a token-identical conclusion (`FindIndexPlacedOk H A`). -/
theorem find_receiver_chain_index_placed_ok_at_cmk_sat [LibsignalPlacement] {M : AllocCostModel}
    {H : String → Option (State → State)} (A : RustCliAllocBudget M)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    FindIndexPlacedOk H A := by
  refine subroutine_ok_outcome_intro fun ⟨p, cs, theirA, their⟩ R s0 hpc hrun hpre hsp => ?_
  have h1 : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 26)
      (withLsCodeLoaded lsmpl (findPlacedSpec A)) :=
    ls_subroutine_ok_of_block (i := 24) (j := 26) (find_receiver_chain_index_placed_ok_sat A h_bb)
  refine h1.mono_outcome (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun _ hout => hout
  have ⟨hcl, hp⟩ := extract_withLsCodeLoaded hpre
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcl, ?_⟩
  dsimp only [findPlacedSpec, findPlacedAllocSpec, findIndexPlacedSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.findPlacedSpec,
    CryptoVerification.LibsignalSession.findIndexPlacedSpec] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2, hsp⟩, hp.2⟩

end LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexBudgetSat
