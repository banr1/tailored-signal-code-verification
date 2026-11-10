/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode
public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Nonempty
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.NonemptyBudget

/-!
# Budget-Threaded `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>` Proof

Proves `signedDecode_placed_ok_of_deps` (`signedDecodePlacedSpec`, Block `562`) over
`RustCliAllocBudget` from `SignedHooksPlaced` and `SignedPortDepsPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecodeBudget

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification
open CryptoVerification.RecordCodecs.Placed
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (SignedHooksPlaced SignedPortDepsPlaced signedDecodePlacedSpec signedDecodeRawSpec)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.NonemptyBudget (signedDecode_placed_outcome_of_nonempty)

/-- Relocatable `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>` (block `562`) meets
`signedDecodePlacedSpec`, given `SignedHooksPlaced` and `SignedPortDepsPlaced`. -/
theorem signedDecode_placed_ok_of_deps [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H) (d : SignedPortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_562 H) (blkPl_562).base (signedDecodePlacedSpec A lim) := by
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp _ => ?_
  have hne : x.bytes ≠ [] := by
    obtain ⟨_, hraw⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
    dsimp only [signedDecodeRawSpec] at hraw
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hraw
    rcases hraw with ⟨⟨_, _, _, hpos, _, _⟩, _⟩
    intro hnil
    simp [hnil] at hpos
  exact signedDecode_placed_outcome_of_nonempty hH d hne hpc hrun hpre hsp

end LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecodeBudget
