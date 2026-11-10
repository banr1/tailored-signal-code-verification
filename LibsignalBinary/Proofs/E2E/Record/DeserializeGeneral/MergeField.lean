/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.MergeFieldLeaves

/-!
# General `SessionStructure::merge_field` Dispatcher

Combines the per-tag leaves from `MergeFieldLeaves.lean` (`1`, `2`–`4`, `5`, `6`, `7`, `9`) with
`chainMergeGen_ok` (`ChainMerge.lean`) to prove `mergeFieldGen_ok` across all in-scope fields.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed

theorem mergeFieldGenSpec_pre_iff {P : GenField → Prop} {x : MergeFieldGenGhost} {s : State}
    {R : SepProp} :
    (s.mem ⊨ (mergeFieldGenSpec P).pre x s ∗ R) ↔
      P x.fld ∧ (s.mem ⊨ (mergeFieldGenSpec (fun _ => True)).pre x s ∗ R) := by
  simp only [mergeFieldGenSpec, sepConj_assoc, satisfies_pure_sepConj]
  constructor
  · rintro ⟨⟨h0, h1, h2, h3, h4, hp, hr⟩, hm⟩
    exact ⟨hp, ⟨h0, h1, h2, h3, h4, trivial, hr⟩, hm⟩
  · rintro ⟨hp, ⟨h0, h1, h2, h3, h4, -, hr⟩, hm⟩
    exact ⟨⟨h0, h1, h2, h3, h4, hp, hr⟩, hm⟩

theorem mergeFieldGenOk_of_imp {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {P Q : GenField → Prop} (hP : MergeFieldGenOk C ctl P abs)
    (hQP : ∀ fl, Q fl → P fl) : MergeFieldGenOk C ctl Q abs := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hq, hpre⟩ := mergeFieldGenSpec_pre_iff.mp hpre
  exact hP.mono_outcome x R s0 hpc hrun (mergeFieldGenSpec_pre_iff.mpr ⟨hQP _ hq, hpre⟩) hal
    fun _ hout => hout

theorem mergeFieldGenOk_or {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {P Q : GenField → Prop} (hP : MergeFieldGenOk C ctl P abs)
    (hQ : MergeFieldGenOk C ctl Q abs) :
    MergeFieldGenOk C ctl (fun fl => P fl ∨ Q fl) abs := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hpq, hpre⟩ := mergeFieldGenSpec_pre_iff.mp hpre
  rcases hpq with hp | hq
  · exact hP.mono_outcome x R s0 hpc hrun (mergeFieldGenSpec_pre_iff.mpr ⟨hp, hpre⟩) hal
      fun _ hout => hout
  · exact hQ.mono_outcome x R s0 hpc hrun (mergeFieldGenSpec_pre_iff.mpr ⟨hq, hpre⟩) hal
      fun _ hout => hout

/-- `SessionStructure::merge_field` (`0x581c`) satisfies `mergeFieldGenSpec (fun _ => True)` on
`tripleRatchetProgAt`. -/
theorem mergeFieldGen_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (hCh : ChainMergeGenOk C ctl abs) :
    MergeFieldGenOk C ctl (fun _ => True) abs := by
  refine mergeFieldGenOk_of_imp
    (mergeFieldGenOk_or (mergeFieldGenSessionVersion_ok C ctl hC)
      (mergeFieldGenOk_or (mergeFieldGenIdentityRootKeys_ok C ctl hC)
        (mergeFieldGenOk_or (mergeFieldGenPreviousCounter_ok C ctl hC)
          (mergeFieldGenOk_or (mergeFieldGenSenderChain_ok C ctl hC hCh)
            (mergeFieldGenOk_or (mergeFieldGenReceiverChains_ok C ctl hC hCh)
              (mergeFieldGenPendingPreKey_ok C ctl hC)))))) ?_
  intro fl _
  cases fl <;> simp [GenField.tag]

end CryptoVerification.E2E.Record.DeserializeGeneral
