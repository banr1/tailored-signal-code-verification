/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers

/-!
# `VmPreserved` Unpinning Bridges for `V1State::encoded_len`

Unpinning bridges `v1StateEncodedLen_ro_ok_of_pinned` and `v1StateEncodedLen_ro_lscl_ok_of_pinned`
for `DefsV1StateBudget.v1StateEncodedLenRo{Pinned,}Spec`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersBudget

open _root_.Arm64 _root_.Arm64.Obj ProofLib SepProp
open CryptoVerification (withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.ProtoRepr (v1StatePBAt)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec v1StateEncodedLenRoSpec)

theorem v1StateEncodedLen_ro_ok_of_pinned {prog : Program} {entry roBase : BitVec 64}
    {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (v1StateEncodedLenRoPinnedSpec A roBase)) :
    subroutine_ok prog entry (v1StateEncodedLenRoSpec A roBase) := by
  apply subroutine_ok_outcome_intro
  intro ⟨a, m⟩ R s0 hpc hrun hpre hsp
  dsimp only [v1StateEncodedLenRoSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoSpec, v1StatePBAt,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine (hpinned.to_outcome ⟨a, g, m⟩ R s0 hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [v1StateEncodedLenRoPinnedSpec, v1StateEncodedLenRoSpec, withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoSpec, v1StatePBAt,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem v1StateEncodedLen_ro_lscl_ok_of_pinned {prog : Program} {entry roBase : BitVec 64}
    {pl : MultiPlacement} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded pl (v1StateEncodedLenRoPinnedSpec A roBase))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (v1StateEncodedLenRoSpec A roBase)) := by
  apply subroutine_ok_outcome_intro
  intro ⟨a, m⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded, v1StateEncodedLenRoSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoSpec, v1StatePBAt,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine (hpinned.to_outcome ⟨a, g, m⟩ R s0 hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, v1StateEncodedLenRoPinnedSpec, v1StateEncodedLenRoSpec,
      withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoSpec, v1StatePBAt,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersBudget
