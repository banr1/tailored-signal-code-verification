/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore
public import Symbolic.BugInjection.Proofs.Common443.CompRWs81UntaggedShape

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore
def IsKdf (u : DY.Bytes) : Prop := ∃ k m : DY.Bytes, u = DY.KdfExtract.kdfExtract k m
def IsDhPk (u : DY.Bytes) : Prop := ∃ s : DY.Bytes, u = DY.DiffieHellman.dhPk s
def IsDh (u : DY.Bytes) : Prop := ∃ p s : DY.Bytes, u = (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)
def IsTrunc8 (u : DY.Bytes) : Prop := ∃ a : DY.Bytes, u = DY.Trunc.trunc8 a
def IsX (u : DY.Bytes) : Prop := IsDhPk u ∨ IsDh u
variable {S : Sem} {g : Ghost}
theorem gamma_mem_x25519Vals_of_isX {u : DY.Bytes} (h : IsX u) : gamma compI0 S g u ∈ x25519Vals := by
  rcases h with ⟨s, rfl⟩ | ⟨p, s, rfl⟩
  · rw [gamma_dhPk_compI0]; exact compLookupPub_mem _
  · rw [gamma_dh_pack_compI0]; exact compLookupDh_mem _ _
theorem gamma_length_of_isX {u : DY.Bytes} (h : IsX u) : (gamma compI0 S g u).length = 32 := x25519Vals_length _ (gamma_mem_x25519Vals_of_isX h)
theorem gamma_length_of_isKdf {u : DY.Bytes} (h : IsKdf u) : (gamma compI0 S g u).length = 32 := by obtain ⟨k, m, rfl⟩ := h; exact gamma_kdfExtract_length k m
def CrossSep (u₁ u₂ : DY.Bytes) : Prop := (IsKdf u₁ ∧ IsX u₂) ∨ (IsX u₁ ∧ IsKdf u₂) ∨ (IsDhPk u₁ ∧ IsDh u₂) ∨ (IsDh u₁ ∧ IsDhPk u₂) ∨ (IsTrunc8 u₁ ∧ (IsKdf u₂ ∨ IsX u₂)) ∨ ((IsKdf u₁ ∨ IsX u₁) ∧ IsTrunc8 u₂)
theorem shapeAgree_kdf_x {u₁ u₂ : DY.Bytes} (h₁ : IsKdf u₁) (h₂ : IsX u₂) : ShapeAgree S g u₁ u₂ := by obtain ⟨k, m, rfl⟩ := h₁; exact shapeAgree_kdf_of_kdfFree (kdfFree_of_mem_x25519Vals (gamma_mem_x25519Vals_of_isX h₂))
theorem shapeAgree_dhPk_dh' {u₁ u₂ : DY.Bytes} (h₁ : IsDhPk u₁) (h₂ : IsDh u₂) : ShapeAgree S g u₁ u₂ := by obtain ⟨s, rfl⟩ := h₁; obtain ⟨p, s', rfl⟩ := h₂; exact CompRWs81UntaggedShape.shapeAgree_dhPk_dh s p s'
theorem shapeAgree_trunc8_of_32 {u₁ u₂ : DY.Bytes} (h₁ : IsTrunc8 u₁) (h₂ : IsKdf u₂ ∨ IsX u₂) : ShapeAgree S g u₁ u₂ := by
  obtain ⟨a, rfl⟩ := h₁; refine shapeAgree_trunc8_of_len32 ?_
  rcases h₂ with h | h
  · exact gamma_length_of_isKdf h
  · exact gamma_length_of_isX h
theorem shapeAgree_of_crossSep {u₁ u₂ : DY.Bytes} (h : CrossSep u₁ u₂) : ShapeAgree S g u₁ u₂ := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact shapeAgree_kdf_x h₁ h₂
  · exact (shapeAgree_kdf_x h₂ h₁).symm
  · exact shapeAgree_dhPk_dh' h₁ h₂
  · exact (shapeAgree_dhPk_dh' h₂ h₁).symm
  · exact shapeAgree_trunc8_of_32 h₁ h₂
  · exact (shapeAgree_trunc8_of_32 h₂ h₁).symm
def QRest : PairQ := fun S g known pts x₁ x₂ =>
  ¬ IsKdf x₁.1 → ¬ CrossSep x₁.1 x₂.1 → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → ShapeAgree S g x₁.1 x₂.1
theorem qUntagged_of_kdf_rest (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (hK : QKdf S g known pts x₁ x₂) (hR : QRest S g known pts x₁ x₂) : QUntagged S g known pts x₁ x₂ := by
  intro hs hu
  by_cases hk : IsKdf x₁.1
  · obtain ⟨k, m, he⟩ := hk; exact hK k m he hs hu
  · by_cases hc : CrossSep x₁.1 x₂.1
    · exact shapeAgree_of_crossSep hc
    · exact hR hk hc hs hu
theorem untaggedW_of_kdf_rest {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (hK : Split38PairsAt QKdf w τ wire v t) (hR : Split38PairsAt QRest w τ wire v t) : Split38PairsAt QUntagged w τ wire v t :=
  split38PairsAt_of₂ (fun S g known pts x₁ x₂ _ _ _ _ h₁ h₂ =>
    qUntagged_of_kdf_rest S g known pts x₁ x₂ h₁ h₂) hK hR
end Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape
