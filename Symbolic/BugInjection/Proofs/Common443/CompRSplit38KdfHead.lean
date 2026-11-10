/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore
public import Symbolic.BugInjection.Proofs.Common443.CompRWs81KdfHead
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38Untagged

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRSplit38KdfHead
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj Symbolic.BugInjection.Proofs.Common443.CompRWs81KdfHead Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore
def QKdfUPar : PairQ := fun S g known pts x₁ x₂ =>
  ∀ k m : DY.Bytes, x₁.1 = DY.KdfExtract.kdfExtract k m → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → UPar S g x₁.1 x₂.1
theorem qKdf_of_qKdfUPar (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (h : QKdfUPar S g known pts x₁ x₂) : QKdf S g known pts x₁ x₂ :=
  fun k m hk hs hu => (h k m hk hs hu).shapeAgree hu
section Head
variable {S : Sem} {g : Ghost}
def KdfPartner (S : Sem) (g : Ghost) (k₁ m₁ u : DY.Bytes) : Prop := (∃ k₂ m₂, u = DY.KdfExtract.kdfExtract k₂ m₂ ∧ (gamma compI0 S g k₁).length ≤ 64 ∧ (gamma compI0 S g k₂).length ≤ 64 ∧ (padKey (gamma compI0 S g k₁) = padKey (gamma compI0 S g k₂) → (gamma compI0 S g k₁).length = (gamma compI0 S g k₂).length) ∧ UPar S g k₁ k₂ ∧ UPar S g m₁ m₂) ∨ (∃ s, u = DY.DiffieHellman.dhPk s) ∨ (∃ p s, u = (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)) ∨ KdfFree (gamma compI0 S g u) ∨ (gamma compI0 S g u).length ≠ 32 ∨ (gamma' compI0 S g (DY.KdfExtract.kdfExtract k₁ m₁)).shape = (gamma' compI0 S g u).shape
def KdfPartner32 (S : Sem) (g : Ghost) (k₁ m₁ u : DY.Bytes) : Prop := (∃ k₂ m₂, u = DY.KdfExtract.kdfExtract k₂ m₂ ∧ (gamma compI0 S g k₁).length = 32 ∧ (gamma compI0 S g k₂).length = 32 ∧ UPar S g k₁ k₂ ∧ UPar S g m₁ m₂) ∨ (∃ s, u = DY.DiffieHellman.dhPk s) ∨ (∃ p s, u = (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)) ∨ KdfFree (gamma compI0 S g u) ∨ (gamma compI0 S g u).length ≠ 32 ∨ (gamma' compI0 S g (DY.KdfExtract.kdfExtract k₁ m₁)).shape = (gamma' compI0 S g u).shape
theorem kdfPartner_of_32 {k₁ m₁ u : DY.Bytes} (h : KdfPartner32 S g k₁ m₁ u) : KdfPartner S g k₁ m₁ u := by
  rcases h with ⟨k₂, m₂, hu, h₁, h₂, hK, hM⟩ | h | h | h | h | h
  · exact Or.inl ⟨k₂, m₂, hu, by omega, by omega, fun _ => by omega, hK, hM⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
theorem upar_of_kdfPartner {k₁ m₁ u : DY.Bytes} (h : KdfPartner S g k₁ m₁ u) : UPar S g (DY.KdfExtract.kdfExtract k₁ m₁) u := upar_kdf_head h
end Head
def QKdfHead : PairQ := fun S g known pts x₁ x₂ =>
  ∀ k m : DY.Bytes, x₁.1 = DY.KdfExtract.kdfExtract k m → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → gamma compI0 S g x₁.1 = gamma compI0 S g x₂.1 → KdfPartner S g k m x₂.1
def QKdfHead32 : PairQ := fun S g known pts x₁ x₂ =>
  ∀ k m : DY.Bytes, x₁.1 = DY.KdfExtract.kdfExtract k m → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → gamma compI0 S g x₁.1 = gamma compI0 S g x₂.1 → KdfPartner32 S g k m x₂.1
theorem qKdfUPar_of_head (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (h : QKdfHead S g known pts x₁ x₂) : QKdfUPar S g known pts x₁ x₂ := by
  intro k m hk hs hu
  by_cases he : gamma compI0 S g x₁.1 = gamma compI0 S g x₂.1
  · have hp := h k m hk hs hu he; rw [hk]; exact upar_of_kdfPartner hp
  · exact .of_shapeAgree (shapeAgree_of_gamma_ne he)
theorem qKdfHead_of_32 (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (h : QKdfHead32 S g known pts x₁ x₂) : QKdfHead S g known pts x₁ x₂ :=
  fun k m hk hs hu he => kdfPartner_of_32 (h k m hk hs hu he)
theorem qKdf_of_head (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (h : QKdfHead S g known pts x₁ x₂) : QKdf S g known pts x₁ x₂ := qKdf_of_qKdfUPar S g known pts x₁ x₂ (qKdfUPar_of_head S g known pts x₁ x₂ h)
theorem split38PairsAt_qKdf_of_head {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (h : Split38PairsAt QKdfHead w τ wire v t) : Split38PairsAt QKdf w τ wire v t :=
  split38PairsAt_mono (fun S g known pts x₁ x₂ _ _ _ _ hq => qKdf_of_head S g known pts x₁ x₂ hq) h
theorem split38PairsAt_qKdf_of_head32 {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (h : Split38PairsAt QKdfHead32 w τ wire v t) : Split38PairsAt QKdf w τ wire v t :=
  split38PairsAt_qKdf_of_head
    (split38PairsAt_mono (fun S g known pts x₁ x₂ _ _ _ _ hq => qKdfHead_of_32 S g known pts x₁ x₂ hq) h)
end Symbolic.BugInjection.Proofs.Common443.CompRSplit38KdfHead
