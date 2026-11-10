/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.DefsCompI0

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompRI0Census
open DY.Libsignal (HwBytes)
open DY.X25519 (isLowOrderKey)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
def zeroDh : HwBytes := List.replicate 32 0#8
def I0Default (b : HwBytes) : Prop := b = compDefaultPub ∨ b = compDefaultDh ∨ b = zeroDh ∨ b = compDefaultKyberSs
instance (b : HwBytes) : Decidable (I0Default b) := by unfold I0Default; infer_instance
theorem compPubOfIdx_not_default (i : Fin 12) : ¬ I0Default (compPubOfIdx i) := by revert i; decide +kernel
def dhRows : List (Nat × Nat) := [(0, 3), (1, 3), (1, 4), (2, 3), (2, 5), (3, 6), (3, 7), (3, 9), (3, 10), (4, 6), (4, 9), (7, 8), (7, 11)]
def DhRow (i j : Fin 12) : Prop := (min i.val j.val, max i.val j.val) ∈ dhRows
instance (i j : Fin 12) : Decidable (DhRow i j) := by unfold DhRow; infer_instance
theorem compLookupDh_cases (s p : HwBytes) : (isLowOrderKey (p.map BitVec.toNat) = true ∧ compLookupDh s p = zeroDh) ∨ (isLowOrderKey (p.map BitVec.toNat) = false ∧ ∃ i j, compSecretIdx s = some i ∧ compPointIdx p = some j ∧ compLookupDh s p = compDhByIdx i j) ∨ (isLowOrderKey (p.map BitVec.toNat) = false ∧ (compSecretIdx s = none ∨ compPointIdx p = none) ∧ compLookupDh s p = compDefaultDh) := by
  unfold compLookupDh
  cases hlo : isLowOrderKey (p.map BitVec.toNat) with
  | true => exact Or.inl ⟨rfl, rfl⟩
  | false =>
    cases hs : compSecretIdx s with
    | none => exact Or.inr (Or.inr ⟨rfl, Or.inl rfl, rfl⟩)
    | some i =>
      cases hp : compPointIdx p with
      | none => exact Or.inr (Or.inr ⟨rfl, Or.inr rfl, rfl⟩)
      | some j => exact Or.inr (Or.inl ⟨rfl, i, j, rfl, rfl, rfl⟩)
theorem compLookupPub_cases (s : HwBytes) : compLookupPub s = compDefaultPub ∨ ∃ i, compLookupPub s = compPubOfIdx i := by
  unfold compLookupPub
  cases compSecretIdx s with
  | none => exact Or.inl rfl
  | some i => exact Or.inr ⟨i, rfl⟩
theorem compPubOfIdx_ne_compDhByIdx : ∀ i j k : Fin 12, compPubOfIdx i ≠ compDhByIdx j k := by decide +kernel
theorem compDefaultPub_ne_compDhByIdx : ∀ j k : Fin 12, compDefaultPub ≠ compDhByIdx j k := by decide +kernel
theorem compDefaultPub_ne_dhDefaults : compDefaultPub ≠ zeroDh ∧ compDefaultPub ≠ compDefaultDh := by decide +kernel
theorem compLookupPub_ne_compLookupDh (s s' p : HwBytes) : compLookupPub s ≠ compLookupDh s' p := by
  rcases compLookupDh_cases s' p with ⟨_, hz⟩ | ⟨_, j, k, _, _, hv⟩ | ⟨_, _, hd⟩ <;>
    rcases compLookupPub_cases s with hp | ⟨i, hp⟩ <;> rw [hp]
  · rw [hz]; exact compDefaultPub_ne_dhDefaults.1
  · rw [hz]; exact fun h => compPubOfIdx_not_default i (Or.inr (Or.inr (Or.inl h)))
  · rw [hv]; exact compDefaultPub_ne_compDhByIdx j k
  · rw [hv]; exact compPubOfIdx_ne_compDhByIdx i j k
  · rw [hd]; exact compDefaultPub_ne_dhDefaults.2
  · rw [hd]; exact fun h => compPubOfIdx_not_default i (Or.inr (Or.inl h))
def KyberSsVal (b : HwBytes) : Prop := b = compDefaultKyberSs ∨ b = compKyberSs0 ∨ b = compKyberSs1 ∨ b = compKyberSs2
instance (b : HwBytes) : Decidable (KyberSsVal b) := by unfold KyberSsVal; infer_instance
section Gamma
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection
private theorem gamma_dhPk_compI0 (S : Sem) (g : Ghost) (sk : DY.Bytes) : gamma compI0 S g (DY.DiffieHellman.dhPk sk) = compLookupPub (clamp (gamma compI0 S g sk)) := by
  unfold gamma gamma'
  show ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (gAll compI0 S g)).val = _
  rw [DY.Bytes.rec_eq (gDhPk compI0) (gAll compI0 S g)]; rfl
private theorem gamma_dh_pack_compI0 (S : Sem) (g : Ghost) (pk sk : DY.Bytes) : gamma compI0 S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) = compLookupDh (clamp (gamma compI0 S g sk)) (gamma compI0 S g pk) := by unfold gamma gamma'; rw [DY.Bytes.rec_eq (gDh compI0) (gAll compI0 S g)]; rfl
theorem gamma_dhPk_ne_dh_pack (S : Sem) (g : Ghost) (sk pk sk' : DY.Bytes) : gamma compI0 S g (DY.DiffieHellman.dhPk sk) ≠ gamma compI0 S g (({ pk := pk, sk := sk' } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by rw [gamma_dhPk_compI0, gamma_dh_pack_compI0]; exact compLookupPub_ne_compLookupDh _ _ _
end Gamma
end Symbolic.BugInjection.Proofs.Common443.CompRI0Census
