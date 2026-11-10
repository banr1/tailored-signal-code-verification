/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import Computational.Proofs.CryptoGames.AEAD.PrimitivesProofDefs
public import Computational.Proofs.CryptoGames.CKA.CKAProofDefs
public import Computational.Proofs.CryptoGames.SM.GameProofDefs

/-!
# Proof Helpers for Theorem 7

**Checked by Lean.** Basic `Party.sendsIn` parity and exhaustion lemmas for the Fig. 8 SM
correctness proof.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.Construction

theorem Party.sendsIn_succ (P : Party) (t : ℕ) :
    P.sendsIn (t + 1) = !P.sendsIn t := by
  cases P
  · dsimp only [Party.sendsIn]
    by_cases h : (t + 1) % 2 = 1
    · have h0 : t % 2 ≠ 1 := by omega
      rw [beq_iff_eq.mpr h, beq_eq_false_iff_ne.mpr h0]; rfl
    · have h0 : t % 2 = 1 := by omega
      rw [beq_eq_false_iff_ne.mpr h, beq_iff_eq.mpr h0]; rfl
  · dsimp only [Party.sendsIn]
    by_cases h : (t + 1) % 2 = 0
    · have h0 : t % 2 ≠ 0 := by omega
      rw [beq_iff_eq.mpr h, beq_eq_false_iff_ne.mpr h0]; rfl
    · have h0 : t % 2 = 0 := by omega
      rw [beq_eq_false_iff_ne.mpr h, beq_iff_eq.mpr h0]; rfl

theorem Party.other_sendsIn (P : Party) (t : ℕ) :
    P.other.sendsIn t = !P.sendsIn t := by
  cases P
  · dsimp only [Party.other, Party.sendsIn]
    by_cases h : t % 2 = 0
    · have h1 : t % 2 ≠ 1 := by omega
      rw [beq_iff_eq.mpr h, beq_eq_false_iff_ne.mpr h1]; rfl
    · have h1 : t % 2 = 1 := by omega
      rw [beq_eq_false_iff_ne.mpr h, beq_iff_eq.mpr h1]; rfl
  · dsimp only [Party.other, Party.sendsIn]
    by_cases h : t % 2 = 1
    · have h0 : t % 2 ≠ 0 := by omega
      rw [beq_iff_eq.mpr h, beq_eq_false_iff_ne.mpr h0]; rfl
    · have h0 : t % 2 = 0 := by omega
      rw [beq_eq_false_iff_ne.mpr h, beq_iff_eq.mpr h0]; rfl

theorem Party.sendsIn_eq_false_of_other (P : Party) (t : ℕ) (h : P.other.sendsIn t = true) :
    P.sendsIn t = false := by
  rw [Party.other_sendsIn, Bool.not_eq_true'] at h
  exact h

theorem Party.other_sendsIn_of_eq_false (P : Party) (t : ℕ) (h : P.sendsIn t = false) :
    P.other.sendsIn t = true := by
  rw [Party.other_sendsIn, h, Bool.not_false]

theorem Party.sendsIn_of_succ_eq_false (P : Party) (t : ℕ) (h : P.sendsIn (t + 1) = false) :
    P.sendsIn t = true := by
  rw [Party.sendsIn_succ, Bool.not_eq_false'] at h
  exact h

theorem Party.sendsIn_eq_false_of_succ (P : Party) (t : ℕ) (h : P.sendsIn (t + 1) = true) :
    P.sendsIn t = false := by
  rw [Party.sendsIn_succ, Bool.not_eq_true'] at h
  exact h

section Ratchet

variable {CK MK AD M C : Type}

end Ratchet

section CKA

variable {KC Γ CCoins T I : Type}

end CKA

section StateInv

variable {KC Γ CCoins T I : Type} {KR Sig : Type} {CK MK M C : Type}

theorem Party.eq_or_eq_other (P Q : Party) : Q = P ∨ Q = P.other := by
  cases P <;> cases Q <;> decide

theorem Party.forall_iff (P : Party) {Φ : Party → Prop} :
    (∀ Q, Φ Q) ↔ Φ P ∧ Φ P.other :=
  ⟨fun h => ⟨h P, h P.other⟩, fun ⟨h1, h2⟩ Q => by
    rcases Party.eq_or_eq_other P Q with rfl | rfl
    · exact h1
    · exact h2⟩

end StateInv

end CryptoGames.SM.Construction
