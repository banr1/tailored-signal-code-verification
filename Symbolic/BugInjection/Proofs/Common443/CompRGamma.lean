/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompRGamma
open DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.DiffieHellman
open DY.X25519 (leValue p25519)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (x25519PublicKeySymbol x25519AgreementSymbol CryptoEquationsHold)
open DY.Libsignal.PQXDH (agree)
theorem gamma_dhPk (interpretation : ExternInterpretation) (S : Sem) (g : Ghost) (sk : DY.Bytes) : gamma interpretation S g (DY.DiffieHellman.dhPk sk) = (interpretation x25519PublicKeySymbol [clamp (gamma interpretation S g sk)]).getD [] := by
  unfold gamma gamma'
  show ((({sk} : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (gAll interpretation S g)).val = _
  rw [DY.Bytes.rec_eq (gDhPk interpretation) (gAll interpretation S g)]; rfl
theorem gamma_dh_raw (interpretation : ExternInterpretation) (S : Sem) (g : Ghost) (pk sk : DY.Bytes) : gamma interpretation S g (({pk, sk} : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) = (interpretation x25519AgreementSymbol [clamp (gamma interpretation S g sk), gamma interpretation S g pk]).getD [] := by unfold gamma gamma'; rw [DY.Bytes.rec_eq (gDh interpretation) (gAll interpretation S g)]; rfl
theorem gamma_dh (interpretation : ExternInterpretation) (hEq : CryptoEquationsHold interpretation) (S : Sem) (g : Ghost) (pk sk : DY.Bytes) : gamma interpretation S g (DY.DiffieHellman.dh pk sk) = (interpretation x25519AgreementSymbol [clamp (gamma interpretation S g sk), gamma interpretation S g pk]).getD [] := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk; simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv
    split
    · rw [gamma_dh_raw]
    · rw [gamma_dh_raw]
      show (interpretation x25519AgreementSymbol [clamp (gamma interpretation S g sk2), gamma interpretation S g (dhPk sk)]).getD [] = (interpretation x25519AgreementSymbol [clamp (gamma interpretation S g sk), gamma interpretation S g (dhPk sk2)]).getD []
      rw [gamma_dhPk, gamma_dhPk, hEq.x25519_agreement_commutes (clamp (gamma interpretation S g sk2)) (clamp (gamma interpretation S g sk))]
  · rw [gamma_dh_raw]
theorem length_leBytes : ∀ n w, (leBytes n w).length = n
  | 0, _ => rfl
  | n + 1, w => by simp [leBytes, length_leBytes n]
theorem leValue_leBytes : ∀ n w, leValue ((leBytes n w).map BitVec.toNat) = w % 256 ^ n
  | 0, w => by simp [leBytes, leValue, Nat.mod_one]
  | n + 1, w => by
    have h : w % 256 ^ (n + 1) = w % 256 + 256 * (w / 256 % 256 ^ n) := by rw [Nat.pow_succ', Nat.mod_mul]
    simp only [leBytes, List.map_cons, leValue, leValue_leBytes n, BitVec.toNat_ofNat]; exact h.symm
theorem p25519_lt : p25519 < 2 ^ 255 := by unfold p25519; omega
theorem p25519_pos : 0 < p25519 := by unfold p25519; omega
theorem uOf_lt (b : HwBytes) : uOf b < p25519 := Nat.mod_lt _ p25519_pos
theorem uOf_leBytes (w : Nat) (hw : w < 2 ^ 256) : uOf (leBytes 32 w) = w % 2 ^ 255 % p25519 := by
  unfold uOf x25519UCoord DY.X25519.uCoord
  have hpow : w < 256 ^ 32 := by omega
  rw [leValue_leBytes, Nat.mod_eq_of_lt hpow]
theorem variantBytes_spec (b : HwBytes) (hb : b.length = 32) (v : Fin 4) : (variantBytes b v).length = 32 ∧ uOf (variantBytes b v) = uOf b := by
  unfold variantBytes; simp only [hb, ↓reduceIte]; refine ⟨length_leBytes _ _, ?_⟩; have hu := uOf_lt b; have hp := p25519_lt; unfold uOf at hu ⊢; generalize x25519UCoord b = u at hu ⊢
  have key : ∀ u', u' < 2 ^ 255 → u' % p25519 = u →
      x25519UCoord (leBytes 32 (if v.val % 2 = 1 then u' + 2 ^ 255 else u')) = u := by
    intro u' h1 h2
    split
    · rw [← uOf, uOf_leBytes _ (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt h1, h2]
    · rw [← uOf, uOf_leBytes _ (by omega), Nat.mod_eq_of_lt h1, h2]
  apply key
  · split <;> omega
  · split
    · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hu]
    · exact Nat.mod_eq_of_lt hu
theorem gamma_agree (interpretation : ExternInterpretation) (hEq : CryptoEquationsHold interpretation) (S : Sem) (g : Ghost) (pk sk : DY.Bytes) : gamma interpretation S g (agree pk sk) = (interpretation x25519AgreementSymbol [clamp (gamma interpretation S g sk), gamma interpretation S g pk]).getD [] := by
  unfold agree; rw [gamma_dh interpretation hEq]; unfold DY.X25519.normalizeX25519Key
  cases hview : pk.view? DY.X25519.Variant.SubF with
  | none => rfl
  | some v =>
    dsimp only; have hpack : v.pack = pk := (by have hp := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk; simpa [hview] using hp)
    have hgamma_pk : gamma interpretation S g pk = variantBytes (DY.Libsignal.Refinement.torsionShift interpretation
          (gamma interpretation S g v.key) v.torsion) v.variation := by
      rw [← hpack]; unfold gamma gamma'; rw [DY.Bytes.rec_eq (gVariant0 interpretation) (gAll interpretation S g)]; rfl
    rw [hgamma_pk]
    have htl : (DY.Libsignal.Refinement.torsionShift interpretation (gamma interpretation S g v.key) v.torsion).length =
          (gamma interpretation S g v.key).length := by
      unfold DY.Libsignal.Refinement.torsionShift
      split
      · rfl
      · rename_i h
        have hlen : (gamma interpretation S g v.key).length = 32 := by revert h; simp
        split
        · split
          · rename_i q _ hq; omega
          · rfl
        · rfl
    by_cases hlen : (gamma interpretation S g v.key).length = 32
    · have hlen' := htl.trans hlen; have hspec := variantBytes_spec _ hlen' v.variation; rw [← hEq.x25519_agreement_torsion_invariant (clamp (gamma interpretation S g sk)) (gamma interpretation S g v.key) v.torsion, hEq.x25519_agreement_reads_u_coordinate (clamp (gamma interpretation S g sk)) (DY.Libsignal.Refinement.torsionShift interpretation (gamma interpretation S g v.key) v.torsion) (variantBytes (DY.Libsignal.Refinement.torsionShift interpretation (gamma interpretation S g v.key) v.torsion) v.variation) hlen' hspec.1 hspec.2.symm]
    · have hts : DY.Libsignal.Refinement.torsionShift interpretation
          (gamma interpretation S g v.key) v.torsion = gamma interpretation S g v.key := by
        unfold DY.Libsignal.Refinement.torsionShift; simp [hlen]
      rw [hts]; unfold variantBytes; simp [hlen]
end Symbolic.BugInjection.Proofs.Common443.CompRGamma
