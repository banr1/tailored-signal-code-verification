/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38KdfHead

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRSplit38QKdf
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRNoBSC
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc (zeroSaltedTermsStA)
open Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj (KdfFree)
open Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompRWs81KdfHead Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore Symbolic.BugInjection.Proofs.Common443.CompRSplit38KdfHead Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
section ViewKdf
unseal DY.Bytes
theorem assumedInjective_kdfExtract (k m : DY.Bytes) : assumedInjective (DY.KdfExtract.kdfExtract k m) = true := by unfold assumedInjective; dsimp only [DY.KdfExtract.kdfExtract, DY.KdfExtract.CanKdfExtract.kdfExtract]; rw [DY.BytesView.view_pack]; simp
end ViewKdf
section Census
variable {S : Sem} {g : Ghost}
theorem gamma_zeroKey_length (S : Sem) (g : Ghost) : (gamma compI0 S g DY.Spqr.zeroKey).length = 32 := CompRSplit38Untagged.gamma_zeroSalt_length S g
theorem kdfSalt32_zeroSalted {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x.1 ∈ zeroSaltedTermsStA tr₂ stA cl pq) : KdfSalt32 S g x := by
  intro k m hk; unfold zeroSaltedTermsStA at hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h <;> rw [hk] at h
  · rw [kdfExtract_salt_eq h]; exact gamma_zeroKey_length S g
  · rw [kdfExtract_salt_eq h]; exact CompRI0TermInj.gamma_kdfExtract_length _ _
  · rw [kdfExtract_salt_eq h]; exact CompRI0TermInj.gamma_kdfExtract_length _ _
  · rw [kdfExtract_salt_eq h]; exact CompRI0TermInj.gamma_kdfExtract_length _ _
  · rw [kdfExtract_salt_eq h]; exact CompRI0TermInj.gamma_kdfExtract_length _ _
  · exact absurd h (ne_kdfExtract_of_notKdf (nk_trunc8 _) k m).symm
theorem kdfSalt32_of_split38MemoClass {r : Records} (hNe : r.alice ≠ r.bob) (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let ms := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post;
    ModelRun r ms → MovesFrom InvisibleNoEffect (setupTrace r) pre →
    MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
    MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c'))).next tr₂) post →
    m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o →
    ∀ x, CompRNbsc38VT.Split38MemoClass r S g ms' tr₁ tr₂ cl x → KdfSalt32 S g x := by
  intro tr₁ o m₀ tr₂ pq ms ms' hmr hpre hmid hpost hm₀ x hc; unfold CompRNbsc38VT.Split38MemoClass at hc; dsimp only at hc
  rcases hc with hpm | hai | hz
  · exact kdfSalt32_preMemo_split38_of_modelRun (i := compI0) (S := S) (g := g) hNe pre mid post hb shown cl e c' hmr hpre hmid hpost hm₀ x hpm
  · intro k m hk; rw [hk, assumedInjective_kdfExtract] at hai; cases hai
  · exact kdfSalt32_zeroSalted hz
end Census
section Partner
variable {S : Sem} {g : Ghost}
def KdfPartnerC (S : Sem) (g : Ghost) (k₁ m₁ u : DY.Bytes) : Prop := (∃ k₂ m₂, u = DY.KdfExtract.kdfExtract k₂ m₂ ∧ UPar S g k₁ k₂ ∧ UPar S g m₁ m₂) ∨ (∃ s, u = DY.DiffieHellman.dhPk s) ∨ (∃ p s, u = (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)) ∨ KdfFree (gamma compI0 S g u) ∨ (gamma compI0 S g u).length ≠ 32 ∨ (gamma' compI0 S g (DY.KdfExtract.kdfExtract k₁ m₁)).shape = (gamma' compI0 S g u).shape
theorem kdfPartner32_of_c {k₁ m₁ u : DY.Bytes} (h₁ : (gamma compI0 S g k₁).length = 32) (h₂ : ∀ k₂ m₂, u = DY.KdfExtract.kdfExtract k₂ m₂ → (gamma compI0 S g k₂).length = 32) (h : KdfPartnerC S g k₁ m₁ u) : KdfPartner32 S g k₁ m₁ u := by
  rcases h with ⟨k₂, m₂, hu, hK, hM⟩ | h | h | h | h | h
  · exact Or.inl ⟨k₂, m₂, hu, h₁, h₂ k₂ m₂ hu, hK, hM⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
end Partner
def QKdfC : PairQ := fun S g known pts x₁ x₂ =>
  ∀ k m : DY.Bytes, x₁.1 = DY.KdfExtract.kdfExtract k m → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → gamma compI0 S g x₁.1 = gamma compI0 S g x₂.1 → KdfPartnerC S g k m x₂.1
theorem qKdfHead32_of_c (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (hs₁ : KdfSalt32 S g x₁) (hs₂ : KdfSalt32 S g x₂) (h : QKdfC S g known pts x₁ x₂) : QKdfHead32 S g known pts x₁ x₂ :=
  fun k m hk hps hu he => kdfPartner32_of_c (hs₁ k m hk) hs₂ (h k m hk hps hu he)
theorem split38PairsAt_head32_of_c {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (h : Split38PairsAt QKdfC w τ wire v t) : Split38PairsAt QKdfHead32 w τ wire v t := by intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have h' := h r S g p hfits hp hopk pre mid post hb shown cl e c'; have hNe : r.alice ≠ r.bob := hfits.1.1.1; have hcen := kdfSalt32_of_split38MemoClass (S := S) (g := g) hNe pre mid post hb shown cl e c'; dsimp only at h' hcen ⊢; intro hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; exact qKdfHead32_of_c S g _ _ x₁ x₂ (hcen hrun hpre hmid hpost hm₀ x₁ hc₁) (hcen hrun hpre hmid hpost hm₀ x₂ hc₂) (h' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂)
theorem split38PairsAt_qKdf_of_c {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (h : Split38PairsAt QKdfC w τ wire v t) : Split38PairsAt QKdf w τ wire v t :=
  split38PairsAt_qKdf_of_head32 (split38PairsAt_head32_of_c h)
end Symbolic.BugInjection.Proofs.Common443.CompRSplit38QKdf
