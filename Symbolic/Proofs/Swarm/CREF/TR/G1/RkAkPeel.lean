/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeel
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal

/-!
# One-Sided Peel Under Relaxed Seed Separation

Proves `oneSidedPeelAK` and `false_of_oneSidedPeelAK`, establishing the one-sided spine peel under
the relaxed seed separation hypothesis `SeedSepAK`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY.DiffieHellman
open DY.Libsignal.TripleRatchet (hmac hkdfBlock1 lit litByte zeroSalt)
open DY.Libsignal.PQXDH (pqxdhLabel)
open CryptoProofLib.Refinement (ExternInterpretation)

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

/-- Relaxed seed separation: an attacker-known honest or skipped-seed term `u'` in the memo window
of `t₁` matching the `gamma'` shape of a `Q`-term `v'` in the memo window of `t₂` equals `v'`,
forces `v'` to be attacker-known, or decomposes `u'` as `kdfExtract` on attacker-known inputs. -/
def SeedSepAK (T : ExecTrace) (Q : DY.Bytes → Prop) (t₁ t₂ : DY.Bytes) : Prop :=
  ∀ (u' v' : DY.Bytes), u'.AttackerKnows T → (HonestKdfOut T u' ∨ SkippedSeedLogged T u') → Q v' →
    (∀ e ∈ (gamma' i S g u').memo, e ∈ (gamma' i S g t₁).memo) →
    (∀ e ∈ (gamma' i S g v').memo, e ∈ (gamma' i S g t₂).memo) →
    (gamma' i S g u').shape = (gamma' i S g v').shape →
    u' = v' ∨ v'.AttackerKnows T ∨
      ∃ s i, u' = KdfExtract.kdfExtract s i ∧ s.AttackerKnows T ∧ i.AttackerKnows T

theorem peel_stepAK {T : ExecTrace} (hT : ReachableTrace T) {Q : DY.Bytes → Prop}
    {t₁ t₂ : DY.Bytes} (hSP : SeedSepAK i S g T Q t₁ t₂)
    {s₁ i₁ u : DY.Bytes} (hQv : Q (KdfExtract.kdfExtract s₁ i₁))
    (h7 : ∀ b1, (gamma' i S g (Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3)))).shape ≠
      (gamma' i S g i₁).shape)
    (hu : u.AttackerKnows T)
    (hm₁ : ∀ e ∈ (gamma' i S g u).memo, e ∈ (gamma' i S g t₁).memo)
    (hm₂ : ∀ e ∈ (gamma' i S g (KdfExtract.kdfExtract s₁ i₁)).memo, e ∈ (gamma' i S g t₂).memo)
    (hsh : (gamma' i S g u).shape = (gamma' i S g (KdfExtract.kdfExtract s₁ i₁)).shape) :
    (KdfExtract.kdfExtract s₁ i₁).AttackerKnows T ∨
      ∃ s' i', u = KdfExtract.kdfExtract s' i' ∧
        (gamma' i S g s').shape = (gamma' i S g s₁).shape ∧
        (gamma' i S g i').shape = (gamma' i S g i₁).shape ∧
        s'.AttackerKnows T ∧ i'.AttackerKnows T := by
  obtain ⟨s', i', hu_eq, hs, hi, hprov⟩ := peel_outer i S g hT hu hsh
  rcases hprov with hH | ⟨b1, rfl⟩ | ⟨hs', hi'⟩
  · rcases hSP u _ hu hH hQv hm₁ hm₂ hsh with h | h | ⟨s'', i'', hu'', hs'', hi''⟩
    · exact .inl (by rw [← h]; exact hu)
    · exact .inl h
    · obtain ⟨h1, h2⟩ := kdfExtract_injective (hu_eq.symm.trans hu'')
      exact .inr ⟨s', i', hu_eq, hs, hi, h1 ▸ hs'', h2 ▸ hi''⟩
  · exact absurd hi (h7 b1)
  · exact .inr ⟨s', i', hu_eq, hs, hi, hs', hi'⟩

/-- One-sided spine peel under `SeedSepAK`: if `v` lies on a known-peer-key seed spine with
`IkmHolesKemK` base IKMs and an attacker-known `u` in the memo window of `t₁` matches the shape of
`v` in the memo window of `t₂`, then `v` is attacker-known. -/
theorem oneSidedPeelAK {T : ExecTrace} (hT : ReachableTrace T) {Q : DY.Bytes → Prop}
    (hQ : SpineDown Q) {B : Bool → DY.Bytes → Prop}
    (hKemB : ∀ {c : Bool} {ikm : DY.Bytes}, B c ikm → IkmHolesKemK i S g T ikm)
    {t₁ t₂ : DY.Bytes} (hSP : SeedSepAK i S g T Q t₁ t₂)
    {c : Bool} {v : DY.Bytes} (hv : SpineRkK (·.AttackerKnows T) B c v) :
    Q v → ∀ {u : DY.Bytes}, u.AttackerKnows T →
      (∀ e ∈ (gamma' i S g u).memo, e ∈ (gamma' i S g t₁).memo) →
      (∀ e ∈ (gamma' i S g v).memo, e ∈ (gamma' i S g t₂).memo) →
      (gamma' i S g u).shape = (gamma' i S g v).shape →
      v.AttackerKnows T := by
  induction hv with
  | @hsRk c ikm hB _ =>
    intro hQv u hu hm₁ hm₂ hsh
    have hQv' : Q (KdfExtract.kdfExtract (hmac zeroSalt ikm)
        (Concat.concat pqxdhLabel (litByte 1))) := hQv
    rcases peel_stepAK i S g hT hSP hQv' (no7_x1 i S g _) hu hm₁ hm₂ hsh with h |
        ⟨s', i', rfl, hs, -, hs', -⟩
    · exact h
    · exact ak_hkdfBlock1 (ak_hmac (ak_lit _) (peel_ikm i S g hT (hKemB hB) hs' hs)) (ak_lit _)
  | @hsCk c ikm hB _ =>
    intro hQv u hu hm₁ hm₂ hsh
    have hQv' : Q (KdfExtract.kdfExtract (hmac zeroSalt ikm)
        (Concat.concat (hkdfBlock1 (hmac zeroSalt ikm) pqxdhLabel)
          (Concat.concat pqxdhLabel (litByte 2)))) := hQv
    rcases peel_stepAK i S g hT hSP hQv' (no7_pq2 i S g _) hu hm₁ hm₂ hsh with h |
        ⟨s', i', rfl, hs, -, hs', -⟩
    · exact h
    · exact ak_hkdfBlock2 (ak_hmac (ak_lit _) (peel_ikm i S g hT (hKemB hB) hs' hs)) (ak_lit _)
  | @rkStep1 c rk d hrk hRk hD ih =>
    intro hQv u hu hm₁ hm₂ hsh
    have hQv' : Q (KdfExtract.kdfExtract (hmac rk d)
        (Concat.concat (lit "WhisperRatchet") (litByte 1))) := hQv
    rcases peel_stepAK i S g hT hSP hQv' (no7_x1 i S g _) hu hm₁ hm₂ hsh with h |
        ⟨s', i', rfl, hs, -, hs', -⟩
    · exact h
    · obtain ⟨rk', d', rfl, hrk', hrkK', hdK⟩ := peel_rk i S g hT hD hs' hs
      have h := ih (hQ.rk1 hQv) hrkK'
        (fun x hx => hm₁ _ (memo_mem_of_kdfExtract_left i S g _ _
          (memo_mem_of_kdfExtract_left i S g _ _ hx)))
        (fun x hx => hm₂ _ (memo_mem_of_kdfRk_fst_rk i S g _ _ hx)) hrk'
      exact ak_hkdfBlock1 (ak_hmac h hdK) (ak_lit _)
  | @rkStep2 c rk d hrk hRk hD ih =>
    intro hQv u hu hm₁ hm₂ hsh
    have hQv' : Q (KdfExtract.kdfExtract (hmac rk d)
        (Concat.concat (hkdfBlock1 (hmac rk d) (lit "WhisperRatchet"))
          (Concat.concat (lit "WhisperRatchet") (litByte 2)))) := hQv
    rcases peel_stepAK i S g hT hSP hQv' (no7_wr2 i S g _) hu hm₁ hm₂ hsh with h |
        ⟨s', i', rfl, hs, -, hs', -⟩
    · exact h
    · obtain ⟨rk', d', rfl, hrk', hrkK', hdK⟩ := peel_rk i S g hT hD hs' hs
      have h := ih (hQ.rk2 hQv) hrkK'
        (fun x hx => hm₁ _ (memo_mem_of_kdfExtract_left i S g _ _
          (memo_mem_of_kdfExtract_left i S g _ _ hx)))
        (fun x hx => hm₂ _ (memo_mem_of_kdfRk_snd_rk i S g _ _ hx)) hrk'
      exact ak_hkdfBlock2 (ak_hmac h hdK) (ak_lit _)
  | @ckStep1 c ck hck ih =>
    intro hQv u hu hm₁ hm₂ hsh
    have hQv' : Q (KdfExtract.kdfExtract ck (litByte 2)) := hQv
    rcases peel_stepAK i S g hT hSP hQv' (no7_lit i S g _) hu hm₁ hm₂ hsh with h |
        ⟨s', i', rfl, hs, -, hs', -⟩
    · exact h
    · have h := ih (hQ.ck1 hQv) hs'
        (fun x hx => hm₁ _ (memo_mem_of_kdfExtract_left i S g _ _ hx))
        (fun x hx => hm₂ _ (memo_mem_of_kdfCk_fst i S g _ hx)) hs
      exact ak_hmac h (ak_lit _)
  | @ckStep2 c ck hck ih =>
    intro hQv u hu hm₁ hm₂ hsh
    have hQv' : Q (KdfExtract.kdfExtract ck (litByte 1)) := hQv
    rcases peel_stepAK i S g hT hSP hQv' (no7_lit i S g _) hu hm₁ hm₂ hsh with h |
        ⟨s', i', rfl, hs, -, hs', -⟩
    · exact h
    · have h := ih (hQ.ck2 hQv) hs'
        (fun x hx => hm₁ _ (memo_mem_of_kdfExtract_left i S g _ _ hx))
        (fun x hx => hm₂ _ (memo_mem_of_kdfCk_snd i S g _ hx)) hs
      exact ak_hmac h (ak_lit _)

theorem false_of_oneSidedPeelAK {T : ExecTrace} (hT : ReachableTrace T)
    {Q : DY.Bytes → Prop} (hQ : SpineDown Q) {B : Bool → DY.Bytes → Prop}
    (hKemB : ∀ {c : Bool} {ikm : DY.Bytes}, B c ikm → IkmHolesKemK i S g T ikm)
    {t₁ t₂ : DY.Bytes} (hSP : SeedSepAK i S g T Q t₁ t₂)
    {c : Bool} {u v : DY.Bytes} (hv : SpineRkK (·.AttackerKnows T) B c v) (hQv : Q v)
    (hvK : ¬v.AttackerKnows T) (hu : u.AttackerKnows T)
    (hm₁ : ∀ e ∈ (gamma' i S g u).memo, e ∈ (gamma' i S g t₁).memo)
    (hm₂ : ∀ e ∈ (gamma' i S g v).memo, e ∈ (gamma' i S g t₂).memo)
    (hsh : (gamma' i S g u).shape = (gamma' i S g v).shape) :
    False :=
  hvK (oneSidedPeelAK i S g hT hQ hKemB hSP hv hQv hu hm₁ hm₂ hsh)

end Symbolic.Swarm.CREF.TR.G1.Spine
