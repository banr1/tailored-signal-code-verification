/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkSeedSepBase
import ProofLib.Lemmas
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeel
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeelDefs

/-!
# Alice and Bob Handshake Root-Key Twins

Proves `aliceBobTwin_of_reachable`: on a reachable trace satisfying `AliceKemLen32`, an `AliceDone`
key bundle and a `BobDone` key bundle whose root keys have equal `gamma'` shapes have equal root
keys unless their memo windows satisfy `KemSlotAlias`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Libsignal.TripleRatchet Symbolic.Swarm.CREF.TR
open DY.Libsignal.PQXDH (HandshakeKeys pqxdhIkm pqxdhKdf)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompInv (SpqrInv spqrInv_of_reachable)

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

/-! ## Key schedules -/

private theorem bobTwin_keys_of_aliceAgreement {ikA ek ikB spk pq e ct : DY.Bytes}
    {opk : Option DY.Bytes} {keys : HandshakeKeys}
    (h : (ct, keys) = DY.Libsignal.PQXDH.aliceAgreement ikA ek ikB spk pq opk e) :
    keys = pqxdhKdf (pqxdhIkm (DY.Libsignal.PQXDH.agree spk ikA)
      (DY.Libsignal.PQXDH.agree ikB ek) (DY.Libsignal.PQXDH.agree spk ek)
      (opk.map (DY.Libsignal.PQXDH.agree · ek)) (DY.PQKem.kemEncap pq e).2) := by
  unfold DY.Libsignal.PQXDH.aliceAgreement at h
  generalize hk : DY.PQKem.kemEncap pq e = p at h ⊢
  obtain ⟨c₀, s₀⟩ := p
  simp only [Prod.mk.injEq] at h
  exact h.2

private theorem bobTwin_ikm_shape {ikm₁ ikm₂ : DY.Bytes}
    (hsh : (gamma' i S g (pqxdhKdf ikm₁).rk).shape = (gamma' i S g (pqxdhKdf ikm₂).rk).shape) :
    (gamma' i S g ikm₁).shape = (gamma' i S g ikm₂).shape :=
  (ShapeModKem.shape_kdfExtract_inj i S g (ShapeModKem.shape_kdfExtract_inj i S g hsh).1).2

private theorem bobTwin_ss_shape {a₁ b₁ c₁ a₂ b₂ c₂ ss₁ ss₂ : DY.Bytes}
    {d₁ d₂ : Option DY.Bytes}
    (hk₁ : ShapeModKem.KemLeaf ss₁) (hk₂ : ShapeModKem.KemLeaf ss₂)
    (hsh : (gamma' i S g (pqxdhIkm a₁ b₁ c₁ d₁ ss₁)).shape =
      (gamma' i S g (pqxdhIkm a₂ b₂ c₂ d₂ ss₂)).shape) :
    (gamma' i S g ss₁).shape = (gamma' i S g ss₂).shape := by
  unfold pqxdhIkm at hsh
  have h := (shape_concat_inj i S g (shape_concat_inj i S g (shape_concat_inj i S g
    (shape_concat_inj i S g hsh).2).2).2).2
  cases d₁ <;> cases d₂ <;> dsimp only at h
  · exact h
  · exact absurd h (ShapeModKem.shape_kemLeaf_ne_concat i S g hk₁)
  · exact absurd h.symm (ShapeModKem.shape_kemLeaf_ne_concat i S g hk₂)
  · exact (shape_concat_inj i S g h).2

/-! ## DH slot rigidity -/

private theorem bobTwin_view_dhPk (sk : DY.Bytes) :
    (dhPk sk).view? DY.DiffieHellman.DhPk.SubF = some { sk := sk } := by
  change DY.Bytes.view? (({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack)
    DY.DiffieHellman.DhPk.SubF = _
  exact DY.BytesView.view_pack _

private theorem bobTwin_dh_slot {X Y : DY.Bytes} {a b : Nat}
    (hsh : (gamma' i S g (dh X (CompKeyInversion.rnd a 32))).shape =
      (gamma' i S g (dh Y (CompKeyInversion.rnd b 32))).shape) :
    dh X (CompKeyInversion.rnd a 32) = dh Y (CompKeyInversion.rnd b 32) ∨ a = b := by
  have hrig : ∀ {c d : Nat}, (gamma' i S g (CompKeyInversion.rnd c 32)).shape =
      (gamma' i S g (CompKeyInversion.rnd d 32)).shape → c = d := fun {c d} h =>
    randTerm32_injective (Symbolic.Swarm.CREF.TR.G1.Spine.eq_randTerm32_of_shape_eq i S g c h)
  rcases dh_cases_c X (CompKeyInversion.rnd a 32) with ⟨hvX, hX⟩ | ⟨skX, rfl, hX⟩ <;>
    rcases dh_cases_c Y (CompKeyInversion.rnd b 32) with ⟨hvY, hY⟩ | ⟨skY, rfl, hY⟩
  ·
    rw [hX, hY] at hsh
    exact .inr (hrig (shape_dh_pack_inj i S g hsh).2)
  ·
    rw [hX, hY] at hsh
    split_ifs at hsh with h
    · exact .inr (hrig (shape_dh_pack_inj i S g hsh).2)
    · have hp := (shape_dh_pack_inj i S g hsh).1
      have := eq_dhPk_randTerm32_of_shape_eq i S g b hp.symm
      subst this
      rw [bobTwin_view_dhPk] at hvX
      cases hvX
  ·
    rw [hX, hY] at hsh
    split_ifs at hsh with h
    · exact .inr (hrig (shape_dh_pack_inj i S g hsh).2)
    · have hp := (shape_dh_pack_inj i S g hsh).1
      have := eq_dhPk_randTerm32_of_shape_eq i S g a hp
      subst this
      rw [bobTwin_view_dhPk] at hvY
      cases hvY
  ·
    rw [hX, hY] at hsh ⊢
    split_ifs at hsh ⊢ with h₁ h₂
    · exact .inr (hrig (shape_dh_pack_inj i S g hsh).2)
    · obtain ⟨hp, hs⟩ := shape_dh_pack_inj i S g hsh
      have e₁ := dhPk_injective (eq_dhPk_randTerm32_of_shape_eq i S g b hp.symm)
      have e₂ := Symbolic.Swarm.CREF.TR.G1.Spine.eq_randTerm32_of_shape_eq i S g a hs
      subst e₁ e₂
      exact .inl rfl
    · obtain ⟨hp, hs⟩ := shape_dh_pack_inj i S g hsh
      have e₁ := dhPk_injective (eq_dhPk_randTerm32_of_shape_eq i S g a hp)
      have e₂ := Symbolic.Swarm.CREF.TR.G1.Spine.eq_randTerm32_of_shape_eq i S g b hs.symm
      subst e₁ e₂
      exact .inl rfl
    · have hp := (shape_dh_pack_inj i S g hsh).1
      exact .inr (randTerm32_injective (dhPk_injective (eq_dhPk_randTerm32_of_shape_eq i S g a hp)))

private theorem bobTwin_agree_slot {X Y : DY.Bytes} {a b : Nat}
    (hsh : (gamma' i S g (DY.Libsignal.PQXDH.agree X (CompKeyInversion.rnd a 32))).shape =
      (gamma' i S g (DY.Libsignal.PQXDH.agree Y (CompKeyInversion.rnd b 32))).shape) :
    DY.Libsignal.PQXDH.agree X (CompKeyInversion.rnd a 32) =
      DY.Libsignal.PQXDH.agree Y (CompKeyInversion.rnd b 32) ∨ a = b :=
  bobTwin_dh_slot i S g hsh

/-! ## Alice/Bob twins -/

/-- On a reachable trace satisfying `AliceKemLen32`, an `AliceDone` key bundle and a `BobDone` key
bundle whose root keys have equal `gamma'` shapes have equal root keys unless `KemSlotAlias` holds. -/
theorem aliceBobTwin_of_reachable {T : ExecTrace} (hT : ReachableTrace T)
    (hKem32 : AliceKemLen32 i S g T) :
    ∀ {k₁ k₂ : HandshakeKeys} {t₁ t₂ : DY.Bytes}, AliceDoneKeys T k₁ → BobDoneKeys T k₂ →
      (∀ e ∈ (gamma' i S g k₁.rk).memo, e ∈ (gamma' i S g t₁).memo) →
      (∀ e ∈ (gamma' i S g k₂.rk).memo, e ∈ (gamma' i S g t₂).memo) →
      (gamma' i S g k₁.rk).shape = (gamma' i S g k₂.rk).shape →
      k₁.rk = k₂.rk := by
  intro k₁ k₂ t₁ t₂ h₁ h₂ _hm₁ _hm₂ hsh
  obtain ⟨a₁, b₁, ikA₁, ikB₁, spk₁, pq₁, opk₁, ek₁, ct₁, j₁, hev₁⟩ := h₁
  obtain ⟨b₂, a₂, ikB₂, ikA₂, spk₂, pq₂, opk₂, ek₂, ct₂, j₂, hev₂⟩ := h₂
  have hinv : SpqrInv T := spqrInv_of_reachable _ hT
  obtain ⟨u, sA, rfl, hslot, hikA, -, -, hag, -⟩ :=
    hinv.aliceDone _ _ _ _ _ _ _ _ _ _ _ hev₁
  obtain ⟨sB, sS, sQ, o, e, hikB, -, hspk, -, -, -, hopk, -, -, he_eq, hk₂, -⟩ :=
    hinv.bobDone _ _ _ _ _ _ _ _ _ _ _ hev₂
  have hk₁ := bobTwin_keys_of_aliceAgreement hag
  have h32 : (gamma i S g (randTerm (u + 1) 32)).length = 32 :=
    hKem32 u a₁ b₁ ikA₁ ikB₁ spk₁ pq₁ opk₁ ek₁ ct₁ k₁ hev₁
  subst hk₁ hk₂
  have hikm := bobTwin_ikm_shape i S g hsh
  have he_leaf : ShapeModKem.KemLeaf e := by
    subst he_eq
    rcases hdec : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap sQ ct₂) with _ | s
    · exact .inr ⟨sQ, ct₂, rfl⟩
    · obtain ⟨e₀, _, rfl⟩ := Stage1Kyber.errToOption_kemDecap_eq_some_iff.mp hdec
      exact .inl ⟨_, e₀, rfl⟩
  have hss := bobTwin_ss_shape i S g (.inl ⟨_, _, rfl⟩) he_leaf hikm
  have hdec : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap sQ ct₂) = some e := by
    rcases hd : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap sQ ct₂) with _ | s
    · exfalso
      have he_rej : e = DY.PQKem.kemRejKey sQ ct₂ := by rw [hd] at he_eq; exact he_eq
      rw [he_rej] at hss
      obtain ⟨pk', e', heq, _⟩ := Stage1Kyber.eq_kemSS_of_shape_eq_kemSS_len32 i S g h32 hss.symm
      have hnone := (Stage1Kyber.view?_kemRejKey_disjoint sQ ct₂).2.2.2.2.2.2.2.2.2.1
      rw [heq, Stage1Kyber.kemEncap_snd_eq_pack, Stage1Kyber.view_kemSS_pack] at hnone
      cases hnone
    · rw [hd] at he_eq
      exact he_eq ▸ rfl
  obtain ⟨e₀, hct₂, rfl⟩ := Stage1Kyber.errToOption_kemDecap_eq_some_iff.mp hdec
  obtain ⟨pk', e₀', hu_eq, _, _, he_sh⟩ :=
    Stage1Kyber.eq_kemSS_of_shape_eq_kemSS_len32 i S g h32 hss.symm
  obtain ⟨_, rfl⟩ := Stage1Kyber.kemEncap_snd_inj hu_eq
  have hsz : (32 : Nat) ≠ 0 := by decide
  rw [(Stage1Kyber.shape_eq_randTerm_iff i S g (randTerm (u + 1) 32) hsz).mpr rfl] at he_sh
  have he₀_eq : e₀ = randTerm (u + 1) 32 :=
    (Stage1Kyber.shape_eq_randTerm_iff i S g e₀ hsz).mp he_sh
  subst he₀_eq
  have hct₂_ak : ct₂.AttackerKnows T :=
    (bobDone_ct_pqpk_attackerKnows_of_reachable hT hev₂).1
  rw [hct₂] at hct₂_ak
  have heq : (DY.PQKem.kemEncap pq₁ (CompKeyInversion.rnd (u + 1) 32)).2 =
      (DY.PQKem.kemEncap (DY.PQKem.kemPk sQ) (randTerm (u + 1) 32)).2 := by
    rcases kemEncap_fst_attackerKnows_inv hT hct₂_ak with hkCoin |
        ⟨t', a', b', ikA', ikB', spk', pqpk', opk', ek', ct', keys', hev', hpqEq, hrndEq⟩
    · exact absurd hkCoin (aliceDone_kemCoin_not_attackerKnows hT hev₁)
    · have ht : u = t' := by
        have h1 := (Stage1Kyber.randTerm_inj hrndEq).1
        omega
      subst ht
      have hevEq := CompInv.CompPresBob.evAt_unique hev₁ hev'
      injection hevEq with _ _ _ _ _ hpq₁ _ _ _ _
      rw [hpqEq, ← hpq₁]
      rfl
  unfold pqxdhIkm at hikm
  have hc1 := (shape_concat_inj i S g hikm).2
  have hdh1 := (shape_concat_inj i S g hc1).1
  have hc2 := (shape_concat_inj i S g hc1).2
  have hdh2 := (shape_concat_inj i S g hc2).1
  have hc3 := (shape_concat_inj i S g hc2).2
  have hdh3 := (shape_concat_inj i S g hc3).1
  have htail := (shape_concat_inj i S g hc3).2
  obtain ⟨tA, rfl, -, hirA⟩ := hikA
  obtain ⟨tB, rfl, -, hirB⟩ := hikB
  obtain ⟨tS, rfl, -, hrS1, -⟩ := hspk
  obtain ⟨-, hr1, -, -⟩ := hslot
  -- DH1: `agree spk sA` vs `agree ikA sS` (identity vs signed-prekey secret).
  have e1 : DY.Libsignal.PQXDH.agree spk₁ (CompKeyInversion.rnd tA 32) =
      DY.Libsignal.PQXDH.agree ikA₂ (CompKeyInversion.rnd tS 32) := by
    rcases bobTwin_agree_slot i S g hdh1 with h | h
    · exact h
    · subst h
      exact (CompInv.CompPresBob.randAt_not_evAt hrS1 hirA).elim
  -- DH2: `agree ikB ek` vs `agree ek₂ sB` (base key vs identity secret).
  have e2 : DY.Libsignal.PQXDH.agree ikB₁ (CompKeyInversion.rnd u 32) =
      DY.Libsignal.PQXDH.agree ek₂ (CompKeyInversion.rnd tB 32) := by
    rcases bobTwin_agree_slot i S g hdh2 with h | h
    · exact h
    · subst h
      exact (CompInv.CompPresBob.randAt_not_evAt hr1 hirB).elim
  -- DH3: `agree spk ek` vs `agree ek₂ sS` (base key vs signed-prekey secret).
  have e3 : DY.Libsignal.PQXDH.agree spk₁ (CompKeyInversion.rnd u 32) =
      DY.Libsignal.PQXDH.agree ek₂ (CompKeyInversion.rnd tS 32) := by
    rcases bobTwin_agree_slot i S g hdh3 with h | h
    · exact h
    · subst h
      exact absurd (CompInv.CompPresBob.randAt_unique hr1 hrS1) (by decide)
  -- DH4 (optional `opk`): base key vs one-time-prekey secret; a KEM leaf is never a `concat`.
  have e4 : opk₁.map (DY.Libsignal.PQXDH.agree · (CompKeyInversion.rnd u 32)) =
      o.map (DY.Libsignal.PQXDH.agree ek₂ ·) := by
    rcases opk₁ with _ | y <;> rcases o with _ | x <;>
      simp only [Option.map_none, Option.map_some] at htail ⊢
    · exact absurd htail (ShapeModKem.shape_kemLeaf_ne_concat i S g (.inl ⟨_, _, rfl⟩))
    · exact absurd htail.symm (ShapeModKem.shape_kemLeaf_ne_concat i S g (.inl ⟨_, _, rfl⟩))
    · obtain ⟨tO, rfl, -, hirO⟩ := hopk x rfl
      rcases bobTwin_agree_slot i S g (shape_concat_inj i S g htail).1 with h | h
      · exact congrArg some h
      · subst h
        exact (CompInv.CompPresBob.randAt_not_evAt hr1 hirO).elim
  rw [e1, e2, e3, e4, heq]

end Symbolic.Swarm.CREF.TR.G1.Spine
