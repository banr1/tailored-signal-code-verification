/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkSeedSepDefs
import all Init.Data.String.Defs
public import Symbolic.Proofs.Swarm.COMPOSED.CompClosed
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.RatchetDHRkSwapPeelTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkHist
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkPairUniq
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac

/-!
# Root-Key Shape Twin Elimination

Proves `rkTwinStored` and `rkTwin`: any two stored root keys with equal shapes are equal, and a
stored root key with the same shape as an honest intermediate root node (`RkInter`) is equal to it
whenever Alice/Bob PQXDH root twins are ruled out (`AliceBobTwin`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Libsignal.TripleRatchet Symbolic.Swarm.CREF.TR
open DY.Libsignal.TripleRatchet (createChain lit)
open DY.Libsignal.PQXDH (HandshakeKeys pqxdhKdf pqxdhLabel)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompInv (spqrInv_of_reachable)
open Symbolic.Swarm.CREF.TR.RecvDecStep (shape_kdfExtract_tr)

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

theorem rkTwin_shape_createChain_fst_inj {r₁ k₁ s₁ r₂ k₂ s₂ : DY.Bytes}
    (h : (gamma' i S g (createChain r₁ k₁ s₁).1).shape =
      (gamma' i S g (createChain r₂ k₂ s₂).1).shape) :
    (gamma' i S g r₁).shape = (gamma' i S g r₂).shape ∧
    (gamma' i S g (DiffieHellman.dh (X25519.normalizeX25519Key k₁) s₁)).shape =
      (gamma' i S g (DiffieHellman.dh (X25519.normalizeX25519Key k₂) s₂)).shape :=
  ShapeModKem.shape_kdfExtract_inj i S g (ShapeModKem.shape_kdfExtract_inj i S g h).1

theorem rkTwin_saltDepth_kdfExtract (s m : DY.Bytes) :
    CompRatchet.saltDepth (gamma' i S g (KdfExtract.kdfExtract s m)).shape =
      CompRatchet.saltDepth (gamma' i S g s).shape + 1 := by
  rw [shape_kdfExtract_tr]
  exact CompRatchet.saltDepth_kdfExtract _ _

theorem rkTwin_shape_createChain_fst_ne_self (r k s : DY.Bytes) :
    (gamma' i S g r).shape ≠ (gamma' i S g (createChain r k s).1).shape := by
  intro h
  obtain ⟨m, hm⟩ : ∃ m, (createChain r k s).1 =
      KdfExtract.kdfExtract (KdfExtract.kdfExtract r (DiffieHellman.dh (X25519.normalizeX25519Key k) s)) m :=
    ⟨_, rfl⟩
  have h3 := congrArg CompRatchet.saltDepth h
  rw [hm, rkTwin_saltDepth_kdfExtract, rkTwin_saltDepth_kdfExtract] at h3
  omega

theorem rkTwin_shape_literal (b : ByteArray) :
    (gamma' i S g (Literal.literalToBytes b)).shape = Literal.literalToBytes b := by
  unfold gamma'; show ((({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll i S g)]; rfl

theorem rkTwin_pqxdhLabel_ne_whisperRatchet : pqxdhLabel ≠ lit "WhisperRatchet" := by
  intro h
  have h1 : pqxdhLabel.length = 46 := by
    unfold pqxdhLabel lit; rw [Literal.length_literalToBytes]; rfl
  have h2 : (lit "WhisperRatchet").length = 14 := by
    unfold lit; rw [Literal.length_literalToBytes]; rfl
  rw [h, h2] at h1; cases h1

theorem rkTwin_shape_pqxdh_rk_ne_createChain (ikm r k s : DY.Bytes) :
    (gamma' i S g (pqxdhKdf ikm).rk).shape ≠ (gamma' i S g (createChain r k s).1).shape := by
  intro h
  have h1 := (ShapeModKem.shape_kdfExtract_inj i S g h).2
  have h2 := (ShapeModKem.shape_concat_inj i S g h1).1
  unfold pqxdhLabel lit at h2
  rw [rkTwin_shape_literal, rkTwin_shape_literal] at h2
  exact rkTwin_pqxdhLabel_ne_whisperRatchet h2

theorem rkTwin_dh_rand_shape_split {k₁ k₂ : DY.Bytes} {t₁ t₂ : Nat}
    (h : (gamma' i S g (DiffieHellman.dh k₁ (randTerm t₁ 32))).shape =
      (gamma' i S g (DiffieHellman.dh k₂ (randTerm t₂ 32))).shape) :
    t₁ = t₂ ∨ (k₁ = dhPk (randTerm t₂ 32) ∧ k₂ = dhPk (randTerm t₁ 32)) := by
  rcases notRandDhPkShape_or_eq_dhPk_randTerm32 i S g k₂ with hnr | ⟨t_m, rfl⟩
  · exact .inl (dh_shape_eq_of_notRandDhPkShape i S g hnr h).2
  · obtain ⟨-, heq⟩ := dh_eq_of_shape_eq_dh_dhPk_randTerm32 i S g h
    rcases CompTermAlgebra.dh_eq_dh_dhPk_cases heq with ⟨_, h2⟩ | ⟨h1, h2⟩
    · exact .inl (randTerm_timestamp_inj h2)
    · have ht : t₁ = t_m := randTerm_timestamp_inj h2
      exact .inr ⟨h1, by rw [ht]⟩

theorem rkTwin_memo_createChain_fst {r k s t : DY.Bytes}
    (hm : ∀ e ∈ (gamma' i S g (createChain r k s).1).memo, e ∈ (gamma' i S g t).memo) :
    ∀ e ∈ (gamma' i S g r).memo, e ∈ (gamma' i S g t).memo :=
  fun e he => hm e (memo_mem_of_kdfExtract_left i S g _ _
    (memo_mem_of_kdfExtract_left i S g r (DiffieHellman.dh (X25519.normalizeX25519Key k) s) he))

theorem rkTwin_createChain_fst_cross_eq {y k₁ k₂ a b : DY.Bytes}
    (h₁ : X25519.normalizeX25519Key k₁ = dhPk b) (h₂ : X25519.normalizeX25519Key k₂ = dhPk a) :
    (createChain y k₁ a).1 = (createChain y k₂ b).1 := by
  unfold createChain DY.X25519.agree
  rw [h₁, h₂, DiffieHellman.dh_commutes]

theorem rkTwin_aliceDoneKeys_pqxdh {T : ExecTrace} (hT : ReachableTrace T) {keys : HandshakeKeys}
    (h : AliceDoneKeys T keys) : ∃ ikm, keys = pqxdhKdf ikm := by
  obtain ⟨a, b, ikA, ikB, spk, pq, opk, ek, ct, j, hev⟩ := h
  obtain ⟨u, sA, rfl, -, -, -, -, hag, -⟩ := (spqrInv_of_reachable _ hT).aliceDone _ _ _ _ _ _ _ _ _ _ _ hev
  rcases hk : DY.PQKem.kemEncap pq (CompKeyInversion.rnd (u + 1) 32) with ⟨c₀, s₀⟩
  unfold DY.Libsignal.PQXDH.aliceAgreement at hag
  rw [hk] at hag
  simp only [Prod.mk.injEq] at hag
  exact ⟨_, hag.2⟩

theorem rkTwin_bobDoneKeys_pqxdh {T : ExecTrace} (hT : ReachableTrace T) {keys : HandshakeKeys}
    (h : BobDoneKeys T keys) : ∃ ikm, keys = pqxdhKdf ikm := by
  obtain ⟨b, a, ikB, ikA, spk, pq, opk, ek, ct, j, hev⟩ := h
  obtain ⟨_sB, _sS, _sQ, _o, _e, -, -, -, -, -, -, -, -, -, -, hk, -⟩ :=
    (spqrInv_of_reachable _ hT).bobDone _ _ _ _ _ _ _ _ _ _ _ hev
  exact ⟨_, hk⟩

theorem rkTwin_stored_parent {T : ExecTrace} (hT : ReachableTrace T)
    {p : Participant} {st : TRState} {i₀ : Nat} (h : TRStateStoredAt p st i₀ T) :
    ∃ s, st.dhs = randTerm s 32 ∧ ∃ y k, st.rk = (createChain y k (randTerm s 32)).1 ∧
      (RkInter T k y ∨ ∃ keys, AliceDoneKeys T keys ∧ y = keys.rk) := by
  obtain ⟨s, -, hdhs, -⟩ := trStateStoredAt_rk_createChain hT h
  refine ⟨s, hdhs, ?_⟩
  rcases rkHist_of_stored hT h with
    (⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, j, hev, heq⟩ |
      ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, keys, j, t, idx, pk, hev, hspk, heq⟩) |
    ⟨p', st', i', pk, -, hst', heq⟩
  · exact ⟨keys.rk, spk, by rw [heq, hdhs],
      .inr ⟨keys, ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, j, hev⟩, rfl⟩⟩
  · exact ⟨(createChain keys.rk pk (randTerm t 32)).1, pk, by rw [heq, hdhs],
      .inl (.inr ⟨keys, t, b, idx, ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, j, hev⟩, hspk, rfl⟩)⟩
  · exact ⟨(createChain st'.rk pk st'.dhs).1, pk, by rw [heq, hdhs],
      .inl (.inl ⟨p', st', i', hst', rfl⟩)⟩

theorem rkTwin_rkInter_parent {T : ExecTrace} (hT : ReachableTrace T) {pk x : DY.Bytes}
    (h : RkInter T pk x) :
    ∃ s r, x = (createChain r pk (randTerm s 32)).1 ∧
      ((∃ (p : Participant) (st : TRState) (i₀ : Nat), TRStateStoredAt p st i₀ T ∧
          st.dhs = randTerm s 32 ∧ r = st.rk) ∨
        (∃ (keys : HandshakeKeys) (b : Participant) (idx : Nat), BobDoneKeys T keys ∧
          CompTrace.PQXDHStoredAt T b { kind := .signedPrekey, sk := randTerm s 32 } idx ∧
          r = keys.rk)) := by
  rcases h with ⟨p, st, i₀, hst, rfl⟩ | ⟨keys, t, b, idx, hk, hspk, rfl⟩
  · obtain ⟨s, -, hdhs, -⟩ := trStateStoredAt_rk_createChain hT hst
    exact ⟨s, st.rk, by rw [hdhs], .inl ⟨p, st, i₀, hst, hdhs, rfl⟩⟩
  · exact ⟨t, keys.rk, rfl, .inr ⟨keys, b, idx, hk, hspk, rfl⟩⟩

theorem rkTwinStored {T : ExecTrace} (hT : ReachableTrace T) : RkTwinStoredStmt i S g T := by
  intro p₁ p₂ st₁ st₂ i₁ i₂ t₁ t₂ h₁ h₂ _ _ hsh
  obtain ⟨a, -, hdhs₁, r₁, k₁, hlt₁, hrk₁⟩ := trStateStoredAt_rk_createChain hT h₁
  obtain ⟨b, -, hdhs₂, r₂, k₂, hlt₂, hrk₂⟩ := trStateStoredAt_rk_createChain hT h₂
  rw [hrk₁, hrk₂] at hsh
  rcases rkTwin_dh_rand_shape_split i S g (rkTwin_shape_createChain_fst_inj i S g hsh).2 with
    hab | ⟨hk₁, hk₂⟩
  · subst hab
    exact stored_rk_eq_of_dhs_eq hT h₁ h₂ (hdhs₁.trans hdhs₂.symm)
  · have := hlt₁ b hk₁
    have := hlt₂ a hk₂
    omega

theorem rkTwin_core {T : ExecTrace} (hT : ReachableTrace T) (hAB : AliceBobTwin i S g T) (n : Nat) :
    ∀ {p₁ : Participant} {st₁ : TRState} {i₁ s₁ : Nat} {pk x t₁ t₂ : DY.Bytes},
      st₁.dhs = randTerm s₁ 32 → s₁ < n →
      TRStateStoredAt p₁ st₁ i₁ T → RkInter T pk x →
      (∀ e ∈ (gamma' i S g st₁.rk).memo, e ∈ (gamma' i S g t₁).memo) →
      (∀ e ∈ (gamma' i S g x).memo, e ∈ (gamma' i S g t₂).memo) →
      (gamma' i S g st₁.rk).shape = (gamma' i S g x).shape →
      st₁.rk = x := by
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro p₁ st₁ i₁ s₁ pk x t₁ t₂ hs₁ hlt h₁ hx hm₁ hm₂ hsh
    obtain ⟨s₁', hdhs₁, y, k, hrk₁, hy⟩ := rkTwin_stored_parent hT h₁
    have hss : s₁' = s₁ := randTerm_timestamp_inj (hdhs₁.symm.trans hs₁)
    rw [hss] at hdhs₁ hrk₁
    obtain ⟨s₀, r₀, rfl, hr₀⟩ := rkTwin_rkInter_parent hT hx
    rw [hrk₁] at hsh hm₁ ⊢
    have hm₁' := rkTwin_memo_createChain_fst i S g hm₁
    have hm₂' := rkTwin_memo_createChain_fst i S g hm₂
    obtain ⟨hsh_r, hsh_dh⟩ := rkTwin_shape_createChain_fst_inj i S g hsh
    rcases rkTwin_dh_rand_shape_split i S g hsh_dh with hst | ⟨hk₁, hk₂⟩
    ·
      rw [← hst] at hr₀
      rcases hr₀ with ⟨p₀, st₀, i₀, h₀, hdhs₀, rfl⟩ | ⟨keys, b, idx, -, hspk, -⟩
      · have hrk := stored_rk_eq_of_dhs_eq hT h₁ h₀ (hdhs₁.trans hdhs₀.symm)
        rw [hrk₁] at hrk
        rw [← hrk] at hsh_r
        exact absurd hsh_r (rkTwin_shape_createChain_fst_ne_self i S g y k _)
      · exact absurd hdhs₁ (stored_dhs_ne_spkSk hT h₁ hspk)
    ·
      rcases hr₀ with ⟨p₀, st₀, i₀, h₀, hdhs₀, rfl⟩ | ⟨keysB, b, idx, hkB, hspk, rfl⟩
      · have hlt₀ : s₀ < s₁ := stored_peer_lt hT h₁ (rk1 := y) hdhs₁
          (by rw [hdhs₁]; exact hrk₁) hk₁
        rcases hy with hyI | ⟨keysA, hkA, rfl⟩
        · have heq := ih hdhs₀ (by omega) h₀ hyI hm₂' hm₁' hsh_r.symm
          rw [heq]; exact rkTwin_createChain_fst_cross_eq hk₁ hk₂
        · exfalso
          obtain ⟨ikm, rfl⟩ := rkTwin_aliceDoneKeys_pqxdh hT hkA
          obtain ⟨s₂, -, y₂, k₂, hrk₀, -⟩ := rkTwin_stored_parent hT h₀
          rw [hrk₀] at hsh_r
          exact rkTwin_shape_pqxdh_rk_ne_createChain i S g ikm _ _ _ hsh_r
      · rcases hy with hyI | ⟨keysA, hkA, rfl⟩
        · exfalso
          obtain ⟨ikm, rfl⟩ := rkTwin_bobDoneKeys_pqxdh hT hkB
          obtain ⟨s₂, r₂, rfl, -⟩ := rkTwin_rkInter_parent hT hyI
          exact rkTwin_shape_pqxdh_rk_ne_createChain i S g ikm _ _ _ hsh_r.symm
        · have heq := hAB hkA hkB hm₁' hm₂' hsh_r
          rw [heq]; exact rkTwin_createChain_fst_cross_eq hk₁ hk₂

theorem rkTwin {T : ExecTrace} (hT : ReachableTrace T) (hAB : AliceBobTwin i S g T) :
    RkTwinStmt i S g T := by
  intro p₁ st₁ i₁ pk x t₁ t₂ h₁ hx hm₁ hm₂ hsh
  obtain ⟨s, -, hdhs, -⟩ := trStateStoredAt_rk_createChain hT h₁
  exact rkTwin_core i S g hT hAB (s + 1) hdhs (Nat.lt_succ_self s) h₁ hx hm₁ hm₂ hsh

end Symbolic.Swarm.CREF.TR.G1.Spine
