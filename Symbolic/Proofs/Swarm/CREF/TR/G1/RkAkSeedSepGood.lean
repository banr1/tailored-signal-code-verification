/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkSeedSepDefs
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeel
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkHist
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac

/-!
# Spine Predicate `Good` and KDF Shape Algebra

Defines `GoodRk`, `GoodCk`, and `Good`, proves KDF injectivity and `gamma'`-shape commutation
lemmas for `hkdfBlock1`, `hkdfBlock2`, and `kdfCk`, and shows `spineDown_good : SpineDown (Good T)`
on reachable traces.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Libsignal.TripleRatchet Symbolic.Swarm.CREF.TR
open DY.Libsignal.TripleRatchet (createChain chainKeyAt kdfCk kdfRk hmac hkdfBlock1 hkdfBlock2 lit
  litByte zeroSalt)
open DY.Libsignal.PQXDH (HandshakeKeys pqxdhKdf pqxdhLabel)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompInv (spqrInv_of_reachable)
open Symbolic.Swarm.CREF.TR.RecvDecStep (shape_kdfExtract_tr shape_concat_tr)

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Term-level KDF algebra -/

/-- Chain-key output selector: the chain key itself (`false`) or its message seed (`true`). -/
def ckOut : Bool → DY.Bytes → DY.Bytes
  | false, x => x
  | true, x => (kdfCk x).2

theorem createChain_fst_eq (rk pk sk : DY.Bytes) : (createChain rk pk sk).1 =
    hkdfBlock1 (hmac rk (DiffieHellman.dh (X25519.normalizeX25519Key pk) sk)) (lit "WhisperRatchet") := rfl

theorem createChain_snd_eq (rk pk sk : DY.Bytes) : (createChain rk pk sk).2 =
    hkdfBlock2 (hmac rk (DiffieHellman.dh (X25519.normalizeX25519Key pk) sk)) (lit "WhisperRatchet") := rfl

theorem pqxdhKdf_rk_eq (ikm : DY.Bytes) :
    (pqxdhKdf ikm).rk = hkdfBlock1 (hmac zeroSalt ikm) pqxdhLabel := rfl

theorem pqxdhKdf_ck_eq (ikm : DY.Bytes) :
    (pqxdhKdf ikm).ck = hkdfBlock2 (hmac zeroSalt ikm) pqxdhLabel := rfl

theorem hmac_inj {k₁ m₁ k₂ m₂ : DY.Bytes} (h : hmac k₁ m₁ = hmac k₂ m₂) : k₁ = k₂ ∧ m₁ = m₂ :=
  kdfExtract_inj_rk h

theorem hkdfBlock1_inj {p₁ l₁ p₂ l₂ : DY.Bytes} (h : hkdfBlock1 p₁ l₁ = hkdfBlock1 p₂ l₂) :
    p₁ = p₂ ∧ l₁ = l₂ := by
  have h' : KdfExtract.kdfExtract p₁ (Concat.concat l₁ (litByte 1)) =
      KdfExtract.kdfExtract p₂ (Concat.concat l₂ (litByte 1)) := h
  exact ⟨(kdfExtract_inj_rk h').1, (concat_inj_rk (kdfExtract_inj_rk h').2).1⟩

theorem hkdfBlock2_inj {p₁ l₁ p₂ l₂ : DY.Bytes} (h : hkdfBlock2 p₁ l₁ = hkdfBlock2 p₂ l₂) :
    p₁ = p₂ ∧ l₁ = l₂ := by
  have h' : KdfExtract.kdfExtract p₁ (Concat.concat (hkdfBlock1 p₁ l₁) (Concat.concat l₁ (litByte 2))) =
      KdfExtract.kdfExtract p₂ (Concat.concat (hkdfBlock1 p₂ l₂) (Concat.concat l₂ (litByte 2))) := h
  exact ⟨(kdfExtract_inj_rk h').1,
    (concat_inj_rk (concat_inj_rk (kdfExtract_inj_rk h').2).2).1⟩

theorem litByte_two_ne_one : litByte 2 ≠ litByte 1 := by
  intro h
  have h1 := congrArg (fun b : ByteArray => b.data[0]!) (literalToBytes_inj h)
  revert h1
  decide

theorem hkdfBlock2_ne_hkdfBlock1 (p₁ l₁ p₂ l₂ : DY.Bytes) : hkdfBlock2 p₁ l₁ ≠ hkdfBlock1 p₂ l₂ := by
  intro h
  have h' : KdfExtract.kdfExtract p₁ (Concat.concat (hkdfBlock1 p₁ l₁) (Concat.concat l₁ (litByte 2))) =
      KdfExtract.kdfExtract p₂ (Concat.concat l₂ (litByte 1)) := h
  exact concat_ne_literal_rk _ _ _ (concat_inj_rk (kdfExtract_inj_rk h').2).2

theorem kdfCk_fst_ne_hkdfBlock1 (ck p l : DY.Bytes) : (kdfCk ck).1 ≠ hkdfBlock1 p l := by
  intro h
  have h' : KdfExtract.kdfExtract ck (litByte 2) =
      KdfExtract.kdfExtract p (Concat.concat l (litByte 1)) := h
  exact concat_ne_literal_rk _ _ _ (kdfExtract_inj_rk h').2.symm

theorem kdfCk_snd_ne_hkdfBlock1 (ck p l : DY.Bytes) : (kdfCk ck).2 ≠ hkdfBlock1 p l := by
  intro h
  have h' : KdfExtract.kdfExtract ck (litByte 1) =
      KdfExtract.kdfExtract p (Concat.concat l (litByte 1)) := h
  exact concat_ne_literal_rk _ _ _ (kdfExtract_inj_rk h').2.symm

theorem kdfCk_fst_ne_hkdfBlock2 (ck p l : DY.Bytes) : (kdfCk ck).1 ≠ hkdfBlock2 p l := by
  intro h
  have h' : KdfExtract.kdfExtract ck (litByte 2) =
      KdfExtract.kdfExtract p (Concat.concat (hkdfBlock1 p l) (Concat.concat l (litByte 2))) := h
  exact concat_ne_literal_rk _ _ _ (kdfExtract_inj_rk h').2.symm

theorem kdfCk_snd_ne_hkdfBlock2 (ck p l : DY.Bytes) : (kdfCk ck).2 ≠ hkdfBlock2 p l := by
  intro h
  have h' : KdfExtract.kdfExtract ck (litByte 1) =
      KdfExtract.kdfExtract p (Concat.concat (hkdfBlock1 p l) (Concat.concat l (litByte 2))) := h
  exact concat_ne_literal_rk _ _ _ (kdfExtract_inj_rk h').2.symm

theorem kdfCk_fst_ne_snd (a b : DY.Bytes) : (kdfCk a).1 ≠ (kdfCk b).2 := by
  intro h
  have h' : KdfExtract.kdfExtract a (litByte 2) = KdfExtract.kdfExtract b (litByte 1) := h
  exact litByte_two_ne_one (kdfExtract_inj_rk h').2

theorem kdfCk_fst_inj {a b : DY.Bytes} (h : (kdfCk a).1 = (kdfCk b).1) : a = b :=
  (kdfExtract_inj_rk (show KdfExtract.kdfExtract a (litByte 2) =
    KdfExtract.kdfExtract b (litByte 2) from h)).1

theorem kdfCk_snd_inj {a b : DY.Bytes} (h : (kdfCk a).2 = (kdfCk b).2) : a = b :=
  (kdfExtract_inj_rk (show KdfExtract.kdfExtract a (litByte 1) =
    KdfExtract.kdfExtract b (litByte 1) from h)).1

/-- A chain-key output over an `hkdfBlock2` root is never an `hkdfBlock1` (root-key) node. -/
theorem ckOut_ne_hkdfBlock1 (b : Bool) (p l p' l' : DY.Bytes) :
    ∀ j, ckOut b (chainKeyAt (hkdfBlock2 p l) j) ≠ hkdfBlock1 p' l' := by
  intro j
  cases b with
  | true => exact kdfCk_snd_ne_hkdfBlock1 _ _ _
  | false =>
    cases j with
    | zero => exact hkdfBlock2_ne_hkdfBlock1 p l p' l'
    | succ j =>
      show chainKeyAt (hkdfBlock2 p l) (j + 1) ≠ _
      rw [chainKeyAt_succ_eq_kdfCk_fst]
      exact kdfCk_fst_ne_hkdfBlock1 _ _ _

/-- Two chain-key outputs over `hkdfBlock2` roots are equal only when their output selectors, step
indices, and roots are equal. -/
theorem ckOut_align {p₁ l₁ p₂ l₂ : DY.Bytes} {b₁ b₂ : Bool} {j₁ j₂ : Nat}
    (h : ckOut b₁ (chainKeyAt (hkdfBlock2 p₁ l₁) j₁) = ckOut b₂ (chainKeyAt (hkdfBlock2 p₂ l₂) j₂)) :
    b₁ = b₂ ∧ j₁ = j₂ ∧ hkdfBlock2 p₁ l₁ = hkdfBlock2 p₂ l₂ := by
  have base : ∀ {k₁ k₂ : Nat}, chainKeyAt (hkdfBlock2 p₁ l₁) k₁ = chainKeyAt (hkdfBlock2 p₂ l₂) k₂ →
      k₁ = k₂ ∧ hkdfBlock2 p₁ l₁ = hkdfBlock2 p₂ l₂ := fun {k₁ k₂} hk => by
    have := chainKeyAt_concat_base_inj (s₁ := p₁) (s₂ := p₂) k₁ k₂ hk
    exact ⟨this.2, this.1⟩
  have mixed : ∀ {k₁ k₂ : Nat} {pa la pb lb : DY.Bytes},
      chainKeyAt (hkdfBlock2 pa la) k₁ ≠ (kdfCk (chainKeyAt (hkdfBlock2 pb lb) k₂)).2 :=
    fun {k₁ k₂ pa la pb lb} hk => by
      cases k₁ with
      | zero => exact kdfCk_snd_ne_hkdfBlock2 _ _ _ hk.symm
      | succ k =>
        rw [chainKeyAt_succ_eq_kdfCk_fst] at hk
        exact kdfCk_fst_ne_snd _ _ hk
  cases b₁ <;> cases b₂
  · obtain ⟨hj, hr⟩ := base h; exact ⟨rfl, hj, hr⟩
  · exact absurd h mixed
  · exact absurd h.symm mixed
  · obtain ⟨hj, hr⟩ := base (kdfCk_snd_inj h); exact ⟨rfl, hj, hr⟩

/-! ## Shapes commute with KDF symbols -/

section Shapes

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

theorem shape_litByte (b : UInt8) : (gamma' i S g (litByte b)).shape = litByte b :=
  shape_literalToBytes i S g _

theorem shape_lit (s : String) : (gamma' i S g (lit s)).shape = lit s :=
  shape_literalToBytes i S g _

theorem shape_pqxdhLabel : (gamma' i S g pqxdhLabel).shape = pqxdhLabel :=
  shape_literalToBytes i S g _

theorem shape_hkdfBlock1 (p l : DY.Bytes) :
    (gamma' i S g (hkdfBlock1 p l)).shape = hkdfBlock1 (gamma' i S g p).shape (gamma' i S g l).shape := by
  show (gamma' i S g (KdfExtract.kdfExtract p (Concat.concat l (litByte 1)))).shape =
    KdfExtract.kdfExtract (gamma' i S g p).shape (Concat.concat (gamma' i S g l).shape (litByte 1))
  rw [shape_kdfExtract_tr, shape_concat_tr, shape_litByte]

theorem shape_hkdfBlock2 (p l : DY.Bytes) :
    (gamma' i S g (hkdfBlock2 p l)).shape = hkdfBlock2 (gamma' i S g p).shape (gamma' i S g l).shape := by
  show (gamma' i S g (KdfExtract.kdfExtract p
      (Concat.concat (hkdfBlock1 p l) (Concat.concat l (litByte 2))))).shape =
    KdfExtract.kdfExtract (gamma' i S g p).shape
      (Concat.concat (hkdfBlock1 (gamma' i S g p).shape (gamma' i S g l).shape)
        (Concat.concat (gamma' i S g l).shape (litByte 2)))
  rw [shape_kdfExtract_tr, shape_concat_tr, shape_hkdfBlock1, shape_concat_tr, shape_litByte]

theorem shape_kdfCk_fst (ck : DY.Bytes) :
    (gamma' i S g (kdfCk ck).1).shape = (kdfCk (gamma' i S g ck).shape).1 := by
  show (gamma' i S g (KdfExtract.kdfExtract ck (litByte 2))).shape =
    KdfExtract.kdfExtract (gamma' i S g ck).shape (litByte 2)
  rw [shape_kdfExtract_tr, shape_litByte]

theorem shape_kdfCk_snd (ck : DY.Bytes) :
    (gamma' i S g (kdfCk ck).2).shape = (kdfCk (gamma' i S g ck).shape).2 := by
  show (gamma' i S g (KdfExtract.kdfExtract ck (litByte 1))).shape =
    KdfExtract.kdfExtract (gamma' i S g ck).shape (litByte 1)
  rw [shape_kdfExtract_tr, shape_litByte]

theorem shape_chainKeyAt (ck : DY.Bytes) :
    ∀ j, (gamma' i S g (chainKeyAt ck j)).shape = chainKeyAt (gamma' i S g ck).shape j
  | 0 => rfl
  | j + 1 => by
    rw [chainKeyAt_succ_eq_kdfCk_fst, chainKeyAt_succ_eq_kdfCk_fst, shape_kdfCk_fst,
      shape_chainKeyAt ck j]

theorem shape_ckOut (b : Bool) (x : DY.Bytes) :
    (gamma' i S g (ckOut b x)).shape = ckOut b (gamma' i S g x).shape := by
  cases b
  · rfl
  · exact shape_kdfCk_snd i S g x

theorem shape_ckOut_chainKeyAt_hkdfBlock2 (b : Bool) (p l : DY.Bytes) (j : Nat) :
    (gamma' i S g (ckOut b (chainKeyAt (hkdfBlock2 p l) j))).shape =
      ckOut b (chainKeyAt (hkdfBlock2 (gamma' i S g p).shape (gamma' i S g l).shape) j) := by
  rw [shape_ckOut, shape_chainKeyAt, shape_hkdfBlock2]

theorem memo_ckOut {X : DY.Bytes} (b : Bool) (j : Nat) {e : DY.Bytes × DY.Bytes × HwBytes}
    (he : e ∈ (gamma' i S g X).memo) : e ∈ (gamma' i S g (ckOut b (chainKeyAt X j))).memo := by
  cases b
  · exact memo_mem_of_chainKeyAt i S g he j
  · exact memo_mem_of_kdfCk_snd i S g _ (memo_mem_of_chainKeyAt i S g he j)

theorem memo_hkdfBlock1_hkdfBlock2 (p l : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (he : e ∈ (gamma' i S g (hkdfBlock1 p l)).memo) : e ∈ (gamma' i S g (hkdfBlock2 p l)).memo :=
  memo_mem_of_hmac_right i S g p _ (memo_mem_of_concat_left i S g _ _ he)

end Shapes

/-! ## Handshake key bundles -/

private theorem rkGood_keys_of_aliceAgreement {ikA ek ikB spk pq e ct : DY.Bytes}
    {opk : Option DY.Bytes} {keys : HandshakeKeys}
    (h : (ct, keys) = DY.Libsignal.PQXDH.aliceAgreement ikA ek ikB spk pq opk e) :
    ∃ ikm, keys = pqxdhKdf ikm := by
  rcases hk : DY.PQKem.kemEncap pq e with ⟨c₀, s₀⟩
  unfold DY.Libsignal.PQXDH.aliceAgreement at h
  rw [hk] at h
  simp only [Prod.mk.injEq] at h
  exact ⟨_, h.2⟩

theorem aliceDoneKeys_pqxdh {T : ExecTrace} (hT : ReachableTrace T) {keys : HandshakeKeys}
    (h : AliceDoneKeys T keys) : ∃ ikm, keys = pqxdhKdf ikm := by
  obtain ⟨a, b, ikA, ikB, spk, pq, opk, ek, ct, j, hev⟩ := h
  obtain ⟨u, sA, rfl, -, -, -, -, hag, -⟩ := (spqrInv_of_reachable _ hT).aliceDone _ _ _ _ _ _ _ _ _ _ _ hev
  exact rkGood_keys_of_aliceAgreement hag

theorem bobDoneKeys_pqxdh {T : ExecTrace} (hT : ReachableTrace T) {keys : HandshakeKeys}
    (h : BobDoneKeys T keys) : ∃ ikm, keys = pqxdhKdf ikm := by
  obtain ⟨b, a, ikB, ikA, spk, pq, opk, ek, ct, j, hev⟩ := h
  obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, -, -, -, hkeys, -⟩ :=
    (spqrInv_of_reachable _ hT).bobDone _ _ _ _ _ _ _ _ _ _ _ hev
  exact ⟨_, hkeys⟩

theorem doneKeys_pqxdh {T : ExecTrace} (hT : ReachableTrace T) {keys : HandshakeKeys}
    (h : AliceDoneKeys T keys ∨ BobDoneKeys T keys) : ∃ ikm, keys = pqxdhKdf ikm :=
  h.elim (aliceDoneKeys_pqxdh hT) (bobDoneKeys_pqxdh hT)

/-! ## `Good` predicate -/

/-- Honest root-key nodes: a stored root key, an intermediate root-key node, or a handshake `rk`. -/
def GoodRk (T : ExecTrace) (x : DY.Bytes) : Prop :=
  (∃ (p : Participant) (st : TRState) (i₀ : Nat), TRStateStoredAt p st i₀ T ∧ x = st.rk) ∨
  (∃ pk, RkInter T pk x) ∨
  (∃ keys : HandshakeKeys, (AliceDoneKeys T keys ∨ BobDoneKeys T keys) ∧ x = keys.rk)

/-- Chain keys and message seeds over an honest receive root. -/
def GoodCk (T : ExecTrace) (x : DY.Bytes) : Prop :=
  ∃ (pk R : DY.Bytes) (j : Nat) (b : Bool), RecvRoot T pk R ∧ x = ckOut b (chainKeyAt R j)

/-- Combined honest receive-chain and root-key spine predicate. -/
def Good (T : ExecTrace) (x : DY.Bytes) : Prop := GoodCk T x ∨ GoodRk T x

/-- Every stored root key is an `hkdfBlock1 _ "WhisperRatchet"` node. -/
theorem stored_rk_form {T : ExecTrace} (hT : ReachableTrace T) {p : Participant} {st : TRState}
    {i₀ : Nat} (hst : TRStateStoredAt p st i₀ T) :
    ∃ prk, st.rk = hkdfBlock1 prk (lit "WhisperRatchet") := by
  rcases rkHist_of_stored hT hst with
    (⟨_, _, _, _, _, _, _, _, _, _, _, _, hrk⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrk⟩) |
      ⟨_, _, _, _, _, _, hrk⟩
  all_goals exact ⟨_, hrk.trans (createChain_fst_eq _ _ _)⟩

/-- Every `GoodRk` node is an `hkdfBlock1` node, labelled `"WhisperRatchet"` unless it is a
handshake `rk` (labelled `pqxdhLabel`). -/
theorem goodRk_form {T : ExecTrace} (hT : ReachableTrace T) {x : DY.Bytes} (h : GoodRk T x) :
    ∃ prk, x = hkdfBlock1 prk (lit "WhisperRatchet") ∨ x = hkdfBlock1 prk pqxdhLabel := by
  rcases h with ⟨p, st, i₀, hst, rfl⟩ | ⟨pk, ⟨-, -, -, -, rfl⟩ | ⟨-, -, -, -, -, -, rfl⟩⟩ |
      ⟨keys, hk, rfl⟩
  · obtain ⟨prk, h⟩ := stored_rk_form hT hst; exact ⟨prk, .inl h⟩
  · exact ⟨_, .inl (createChain_fst_eq _ _ _)⟩
  · exact ⟨_, .inl (createChain_fst_eq _ _ _)⟩
  · obtain ⟨ikm, rfl⟩ := doneKeys_pqxdh hT hk; exact ⟨_, .inr (pqxdhKdf_rk_eq ikm)⟩

/-- Every receive root is an `hkdfBlock2` node, labelled `"WhisperRatchet"` (cases (a), (b)) or
`pqxdhLabel` (case (c)). -/
theorem recvRoot_form {T : ExecTrace} (hT : ReachableTrace T) {pk R : DY.Bytes}
    (h : RecvRoot T pk R) :
    ∃ prk, R = hkdfBlock2 prk (lit "WhisperRatchet") ∨ R = hkdfBlock2 prk pqxdhLabel := by
  rcases h with ⟨-, -, -, -, rfl⟩ | ⟨-, -, -, -, -, -, rfl⟩ | ⟨keys, hk, rfl⟩
  · exact ⟨_, .inl (createChain_snd_eq _ _ _)⟩
  · exact ⟨_, .inl (createChain_snd_eq _ _ _)⟩
  · obtain ⟨ikm, rfl⟩ := aliceDoneKeys_pqxdh hT hk; exact ⟨_, .inr (pqxdhKdf_ck_eq ikm)⟩

theorem recvRoot_form' {T : ExecTrace} (hT : ReachableTrace T) {pk R : DY.Bytes}
    (h : RecvRoot T pk R) : ∃ prk lbl, R = hkdfBlock2 prk lbl := by
  obtain ⟨prk, h | h⟩ := recvRoot_form hT h <;> exact ⟨_, _, h⟩

theorem goodRk_form' {T : ExecTrace} (hT : ReachableTrace T) {x : DY.Bytes} (h : GoodRk T x) :
    ∃ prk lbl, x = hkdfBlock1 prk lbl := by
  obtain ⟨prk, h | h⟩ := goodRk_form hT h <;> exact ⟨_, _, h⟩

/-! ## Predecessor closure (`SpineDown (Good T)`) -/

theorem rk_eq_of_kdfRk_fst_eq {rk d rk' pk sk : DY.Bytes}
    (h : (kdfRk rk d).1 = (createChain rk' pk sk).1) : rk = rk' :=
  (hmac_inj (hkdfBlock1_inj h).1).1

theorem rk_eq_of_kdfRk_snd_eq {rk d rk' pk sk : DY.Bytes}
    (h : (kdfRk rk d).2 = (createChain rk' pk sk).2) : rk = rk' :=
  (hmac_inj (hkdfBlock2_inj h).1).1

theorem goodRk_of_kdfRk_fst_eq_stored {T : ExecTrace} (hT : ReachableTrace T) {p : Participant}
    {st : TRState} {i₀ : Nat} (hst : TRStateStoredAt p st i₀ T) {rk d : DY.Bytes}
    (h : (kdfRk rk d).1 = st.rk) : GoodRk T rk := by
  rcases rkHist_of_stored hT hst with
    (⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, j, hev, hrk⟩ |
      ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, keys, j, t, idx, pk, hev, hspk, hrk⟩) |
      ⟨p', st', i', pk, -, hst', hrk⟩
  · exact .inr (.inr ⟨keys, .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, j, hev⟩,
      rk_eq_of_kdfRk_fst_eq (h.trans hrk)⟩)
  · exact .inr (.inl ⟨pk, .inr ⟨keys, t, b, idx, ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, j, hev⟩,
      hspk, rk_eq_of_kdfRk_fst_eq (h.trans hrk)⟩⟩)
  · exact .inr (.inl ⟨pk, .inl ⟨p', st', i', hst', rk_eq_of_kdfRk_fst_eq (h.trans hrk)⟩⟩)

theorem goodRk_rk1 {T : ExecTrace} (hT : ReachableTrace T) {rk d : DY.Bytes}
    (h : GoodRk T (kdfRk rk d).1) : GoodRk T rk := by
  rcases h with ⟨p, st, i₀, hst, h⟩ | ⟨pk, ⟨p, st, i₀, hst, h⟩ | ⟨keys, t, b, idx, hB, -, h⟩⟩ |
      ⟨keys, hk, h⟩
  · exact goodRk_of_kdfRk_fst_eq_stored hT hst h
  · exact .inl ⟨p, st, i₀, hst, rk_eq_of_kdfRk_fst_eq h⟩
  · exact .inr (.inr ⟨keys, .inr hB, rk_eq_of_kdfRk_fst_eq h⟩)
  · obtain ⟨ikm, rfl⟩ := doneKeys_pqxdh hT hk
    have h' := (hkdfBlock1_inj (h.trans (pqxdhKdf_rk_eq ikm))).2
    exact absurd h'.symm pqxdhLabel_ne_whisperRatchet_rk

/-- `Good T` is closed under Double Ratchet chain-key and root-key KDF predecessors on any
reachable trace `T`. -/
theorem spineDown_good {T : ExecTrace} (hT : ReachableTrace T) : SpineDown (Good T) where
  ck1 := by
    intro ck h
    rcases h with ⟨pk, R, j, b, hR, h⟩ | h
    · obtain ⟨prk, lbl, rfl⟩ := recvRoot_form' hT hR
      cases b with
      | true => exact absurd h (kdfCk_fst_ne_snd _ _)
      | false =>
        cases j with
        | zero => exact absurd h (kdfCk_fst_ne_hkdfBlock2 _ _ _)
        | succ j =>
          have h' : (kdfCk ck).1 = (kdfCk (chainKeyAt (hkdfBlock2 prk lbl) j)).1 :=
            h.trans (chainKeyAt_succ_eq_kdfCk_fst _ _)
          exact .inl ⟨pk, _, j, false, hR, kdfCk_fst_inj h'⟩
    · obtain ⟨prk, lbl, h'⟩ := goodRk_form' hT h
      exact absurd h' (kdfCk_fst_ne_hkdfBlock1 _ _ _)
  ck2 := by
    intro ck h
    rcases h with ⟨pk, R, j, b, hR, h⟩ | h
    · obtain ⟨prk, lbl, rfl⟩ := recvRoot_form' hT hR
      cases b with
      | true => exact .inl ⟨pk, _, j, false, hR, kdfCk_snd_inj h⟩
      | false =>
        cases j with
        | zero => exact absurd h (kdfCk_snd_ne_hkdfBlock2 _ _ _)
        | succ j =>
          have h' := h.trans (chainKeyAt_succ_eq_kdfCk_fst _ _)
          exact absurd h'.symm (kdfCk_fst_ne_snd _ _)
    · obtain ⟨prk, lbl, h'⟩ := goodRk_form' hT h
      exact absurd h' (kdfCk_snd_ne_hkdfBlock1 _ _ _)
  rk1 := by
    intro rk d h
    rcases h with ⟨pk, R, j, b, hR, h⟩ | h
    · obtain ⟨prk, lbl, rfl⟩ := recvRoot_form' hT hR
      exact absurd h.symm (ckOut_ne_hkdfBlock1 b prk lbl _ _ j)
    · exact .inr (goodRk_rk1 hT h)
  rk2 := by
    intro rk d h
    rcases h with ⟨pk, R, j, b, hR, h⟩ | h
    · have hR' := hR
      obtain ⟨prk, lbl, rfl⟩ := recvRoot_form' hT hR
      cases b with
      | true => exact absurd h.symm (kdfCk_snd_ne_hkdfBlock2 _ _ _)
      | false =>
        cases j with
        | succ j =>
          have h' := h.trans (chainKeyAt_succ_eq_kdfCk_fst _ _)
          exact absurd h'.symm (kdfCk_fst_ne_hkdfBlock2 _ _ _)
        | zero =>
          change (kdfRk rk d).2 = hkdfBlock2 prk lbl at h
          rcases hR' with ⟨p₀, st₀, i₀, hst₀, hR⟩ | ⟨keys, t, b', idx, hB, -, hR⟩ | ⟨keys, hk, hR⟩
          · exact .inr (.inl ⟨p₀, st₀, i₀, hst₀, rk_eq_of_kdfRk_snd_eq (h.trans hR)⟩)
          · exact .inr (.inr (.inr ⟨keys, .inr hB, rk_eq_of_kdfRk_snd_eq (h.trans hR)⟩))
          · obtain ⟨ikm, rfl⟩ := aliceDoneKeys_pqxdh hT hk
            have h' := (hkdfBlock2_inj ((h.trans hR).trans (pqxdhKdf_ck_eq ikm))).2
            exact absurd h'.symm pqxdhLabel_ne_whisperRatchet_rk
    · obtain ⟨prk, lbl, h'⟩ := goodRk_form' hT h
      exact absurd h' (hkdfBlock2_ne_hkdfBlock1 _ _ _ _)

end Symbolic.Swarm.CREF.TR.G1.Spine
