/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.MacInv
public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkSpine
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRk
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeel
import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
import Symbolic.Proofs.Swarm.CREF.TR.G1.RatchetDHRkSwapPeelTR

/-!
# HKDF Shape Alignment and Spine Lemmas for Pre-Key Own-Key Exclusion

Proves `gamma'` shape injectivity and disjointness for `hkdfBlock1`, `hkdfBlock2`, `kdfCk`, and
`ckOut`, establishes `SpineRk` inversion and monotonicity along `chainKeyAt`, and defines `BobQ`
for Bob's pre-key receive chain.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg)
open DY.Libsignal.TripleRatchet (RecvChain createChain chainKeyAt consumeMessageKey hmac hkdfBlock1
  hkdfBlock2 kdfCk lit litByte zeroSalt)
open DY.Libsignal.PQXDH (HandshakeKeys pqxdhKdf pqxdhLabel)
open Symbolic.Swarm.CREF.MacInv
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.CREF.TR.G1.Spine

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

def ckOut : Bool → DY.Bytes → DY.Bytes
  | false, x => x
  | true, x => (kdfCk x).2

theorem createChain_snd_eq (rk pk sk : DY.Bytes) : (createChain rk pk sk).2 =
    hkdfBlock2 (hmac rk (DiffieHellman.dh (X25519.normalizeX25519Key pk) sk)) (lit "WhisperRatchet") := rfl

theorem pqxdhKdf_rk_eq (ikm : DY.Bytes) :
    (pqxdhKdf ikm).rk = hkdfBlock1 (hmac zeroSalt ikm) pqxdhLabel := rfl

theorem pqxdhKdf_ck_eq (ikm : DY.Bytes) :
    (pqxdhKdf ikm).ck = hkdfBlock2 (hmac zeroSalt ikm) pqxdhLabel := rfl

private theorem shape_kdfExtract_inj {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {s₁ i₁ s₂ i₂ : DY.Bytes}
    (h : (gamma' i S g (KdfExtract.kdfExtract s₁ i₁)).shape =
      (gamma' i S g (KdfExtract.kdfExtract s₂ i₂)).shape) :
    (gamma' i S g s₁).shape = (gamma' i S g s₂).shape ∧
      (gamma' i S g i₁).shape = (gamma' i S g i₂).shape := by
  obtain ⟨_, _, hs, hi, heq⟩ := kdfExtract_shape_eq_inv_c i S g h
  obtain ⟨rfl, rfl⟩ := kdfExtract_injective heq
  exact ⟨hs, hi⟩

theorem hkdfBlock1_inj {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {p₁ l₁ p₂ l₂ : DY.Bytes}
    (h : (gamma' i S g (hkdfBlock1 p₁ l₁)).shape = (gamma' i S g (hkdfBlock1 p₂ l₂)).shape) :
    (gamma' i S g p₁).shape = (gamma' i S g p₂).shape ∧
      (gamma' i S g l₁).shape = (gamma' i S g l₂).shape := by
  have h' : (gamma' i S g (KdfExtract.kdfExtract p₁ (Concat.concat l₁ (litByte 1)))).shape =
      (gamma' i S g (KdfExtract.kdfExtract p₂ (Concat.concat l₂ (litByte 1)))).shape := h
  obtain ⟨hp, hc⟩ := shape_kdfExtract_inj h'
  exact ⟨hp, (shape_concat_inj i S g hc).1⟩

theorem hkdfBlock2_inj {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {p₁ l₁ p₂ l₂ : DY.Bytes}
    (h : (gamma' i S g (hkdfBlock2 p₁ l₁)).shape = (gamma' i S g (hkdfBlock2 p₂ l₂)).shape) :
    (gamma' i S g p₁).shape = (gamma' i S g p₂).shape ∧
      (gamma' i S g l₁).shape = (gamma' i S g l₂).shape := by
  have h' : (gamma' i S g (KdfExtract.kdfExtract p₁
      (Concat.concat (hkdfBlock1 p₁ l₁) (Concat.concat l₁ (litByte 2))))).shape =
      (gamma' i S g (KdfExtract.kdfExtract p₂
      (Concat.concat (hkdfBlock1 p₂ l₂) (Concat.concat l₂ (litByte 2))))).shape := h
  obtain ⟨hp, hc⟩ := shape_kdfExtract_inj h'
  exact ⟨hp, (shape_concat_inj i S g (shape_concat_inj i S g hc).2).1⟩

unseal DY.Bytes in
private theorem literalToBytes_inj_local {b₁ b₂ : ByteArray}
    (h : (Literal.literalToBytes b₁ : DY.Bytes) = Literal.literalToBytes b₂) : b₁ = b₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.Literal.Literal.SubF) { lit := b₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.Literal.Literal.SubF) { lit := b₂ }
  change DY.Bytes.view? (Literal.literalToBytes b₁) _ = _ at h1
  change DY.Bytes.view? (Literal.literalToBytes b₂) _ = _ at h2
  rw [h, h2] at h1
  injection h1 with h1
  exact (congrArg DY.Literal.Literal.SubF.lit h1).symm

private theorem litByte_two_ne_one_term : litByte 2 ≠ litByte 1 := by
  intro h
  have h1 := congrArg (fun b : ByteArray => b.data[0]!) (literalToBytes_inj_local h)
  revert h1
  decide

private theorem litByte_two_ne_one {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} :
    (gamma' i S g (litByte 2)).shape ≠ (gamma' i S g (litByte 1)).shape := by
  intro h
  exact litByte_two_ne_one_term (eq_of_shape_eq_literal i S g h)

private theorem hkdfBlock2_ne_hkdfBlock1 {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    (p₁ l₁ p₂ l₂ : DY.Bytes) :
    (gamma' i S g (hkdfBlock2 p₁ l₁)).shape ≠ (gamma' i S g (hkdfBlock1 p₂ l₂)).shape := by
  intro h
  have h' : (gamma' i S g (KdfExtract.kdfExtract p₁
      (Concat.concat (hkdfBlock1 p₁ l₁) (Concat.concat l₁ (litByte 2))))).shape =
      (gamma' i S g (KdfExtract.kdfExtract p₂ (Concat.concat l₂ (litByte 1)))).shape := h
  have hc := (shape_concat_inj i S g (shape_kdfExtract_inj h').2).2
  exact shape_literal_ne_concat i S g _ _ _ hc.symm

private theorem kdfCk_fst_ne_hkdfBlock1 {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    (ck p l : DY.Bytes) :
    (gamma' i S g (kdfCk ck).1).shape ≠ (gamma' i S g (hkdfBlock1 p l)).shape := by
  intro h
  have h' : (gamma' i S g (KdfExtract.kdfExtract ck (litByte 2))).shape =
      (gamma' i S g (KdfExtract.kdfExtract p (Concat.concat l (litByte 1)))).shape := h
  exact shape_literal_ne_concat i S g _ _ _ (shape_kdfExtract_inj h').2

private theorem kdfCk_snd_ne_hkdfBlock1 {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    (ck p l : DY.Bytes) :
    (gamma' i S g (kdfCk ck).2).shape ≠ (gamma' i S g (hkdfBlock1 p l)).shape := by
  intro h
  have h' : (gamma' i S g (KdfExtract.kdfExtract ck (litByte 1))).shape =
      (gamma' i S g (KdfExtract.kdfExtract p (Concat.concat l (litByte 1)))).shape := h
  exact shape_literal_ne_concat i S g _ _ _ (shape_kdfExtract_inj h').2

private theorem kdfCk_fst_ne_hkdfBlock2 {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    (ck p l : DY.Bytes) :
    (gamma' i S g (kdfCk ck).1).shape ≠ (gamma' i S g (hkdfBlock2 p l)).shape := by
  intro h
  have h' : (gamma' i S g (KdfExtract.kdfExtract ck (litByte 2))).shape =
      (gamma' i S g (KdfExtract.kdfExtract p
        (Concat.concat (hkdfBlock1 p l) (Concat.concat l (litByte 2))))).shape := h
  exact shape_literal_ne_concat i S g _ _ _ (shape_kdfExtract_inj h').2

private theorem kdfCk_snd_ne_hkdfBlock2 {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    (ck p l : DY.Bytes) :
    (gamma' i S g (kdfCk ck).2).shape ≠ (gamma' i S g (hkdfBlock2 p l)).shape := by
  intro h
  have h' : (gamma' i S g (KdfExtract.kdfExtract ck (litByte 1))).shape =
      (gamma' i S g (KdfExtract.kdfExtract p
        (Concat.concat (hkdfBlock1 p l) (Concat.concat l (litByte 2))))).shape := h
  exact shape_literal_ne_concat i S g _ _ _ (shape_kdfExtract_inj h').2

private theorem kdfCk_fst_ne_snd {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    (a b : DY.Bytes) :
    (gamma' i S g (kdfCk a).1).shape ≠ (gamma' i S g (kdfCk b).2).shape := by
  intro h
  have h' : (gamma' i S g (KdfExtract.kdfExtract a (litByte 2))).shape =
      (gamma' i S g (KdfExtract.kdfExtract b (litByte 1))).shape := h
  exact litByte_two_ne_one (shape_kdfExtract_inj h').2

private theorem kdfCk_fst_inj {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {a b : DY.Bytes} (h : (gamma' i S g (kdfCk a).1).shape = (gamma' i S g (kdfCk b).1).shape) :
    (gamma' i S g a).shape = (gamma' i S g b).shape :=
  (shape_kdfExtract_inj (show (gamma' i S g (KdfExtract.kdfExtract a (litByte 2))).shape =
    (gamma' i S g (KdfExtract.kdfExtract b (litByte 2))).shape from h)).1

private theorem kdfCk_snd_inj {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {a b : DY.Bytes} (h : (gamma' i S g (kdfCk a).2).shape = (gamma' i S g (kdfCk b).2).shape) :
    (gamma' i S g a).shape = (gamma' i S g b).shape :=
  (shape_kdfExtract_inj (show (gamma' i S g (KdfExtract.kdfExtract a (litByte 1))).shape =
    (gamma' i S g (KdfExtract.kdfExtract b (litByte 1))).shape from h)).1

theorem ckOut_ne_hkdfBlock1 {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    (b : Bool) (p l p' l' : DY.Bytes) :
    ∀ j, (gamma' i S g (ckOut b (chainKeyAt (hkdfBlock2 p l) j))).shape ≠
      (gamma' i S g (hkdfBlock1 p' l')).shape := by
  intro j
  cases b with
  | true => exact kdfCk_snd_ne_hkdfBlock1 _ _ _
  | false =>
    cases j with
    | zero => exact hkdfBlock2_ne_hkdfBlock1 p l p' l'
    | succ j =>
      show (gamma' i S g (chainKeyAt (hkdfBlock2 p l) (j + 1))).shape ≠ _
      rw [chainKeyAt_succ_eq_kdfCk_fst]
      exact kdfCk_fst_ne_hkdfBlock1 _ _ _

private theorem chainKeyAt_hkdfBlock2_align {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {p₁ l₁ p₂ l₂ : DY.Bytes} :
    ∀ {k₁ k₂ : Nat},
      (gamma' i S g (chainKeyAt (hkdfBlock2 p₁ l₁) k₁)).shape =
        (gamma' i S g (chainKeyAt (hkdfBlock2 p₂ l₂) k₂)).shape →
      k₁ = k₂ ∧ (gamma' i S g (hkdfBlock2 p₁ l₁)).shape = (gamma' i S g (hkdfBlock2 p₂ l₂)).shape
  | 0, 0, h => ⟨rfl, h⟩
  | 0, k₂ + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    exact absurd h.symm (kdfCk_fst_ne_hkdfBlock2 _ _ _)
  | k₁ + 1, 0, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    exact absurd h (kdfCk_fst_ne_hkdfBlock2 _ _ _)
  | k₁ + 1, k₂ + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst, chainKeyAt_succ_eq_kdfCk_fst] at h
    obtain ⟨hk, hr⟩ := chainKeyAt_hkdfBlock2_align (kdfCk_fst_inj h)
    exact ⟨congrArg Nat.succ hk, hr⟩

theorem ckOut_align {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {p₁ l₁ p₂ l₂ : DY.Bytes} {b₁ b₂ : Bool} {j₁ j₂ : Nat}
    (h : (gamma' i S g (ckOut b₁ (chainKeyAt (hkdfBlock2 p₁ l₁) j₁))).shape =
      (gamma' i S g (ckOut b₂ (chainKeyAt (hkdfBlock2 p₂ l₂) j₂))).shape) :
    b₁ = b₂ ∧ j₁ = j₂ ∧
      (gamma' i S g (hkdfBlock2 p₁ l₁)).shape = (gamma' i S g (hkdfBlock2 p₂ l₂)).shape := by
  have mixed : ∀ {k₁ k₂ : Nat} {pa la pb lb : DY.Bytes},
      (gamma' i S g (chainKeyAt (hkdfBlock2 pa la) k₁)).shape ≠
        (gamma' i S g (kdfCk (chainKeyAt (hkdfBlock2 pb lb) k₂)).2).shape :=
    fun {k₁ k₂ pa la pb lb} hk => by
      cases k₁ with
      | zero => exact kdfCk_snd_ne_hkdfBlock2 _ _ _ hk.symm
      | succ k =>
        rw [chainKeyAt_succ_eq_kdfCk_fst] at hk
        exact kdfCk_fst_ne_snd _ _ hk
  cases b₁ <;> cases b₂
  · obtain ⟨hj, hr⟩ := chainKeyAt_hkdfBlock2_align h; exact ⟨rfl, hj, hr⟩
  · exact absurd h mixed
  · exact absurd h.symm mixed
  · obtain ⟨hj, hr⟩ := chainKeyAt_hkdfBlock2_align (kdfCk_snd_inj h); exact ⟨rfl, hj, hr⟩

theorem stored_rk_form {T : ExecTrace} (hT : ReachableTrace T)
    {p : Participant} {st : TRState} {i₀ : Nat} (hst : TRStateStoredAt p st i₀ T) :
    ∃ prk, st.rk = hkdfBlock1 prk (lit "WhisperRatchet") := by
  obtain ⟨rk1, k, _, _, hrk⟩ := stCksIsCreateChain_of_stored hT hst
  exact ⟨hmac rk1 (DiffieHellman.dh (X25519.normalizeX25519Key k) st.dhs), hrk⟩

private theorem spineRk_of_kdfCk_fst {B : Bool → DY.Bytes → Prop} {b : Bool} {ck : DY.Bytes}
    (h : SpineRk B b (kdfCk ck).1) : SpineRk B b ck := by
  generalize hu : (kdfCk ck).1 = u at h
  cases h with
  | hsRk _ =>
    have h' : KdfExtract.kdfExtract ck (litByte 2) =
        KdfExtract.kdfExtract _ (Concat.concat pqxdhLabel (litByte 1)) := hu
    exact absurd (kdfExtract_inj_rk h').2.symm (concat_ne_literal_rk _ _ _)
  | hsCk _ =>
    have h' : KdfExtract.kdfExtract ck (litByte 2) =
        KdfExtract.kdfExtract _ (Concat.concat _ (Concat.concat pqxdhLabel (litByte 2))) := hu
    exact absurd (kdfExtract_inj_rk h').2.symm (concat_ne_literal_rk _ _ _)
  | rkStep1 _ _ =>
    have h' : KdfExtract.kdfExtract ck (litByte 2) =
        KdfExtract.kdfExtract _ (Concat.concat (lit "WhisperRatchet") (litByte 1)) := hu
    exact absurd (kdfExtract_inj_rk h').2.symm (concat_ne_literal_rk _ _ _)
  | rkStep2 _ _ =>
    have h' : KdfExtract.kdfExtract ck (litByte 2) =
        KdfExtract.kdfExtract _ (Concat.concat _ (Concat.concat (lit "WhisperRatchet") (litByte 2))) := hu
    exact absurd (kdfExtract_inj_rk h').2.symm (concat_ne_literal_rk _ _ _)
  | @ckStep1 _ ck' hck =>
    have h' : KdfExtract.kdfExtract ck (litByte 2) = KdfExtract.kdfExtract ck' (litByte 2) := hu
    exact (kdfExtract_inj_rk h').1.symm ▸ hck
  | @ckStep2 _ ck' _ =>
    have h' : KdfExtract.kdfExtract ck (litByte 2) = KdfExtract.kdfExtract ck' (litByte 1) := hu
    exact absurd (kdfExtract_inj_rk h').2 litByte_two_ne_one_term

private theorem spineRk_of_kdfCk_snd {B : Bool → DY.Bytes → Prop} {b : Bool} {ck : DY.Bytes}
    (h : SpineRk B b (kdfCk ck).2) : SpineRk B b ck := by
  generalize hu : (kdfCk ck).2 = u at h
  cases h with
  | hsRk _ =>
    have h' : KdfExtract.kdfExtract ck (litByte 1) =
        KdfExtract.kdfExtract _ (Concat.concat pqxdhLabel (litByte 1)) := hu
    exact absurd (kdfExtract_inj_rk h').2.symm (concat_ne_literal_rk _ _ _)
  | hsCk _ =>
    have h' : KdfExtract.kdfExtract ck (litByte 1) =
        KdfExtract.kdfExtract _ (Concat.concat _ (Concat.concat pqxdhLabel (litByte 2))) := hu
    exact absurd (kdfExtract_inj_rk h').2.symm (concat_ne_literal_rk _ _ _)
  | rkStep1 _ _ =>
    have h' : KdfExtract.kdfExtract ck (litByte 1) =
        KdfExtract.kdfExtract _ (Concat.concat (lit "WhisperRatchet") (litByte 1)) := hu
    exact absurd (kdfExtract_inj_rk h').2.symm (concat_ne_literal_rk _ _ _)
  | rkStep2 _ _ =>
    have h' : KdfExtract.kdfExtract ck (litByte 1) =
        KdfExtract.kdfExtract _ (Concat.concat _ (Concat.concat (lit "WhisperRatchet") (litByte 2))) := hu
    exact absurd (kdfExtract_inj_rk h').2.symm (concat_ne_literal_rk _ _ _)
  | @ckStep1 _ ck' _ =>
    have h' : KdfExtract.kdfExtract ck (litByte 1) = KdfExtract.kdfExtract ck' (litByte 2) := hu
    exact absurd (kdfExtract_inj_rk h').2.symm litByte_two_ne_one_term
  | @ckStep2 _ ck' hck =>
    have h' : KdfExtract.kdfExtract ck (litByte 1) = KdfExtract.kdfExtract ck' (litByte 1) := hu
    exact (kdfExtract_inj_rk h').1.symm ▸ hck

private theorem spineRk_of_chainKeyAt {B : Bool → DY.Bytes → Prop} {b : Bool} {ck : DY.Bytes} :
    ∀ j : Nat, SpineRk B b (chainKeyAt ck j) → SpineRk B b ck
  | 0, h => h
  | j + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    exact spineRk_of_chainKeyAt j (spineRk_of_kdfCk_fst h)

theorem spineRk_chainKeyAt {B : Bool → DY.Bytes → Prop} {b : Bool} {ck : DY.Bytes}
    (h : SpineRk B b ck) : ∀ j : Nat, SpineRk B b (chainKeyAt ck j)
  | 0 => h
  | j + 1 => by
    rw [chainKeyAt_succ_eq_kdfCk_fst]
    exact .ckStep1 (spineRk_chainKeyAt h j)

theorem spineRk_ckOut {B : Bool → DY.Bytes → Prop} {b : Bool} {x : DY.Bytes}
    (sel : Bool) (h : SpineRk B b x) : SpineRk B b (ckOut sel x) := by
  cases sel
  · exact h
  · exact .ckStep2 h

theorem spineRk_mono {B B' : Bool → DY.Bytes → Prop}
    (hB : ∀ c m, B c m → B' c m) {b : Bool} {u : DY.Bytes}
    (hu : SpineRk B b u) : SpineRk B' b u := by
  induction hu with
  | hsRk h => exact .hsRk (hB _ _ h)
  | hsCk h => exact .hsCk (hB _ _ h)
  | rkStep1 _ hrk ih => exact .rkStep1 ih hrk
  | rkStep2 _ hrk ih => exact .rkStep2 ih hrk
  | ckStep1 _ ih => exact .ckStep1 ih
  | ckStep2 _ ih => exact .ckStep2 ih

theorem spineRk_bobChain_ckOut {r : ProtocolSetup} (hne : r.alice ≠ r.bob) (ms : List Move)
    {p : PreKeyFields} {x' : PreKeyRep} {keys' : HandshakeKeys} {msg' : TRSignalMsg}
    {seed' : DY.Bytes} {c' : RecvChain}
    (hkeys : bobKeys r p x' = some keys')
    (hcmk : consumeMessageKey (bobChain r keys' msg') msg'.counter = some (seed', c'))
    (j : Nat) (b : Bool) :
    SpineRk (LoggedOrBobIkmRk r ms p x') false
      (ckOut b (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j)) := by
  have hseed := spineRk_bobSeed hne ms hkeys hcmk
  have hseed_eq : seed' =
      (kdfCk (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2
        (msg'.counter.toNat - (bobChain r keys' msg').index.toNat))).2 :=
    (consumeMessageKey_eq_spine hcmk).1
  rw [hseed_eq] at hseed
  have hroot := spineRk_of_chainKeyAt _ (spineRk_of_kdfCk_snd hseed)
  exact spineRk_ckOut b (spineRk_chainKeyAt hroot j)

theorem spineRk_of_honestSendRoot {r : ProtocolSetup} {ms : List Move} {root : DY.Bytes}
    (hH : HonestSendRoot (runTraceMoves r ms) root) :
    SpineRk (LoggedIkmRk (runTraceMoves r ms)) true root := by
  obtain ⟨p', st', i', j', hst', hcks, _⟩ := hH
  have hsp := (spStateRk_of_trStoredAt (traceOkR_runTrace r ms) hst').cks
  rw [hcks] at hsp
  exact spineRk_of_chainKeyAt j' hsp

private theorem ckOut_split_of_ak {T : ExecTrace} {s₀ i₀ : DY.Bytes} (hs : s₀.AttackerKnows T)
    (hi : i₀.AttackerKnows T) (b : Bool) (j : Nat) :
    ∃ (s i : DY.Bytes), ckOut b (chainKeyAt (KdfExtract.kdfExtract s₀ i₀) j) = KdfExtract.kdfExtract s i ∧
      s.AttackerKnows T ∧ i.AttackerKnows T := by
  have hX : (KdfExtract.kdfExtract s₀ i₀).AttackerKnows T := ak_hmac hs hi
  cases b with
  | true =>
    exact ⟨chainKeyAt (KdfExtract.kdfExtract s₀ i₀) j, litByte 1, rfl,
      attackerKnows_chainKeyAt_srk j hX, ak_lit _⟩
  | false =>
    cases j with
    | zero => exact ⟨s₀, i₀, rfl, hs, hi⟩
    | succ j =>
      refine ⟨chainKeyAt (KdfExtract.kdfExtract s₀ i₀) j, litByte 2, ?_,
        attackerKnows_chainKeyAt_srk j hX, ak_lit _⟩
      exact chainKeyAt_succ_eq_kdfCk_fst _ j

theorem ckOut_hkdfBlock2_split_of_ak {T : ExecTrace} {prk : DY.Bytes} (hp : prk.AttackerKnows T)
    (b : Bool) (j : Nat) :
    ∃ (s i : DY.Bytes), ckOut b (chainKeyAt (hkdfBlock2 prk (lit "WhisperRatchet")) j) =
      KdfExtract.kdfExtract s i ∧ s.AttackerKnows T ∧ i.AttackerKnows T :=
  ckOut_split_of_ak (s₀ := prk)
    (i₀ := Concat.concat (hkdfBlock1 prk (lit "WhisperRatchet"))
      (Concat.concat (lit "WhisperRatchet") (litByte 2)))
    hp (ak_concat (ak_hkdfBlock1 hp (ak_lit _)) (ak_concat (ak_lit _) (ak_lit _))) b j

/-- Predicate characterizing values on Bob's pre-key receive spine: chain-key outputs from
`(createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2` or the handshake root key `keys'.rk`. -/
def BobQ (r : ProtocolSetup) (keys' : HandshakeKeys) (msg' : TRSignalMsg) (v : DY.Bytes) : Prop :=
  (∃ (j : Nat) (b : Bool),
    v = ckOut b (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j)) ∨
  v = keys'.rk

end Symbolic.Swarm.CREF.CliPure
