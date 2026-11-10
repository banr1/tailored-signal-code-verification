/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Init.Data.String.Defs
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.DiffieHellman
import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Symbolic.Proofs.Swarm.CREF.MacInv
public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainG1bAux
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainLeafA
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.DhSafe
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRk
import Symbolic.Proofs.Swarm.CREF.TR.G1.KdfProvNon01
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeelDefs
import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
import Symbolic.Proofs.Swarm.CREF.TR.G1.RatchetDHRkSwapPeelTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkSpine
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineRkK
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineShapeModKemInv
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Canonical Pre-Key Representation for Attacker-Known Receive Seeds

Constructs a canonical pre-key representation `x` (`rpk_seed_ak_exactRep`) when Bob's receive seed
`seed'` is attacker-known on `runTraceMoves r ms`, splitting on whether `normalizeX25519Key x'.ek`
has a `DhPk` view or peels down the PQXDH key-derivation spine.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg trMsgKeys)
open DY.Libsignal.TripleRatchet (RecvChain createChain chainKeyAt consumeMessageKey computeMac hmac
  hkdfBlock1 hkdfBlock2 kdfCk lit litByte zeroSalt)
open DY.Libsignal.PQXDH (HandshakeKeys pqxdhKdf pqxdhIkm pqxdhLabel discontinuity agree errToOption
  serializedIk)
open Symbolic.Swarm.CREF.MacInv
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.CREF.TR.G1.Spine
open Symbolic.Swarm.CREF.TR.RecvDecStep

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Shape and Attacker-Knowledge Helpers -/

private theorem leafB_shape_concat_inj (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {l₁ r₁ l₂ r₂ : DY.Bytes}
    (h : (gamma' i S g (Concat.concat l₁ r₁)).shape = (gamma' i S g (Concat.concat l₂ r₂)).shape) :
    (gamma' i S g l₁).shape = (gamma' i S g l₂).shape ∧
      (gamma' i S g r₁).shape = (gamma' i S g r₂).shape := by
  rw [shape_concat_tr, shape_concat_tr] at h
  exact concat_injective h

private theorem leafB_shape_literal_ne_concat (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (b : ByteArray) (l r : DY.Bytes) :
    (gamma' i S g (Literal.literalToBytes b)).shape ≠ (gamma' i S g (Concat.concat l r)).shape := by
  rw [shape_literalToBytes, shape_concat_tr]
  exact literal_ne_concat b _ _

unseal DY.Bytes in
private theorem leafB_literal_ne_dhPack (b : ByteArray) (p s : DY.Bytes) :
    Literal.literalToBytes b ≠ (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  intro h
  have h1 := DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) { pk := p, sk := s }
  change DY.Bytes.view? (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) _ = _ at h1
  have h2 : DY.Bytes.view? (Literal.literalToBytes b) DY.DiffieHellman.Dh.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  rw [← h, h2] at h1
  contradiction

unseal DY.Bytes in
private theorem leafB_concat_ne_dhPack (l r p s : DY.Bytes) :
    Concat.concat l r ≠ (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  intro h
  have h1 := DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) { pk := p, sk := s }
  change DY.Bytes.view? (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) _ = _ at h1
  have h2 : DY.Bytes.view? (Concat.concat l r) DY.DiffieHellman.Dh.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  rw [← h, h2] at h1
  contradiction

private theorem leafB_shape_dh_eq_pack (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pk' r : DY.Bytes) : ∃ P Q : DY.Bytes,
    (gamma' i S g (dh pk' r)).shape = (({ pk := P, sk := Q } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  obtain ⟨P, Q, hd, -⟩ := dh_eq_pack_and_or pk' r
  rw [hd, shape_dhPack_c]
  exact ⟨_, _, rfl⟩

private theorem leafB_shape_literal_ne_dh (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (b : ByteArray) (pk' r : DY.Bytes) :
    (gamma' i S g (Literal.literalToBytes b)).shape ≠ (gamma' i S g (dh pk' r)).shape := by
  obtain ⟨P, Q, h⟩ := leafB_shape_dh_eq_pack i S g pk' r
  rw [h, shape_literalToBytes]
  exact leafB_literal_ne_dhPack b P Q

private theorem leafB_shape_concat_ne_dh (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (l r pk' sk : DY.Bytes) :
    (gamma' i S g (Concat.concat l r)).shape ≠ (gamma' i S g (dh pk' sk)).shape := by
  obtain ⟨P, Q, h⟩ := leafB_shape_dh_eq_pack i S g pk' sk
  rw [h, shape_concat_tr]
  exact leafB_concat_ne_dhPack _ _ P Q

unseal DY.Bytes in
private theorem leafB_literalToBytes_inj {b₁ b₂ : ByteArray}
    (h : (Literal.literalToBytes b₁ : DY.Bytes) = Literal.literalToBytes b₂) : b₁ = b₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.Literal.Literal.SubF) { lit := b₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.Literal.Literal.SubF) { lit := b₂ }
  change DY.Bytes.view? (Literal.literalToBytes b₁) _ = _ at h1
  change DY.Bytes.view? (Literal.literalToBytes b₂) _ = _ at h2
  rw [h, h2] at h1
  injection h1 with h1
  exact (congrArg DY.Literal.Literal.SubF.lit h1).symm

private theorem leafB_eq_of_shape_eq_literal (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {b₁ b₂ : ByteArray}
    (h : (gamma' i S g (Literal.literalToBytes b₁)).shape =
      (gamma' i S g (Literal.literalToBytes b₂)).shape) :
    (Literal.literalToBytes b₁ : DY.Bytes) = Literal.literalToBytes b₂ := by
  rwa [shape_literalToBytes, shape_literalToBytes] at h

private theorem leafB_lit_wr_length : (lit "WhisperRatchet").length = 14 := by
  unfold lit
  rw [Literal.length_literalToBytes, String.toUTF8_eq_toByteArray,
      ← String.ofList_toList (s := "WhisperRatchet"), String.toByteArray_ofList]
  decide

private theorem leafB_pqxdhLabel_length : pqxdhLabel.length = 46 := by
  unfold pqxdhLabel lit
  rw [Literal.length_literalToBytes, String.toUTF8_eq_toByteArray,
      ← String.ofList_toList (s := "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"),
      String.toByteArray_ofList]
  decide

private theorem leafB_discontinuity_length : discontinuity.length = 32 := by
  unfold discontinuity; rw [Literal.length_literalToBytes]; rfl

private theorem leafB_shape_lit_wr_ne_pq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    (gamma' i S g (lit "WhisperRatchet")).shape ≠ (gamma' i S g pqxdhLabel).shape := by
  intro h
  have h1 := congrArg DY.Bytes.length (leafB_eq_of_shape_eq_literal i S g h)
  change (lit "WhisperRatchet").length = pqxdhLabel.length at h1
  rw [leafB_lit_wr_length, leafB_pqxdhLabel_length] at h1
  cases h1

private theorem leafB_shape_lit_wr_ne_disc (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    (gamma' i S g (lit "WhisperRatchet")).shape ≠ (gamma' i S g discontinuity).shape := by
  intro h
  have h1 := congrArg DY.Bytes.length (leafB_eq_of_shape_eq_literal i S g h)
  change (lit "WhisperRatchet").length = discontinuity.length at h1
  rw [leafB_lit_wr_length, leafB_discontinuity_length] at h1
  cases h1

private theorem leafB_no7_lit (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (b : ByteArray) (b1 : DY.Bytes) :
    (gamma' i S g (Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3)))).shape ≠
      (gamma' i S g (Literal.literalToBytes b)).shape :=
  fun h => leafB_shape_literal_ne_concat i S g b _ _ h.symm

private theorem leafB_no7_x1 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (L b1 : DY.Bytes) :
    (gamma' i S g (Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3)))).shape ≠
      (gamma' i S g (Concat.concat L (litByte 1))).shape :=
  fun h => leafB_shape_literal_ne_concat i S g _ _ _ (leafB_shape_concat_inj i S g h).2.symm

private theorem leafB_no7_wr2 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (X b1 : DY.Bytes) :
    (gamma' i S g (Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3)))).shape ≠
      (gamma' i S g (Concat.concat X (Concat.concat (lit "WhisperRatchet") (litByte 2)))).shape :=
  fun h => leafB_shape_lit_wr_ne_pq i S g
    (leafB_shape_concat_inj i S g (leafB_shape_concat_inj i S g h).2).1.symm

private theorem leafB_ak_lit {T : ExecTrace} (b : ByteArray) :
    (Literal.literalToBytes b : DY.Bytes).AttackerKnows T :=
  Literal.attacker_knows_literalToBytes b T

private theorem leafB_ak_concat {T : ExecTrace} {l r : DY.Bytes}
    (hl : l.AttackerKnows T) (hr : r.AttackerKnows T) :
    (Concat.concat l r).AttackerKnows T :=
  Concat.attacker_knows_concat l r T hl hr

private theorem leafB_ak_hmac {T : ExecTrace} {k m : DY.Bytes}
    (hk : k.AttackerKnows T) (hm : m.AttackerKnows T) :
    (hmac k m).AttackerKnows T :=
  KdfExtract.attacker_knows_kdfExtract k m T hk hm

private theorem leafB_ak_hkdfBlock1 {T : ExecTrace} {prk info : DY.Bytes}
    (hp : prk.AttackerKnows T) (hi : info.AttackerKnows T) :
    (hkdfBlock1 prk info).AttackerKnows T :=
  leafB_ak_hmac hp (leafB_ak_concat hi (leafB_ak_lit _))

private theorem leafB_ak_hkdfBlock2 {T : ExecTrace} {prk info : DY.Bytes}
    (hp : prk.AttackerKnows T) (hi : info.AttackerKnows T) :
    (hkdfBlock2 prk info).AttackerKnows T :=
  leafB_ak_hmac hp (leafB_ak_concat (leafB_ak_hkdfBlock1 hp hi) (leafB_ak_concat hi (leafB_ak_lit _)))

private theorem leafB_ak_split {T : ExecTrace} {l r : DY.Bytes}
    (h : (Concat.concat l r).AttackerKnows T) :
    l.AttackerKnows T ∧ r.AttackerKnows T := by
  have h1 := Concat.attacker_knows_split _ l.length T h
  rw [Concat.split_concat] at h1
  exact h1

private theorem leafB_peel_outer (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hT : ReachableTrace T) {u s₁ i₁ : DY.Bytes}
    (hu : u.AttackerKnows T)
    (hsh : (gamma' i S g u).shape = (gamma' i S g (KdfExtract.kdfExtract s₁ i₁)).shape) :
    ∃ s' i', u = KdfExtract.kdfExtract s' i' ∧
      (gamma' i S g s').shape = (gamma' i S g s₁).shape ∧
      (gamma' i S g i').shape = (gamma' i S g i₁).shape ∧
      ((HonestKdfOut T u ∨ SkippedSeedLogged T u) ∨
        (∃ b1, i' = Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3))) ∨
        (s'.AttackerKnows T ∧ i'.AttackerKnows T)) := by
  obtain ⟨s', i', hs, hi, rfl⟩ := kdfExtract_shape_eq_inv_c i S g hsh
  refine ⟨s', i', rfl, hs, hi, ?_⟩
  rcases kdfInputValidProv_of_attackerKnows_reachable hT hu with
    h1 | ⟨_, j, ses, pk, n, rIdx, src, hev⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | h7
  · exact .inr (.inr h1)
  · exact .inl (.inr ⟨j, ses, pk, n, rIdx, src, hev⟩)
  · exact .inl (.inl h)
  · exact .inl (.inl h)
  · exact .inl (.inl h)
  · exact .inl (.inl h)
  · exact .inr (.inl h7)

/-! ## Non-`DhPk` Pre-Key Spine Peel -/

private def leafB_ckOut : Bool → DY.Bytes → DY.Bytes
  | false, x => x
  | true, x => (kdfCk x).2

private theorem leafB_createChain_fst_eq (rk pk sk : DY.Bytes) : (createChain rk pk sk).1 =
    hkdfBlock1 (hmac rk (DiffieHellman.dh (X25519.normalizeX25519Key pk) sk)) (lit "WhisperRatchet") := rfl

private theorem leafB_createChain_snd_eq (rk pk sk : DY.Bytes) : (createChain rk pk sk).2 =
    hkdfBlock2 (hmac rk (DiffieHellman.dh (X25519.normalizeX25519Key pk) sk)) (lit "WhisperRatchet") := rfl

private theorem leafB_pqxdhKdf_rk_eq (ikm : DY.Bytes) :
    (pqxdhKdf ikm).rk = hkdfBlock1 (hmac zeroSalt ikm) pqxdhLabel := rfl

private theorem leafB_pqxdhKdf_ck_eq (ikm : DY.Bytes) :
    (pqxdhKdf ikm).ck = hkdfBlock2 (hmac zeroSalt ikm) pqxdhLabel := rfl

private theorem leafB_hkdfBlock1_inj {p₁ l₁ p₂ l₂ : DY.Bytes}
    (h : hkdfBlock1 p₁ l₁ = hkdfBlock1 p₂ l₂) :
    p₁ = p₂ ∧ l₁ = l₂ := by
  have h' : KdfExtract.kdfExtract p₁ (Concat.concat l₁ (litByte 1)) =
      KdfExtract.kdfExtract p₂ (Concat.concat l₂ (litByte 1)) := h
  exact ⟨(kdfExtract_inj_rk h').1, (concat_inj_rk (kdfExtract_inj_rk h').2).1⟩

private theorem leafB_hkdfBlock2_inj {p₁ l₁ p₂ l₂ : DY.Bytes}
    (h : hkdfBlock2 p₁ l₁ = hkdfBlock2 p₂ l₂) :
    p₁ = p₂ ∧ l₁ = l₂ := by
  have h' : KdfExtract.kdfExtract p₁ (Concat.concat (hkdfBlock1 p₁ l₁) (Concat.concat l₁ (litByte 2))) =
      KdfExtract.kdfExtract p₂ (Concat.concat (hkdfBlock1 p₂ l₂) (Concat.concat l₂ (litByte 2))) := h
  exact ⟨(kdfExtract_inj_rk h').1,
    (concat_inj_rk (concat_inj_rk (kdfExtract_inj_rk h').2).2).1⟩

private theorem leafB_litByte_two_ne_one : litByte 2 ≠ litByte 1 := by
  intro h
  have h1 := congrArg (fun b : ByteArray => b.data[0]!) (leafB_literalToBytes_inj h)
  revert h1
  decide

private theorem leafB_hkdfBlock2_ne_hkdfBlock1 (p₁ l₁ p₂ l₂ : DY.Bytes) :
    hkdfBlock2 p₁ l₁ ≠ hkdfBlock1 p₂ l₂ := by
  intro h
  have h' : KdfExtract.kdfExtract p₁ (Concat.concat (hkdfBlock1 p₁ l₁) (Concat.concat l₁ (litByte 2))) =
      KdfExtract.kdfExtract p₂ (Concat.concat l₂ (litByte 1)) := h
  exact concat_ne_literal_rk _ _ _ (concat_inj_rk (kdfExtract_inj_rk h').2).2

private theorem leafB_kdfCk_fst_ne_hkdfBlock1 (ck p l : DY.Bytes) :
    (kdfCk ck).1 ≠ hkdfBlock1 p l := by
  intro h
  have h' : KdfExtract.kdfExtract ck (litByte 2) =
      KdfExtract.kdfExtract p (Concat.concat l (litByte 1)) := h
  exact concat_ne_literal_rk _ _ _ (kdfExtract_inj_rk h').2.symm

private theorem leafB_kdfCk_snd_ne_hkdfBlock1 (ck p l : DY.Bytes) :
    (kdfCk ck).2 ≠ hkdfBlock1 p l := by
  intro h
  have h' : KdfExtract.kdfExtract ck (litByte 1) =
      KdfExtract.kdfExtract p (Concat.concat l (litByte 1)) := h
  exact concat_ne_literal_rk _ _ _ (kdfExtract_inj_rk h').2.symm

private theorem leafB_kdfCk_snd_ne_hkdfBlock2 (ck p l : DY.Bytes) :
    (kdfCk ck).2 ≠ hkdfBlock2 p l := by
  intro h
  have h' : KdfExtract.kdfExtract ck (litByte 1) =
      KdfExtract.kdfExtract p (Concat.concat (hkdfBlock1 p l) (Concat.concat l (litByte 2))) := h
  exact concat_ne_literal_rk _ _ _ (kdfExtract_inj_rk h').2.symm

private theorem leafB_kdfCk_fst_ne_snd (a b : DY.Bytes) :
    (kdfCk a).1 ≠ (kdfCk b).2 := by
  intro h
  have h' : KdfExtract.kdfExtract a (litByte 2) = KdfExtract.kdfExtract b (litByte 1) := h
  exact leafB_litByte_two_ne_one (kdfExtract_inj_rk h').2

private theorem leafB_kdfCk_snd_inj {a b : DY.Bytes} (h : (kdfCk a).2 = (kdfCk b).2) : a = b :=
  (kdfExtract_inj_rk (show KdfExtract.kdfExtract a (litByte 1) =
    KdfExtract.kdfExtract b (litByte 1) from h)).1

private theorem leafB_ckOut_ne_hkdfBlock1 (b : Bool) (p l p' l' : DY.Bytes) :
    ∀ j, leafB_ckOut b (chainKeyAt (hkdfBlock2 p l) j) ≠ hkdfBlock1 p' l' := by
  intro j
  cases b with
  | true => exact leafB_kdfCk_snd_ne_hkdfBlock1 _ _ _
  | false =>
    cases j with
    | zero => exact leafB_hkdfBlock2_ne_hkdfBlock1 p l p' l'
    | succ j =>
      show chainKeyAt (hkdfBlock2 p l) (j + 1) ≠ _
      rw [chainKeyAt_succ_eq_kdfCk_fst]
      exact leafB_kdfCk_fst_ne_hkdfBlock1 _ _ _

private theorem leafB_ckOut_align {p₁ l₁ p₂ l₂ : DY.Bytes} {b₁ b₂ : Bool} {j₁ j₂ : Nat}
    (h : leafB_ckOut b₁ (chainKeyAt (hkdfBlock2 p₁ l₁) j₁) =
      leafB_ckOut b₂ (chainKeyAt (hkdfBlock2 p₂ l₂) j₂)) :
    b₁ = b₂ ∧ j₁ = j₂ ∧ hkdfBlock2 p₁ l₁ = hkdfBlock2 p₂ l₂ := by
  have base : ∀ {k₁ k₂ : Nat}, chainKeyAt (hkdfBlock2 p₁ l₁) k₁ = chainKeyAt (hkdfBlock2 p₂ l₂) k₂ →
      k₁ = k₂ ∧ hkdfBlock2 p₁ l₁ = hkdfBlock2 p₂ l₂ := fun {k₁ k₂} hk => by
    have := chainKeyAt_concat_base_inj (s₁ := p₁) (s₂ := p₂) k₁ k₂ hk
    exact ⟨this.2, this.1⟩
  have mixed : ∀ {k₁ k₂ : Nat} {pa la pb lb : DY.Bytes},
      chainKeyAt (hkdfBlock2 pa la) k₁ ≠ (kdfCk (chainKeyAt (hkdfBlock2 pb lb) k₂)).2 :=
    fun {k₁ k₂ pa la pb lb} hk => by
      cases k₁ with
      | zero => exact leafB_kdfCk_snd_ne_hkdfBlock2 _ _ _ hk.symm
      | succ k =>
        rw [chainKeyAt_succ_eq_kdfCk_fst] at hk
        exact leafB_kdfCk_fst_ne_snd _ _ hk
  cases b₁ <;> cases b₂
  · obtain ⟨hj, hr⟩ := base h; exact ⟨rfl, hj, hr⟩
  · exact absurd h mixed
  · exact absurd h.symm mixed
  · obtain ⟨hj, hr⟩ := base (leafB_kdfCk_snd_inj h); exact ⟨rfl, hj, hr⟩

private theorem leafB_not_spineRk_keys_rk_of_view_none
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {ms : List Move} {p : PreKeyFields} {x' : PreKeyRep}
    {keys' : PQXDH.HandshakeKeys}
    (hkeys : bobKeys r p x' = some keys')
    (hv : (DY.X25519.normalizeX25519Key x'.ek).view? DY.DiffieHellman.DhPk.SubF = none) :
    ¬ SpineRk (LoggedIkmRk (runTraceMoves r ms)) false keys'.rk := by
  intro hrk
  obtain ⟨ikm, ⟨opk, _hsel, hikm⟩, hkeys_eq⟩ := bobKeys_eq_some_iff_bobPreKeyIkm r p x' keys' hkeys
  rw [hkeys_eq] at hrk
  have hlog : LoggedIkmRk (runTraceMoves r ms) false ikm := spineRk_pqxdhKdf_rk_inv i S g hrk
  obtain ⟨a, b, e, d, ss, hm, hroles, _⟩ := loggedIkmRk_roleHoles hlog
  have hb : DY.Libsignal.PQXDH.agree x'.ek (setupSecret r 1) = b := by
    rw [hikm] at hm
    unfold DY.Libsignal.PQXDH.pqxdhIkm at hm
    exact (concat_injective (concat_injective (concat_injective hm).2).2).1
  obtain ⟨_, ⟨pk', t, hbdh, hek⟩, _, _⟩ := hroles
  obtain ⟨tᵢ, hik_eq, hikAt⟩ := G1bAux.ikAt_bob_runTrace hne ms
  have hdh : dh (DY.X25519.normalizeX25519Key x'.ek) (randTerm tᵢ 32) = dh pk' (randTerm t 32) := by
    rw [← hbdh, ← hb, hik_eq]; rfl
  have hne_t : tᵢ ≠ t := fun h => ekAt_ikAt_false _ t hek (h ▸ hikAt)
  have hek_dhPk : DY.X25519.normalizeX25519Key x'.ek = DY.DiffieHellman.dhPk (randTerm t 32) :=
    G1bAux.dh_eq_dh_of_ne hne_t hdh
  rw [hek_dhPk] at hv
  dsimp only [DY.DiffieHellman.dhPk] at hv
  rw [DY.BytesView.view_pack] at hv
  cases hv

private theorem leafB_not_spineRk_bobChain_ckOut_of_view_none
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {ms : List Move} {p : PreKeyFields} {x' : PreKeyRep}
    {keys' : PQXDH.HandshakeKeys} {msg' : TRSignalMsg}
    (hkeys : bobKeys r p x' = some keys')
    (hv : (DY.X25519.normalizeX25519Key x'.ek).view? DY.DiffieHellman.DhPk.SubF = none)
    (j : Nat) (b : Bool) :
    ¬ SpineRk (LoggedIkmRk (runTraceMoves r ms)) true
      (leafB_ckOut b (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j)) := by
  intro hsp
  have hsp_ck : SpineRk (LoggedIkmRk (runTraceMoves r ms)) true
      (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j) := by
    cases b
    · exact hsp
    · exact spineRk_kdfCk_snd_inv i S g hsp
  have hsp_cc := G1bAux.spineRk_of_chainKeyAt i S g j hsp_ck
  obtain ⟨hrk, _⟩ := spineRk_kdfRk_snd_inv i S g hsp_cc
  exact leafB_not_spineRk_keys_rk_of_view_none i S g hne hkeys hv hrk

private theorem leafB_spineRk_chainKeyAt {B : Bool → DY.Bytes → Prop} {b : Bool} {ck : DY.Bytes}
    (h : SpineRk B b ck) : ∀ j : Nat, SpineRk B b (chainKeyAt ck j)
  | 0 => h
  | j + 1 => by
    rw [chainKeyAt_succ_eq_kdfCk_fst]
    exact .ckStep1 (leafB_spineRk_chainKeyAt h j)

private theorem leafB_spineRk_ckOut {B : Bool → DY.Bytes → Prop} {b : Bool} {x : DY.Bytes}
    (sel : Bool) (h : SpineRk B b x) : SpineRk B b (leafB_ckOut sel x) := by
  cases sel
  · exact h
  · exact .ckStep2 h

private theorem leafB_ckOut_split_of_ak {T : ExecTrace} {s₀ i₀ : DY.Bytes}
    (hs : s₀.AttackerKnows T) (hi : i₀.AttackerKnows T) (b : Bool) (j : Nat) :
    ∃ s i, leafB_ckOut b (chainKeyAt (KdfExtract.kdfExtract s₀ i₀) j) = KdfExtract.kdfExtract s i ∧
      s.AttackerKnows T ∧ i.AttackerKnows T := by
  have hX : (KdfExtract.kdfExtract s₀ i₀).AttackerKnows T := leafB_ak_hmac hs hi
  cases b with
  | true =>
    exact ⟨chainKeyAt (KdfExtract.kdfExtract s₀ i₀) j, litByte 1, rfl,
      attackerKnows_chainKeyAt_srk j hX, leafB_ak_lit _⟩
  | false =>
    cases j with
    | zero => exact ⟨s₀, i₀, rfl, hs, hi⟩
    | succ j =>
      refine ⟨chainKeyAt (KdfExtract.kdfExtract s₀ i₀) j, litByte 2, ?_,
        attackerKnows_chainKeyAt_srk j hX, leafB_ak_lit _⟩
      exact chainKeyAt_succ_eq_kdfCk_fst _ j

private theorem leafB_ckOut_hkdfBlock2_split_of_ak {T : ExecTrace} {prk : DY.Bytes}
    (hp : prk.AttackerKnows T) (b : Bool) (j : Nat) :
    ∃ s i, leafB_ckOut b (chainKeyAt (hkdfBlock2 prk (lit "WhisperRatchet")) j) =
      KdfExtract.kdfExtract s i ∧ s.AttackerKnows T ∧ i.AttackerKnows T :=
  leafB_ckOut_split_of_ak (s₀ := prk)
    (i₀ := Concat.concat (hkdfBlock1 prk (lit "WhisperRatchet"))
      (Concat.concat (lit "WhisperRatchet") (litByte 2)))
    hp (leafB_ak_concat (leafB_ak_hkdfBlock1 hp (leafB_ak_lit _))
      (leafB_ak_concat (leafB_ak_lit _) (leafB_ak_lit _))) b j

private theorem leafB_peel_bobQ_of_recvChainSpine
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {ms : List Move} {p : PreKeyFields} {x' : PreKeyRep}
    {keys' : PQXDH.HandshakeKeys} {msg' : TRSignalMsg}
    (hkeys : bobKeys r p x' = some keys')
    (hv : (DY.X25519.normalizeX25519Key x'.ek).view? DY.DiffieHellman.DhPk.SubF = none)
    {c : RecvChain} (hc : RecvChainSpine (runTraceMoves r ms) c) (b_u : Bool)
    {s₁ i₁ : DY.Bytes}
    (hQ : (∃ (j : Nat) (b : Bool),
      KdfExtract.kdfExtract s₁ i₁ =
        leafB_ckOut b (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j)) ∨
      KdfExtract.kdfExtract s₁ i₁ = keys'.rk)
    (hu_c : KdfExtract.kdfExtract s₁ i₁ = leafB_ckOut b_u c.chainKey) :
    s₁.AttackerKnows (runTraceMoves r ms) ∧ i₁.AttackerKnows (runTraceMoves r ms) := by
  obtain ⟨ikm, _, hkeys_eq⟩ := bobKeys_eq_some_iff_bobPreKeyIkm r p x' keys' hkeys
  rcases hc with ⟨rk', t, j_u, -, -, hcj, hH | hprk⟩ |
      ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j_u, hcj, _⟩
  · obtain ⟨p', st', i', j', hst', hcks, _⟩ := hH
    have hsp0 : SpineRk (LoggedIkmRk (runTraceMoves r ms)) true
        (createChain rk' c.ratchetKey (randTerm t 32)).2 :=
      G1bAux.spineRk_of_chainKeyAt i S g j'
        (hcks ▸ (spStateRk_of_trStoredAt (traceOkR_runTrace r ms) hst').cks)
    have hsp_u : SpineRk (LoggedIkmRk (runTraceMoves r ms)) true (leafB_ckOut b_u c.chainKey) := by
      rw [hcj]
      exact leafB_spineRk_ckOut b_u (leafB_spineRk_chainKeyAt hsp0 j_u)
    rcases hQ with ⟨j_v, b_v, hv_eq⟩ | hv_eq
    · rw [← hu_c, hv_eq] at hsp_u
      exact False.elim (leafB_not_spineRk_bobChain_ckOut_of_view_none i S g hne hkeys hv j_v b_v hsp_u)
    · have heq := hu_c.symm.trans hv_eq
      rw [hcj, leafB_createChain_snd_eq, hkeys_eq, leafB_pqxdhKdf_rk_eq] at heq
      exact absurd heq (leafB_ckOut_ne_hkdfBlock1 b_u _ _ _ _ j_u)
  · rw [hcj, leafB_createChain_snd_eq] at hu_c
    obtain ⟨s'', i'', hsplit, hs'', hi''⟩ := leafB_ckOut_hkdfBlock2_split_of_ak hprk b_u j_u
    obtain ⟨rfl, rfl⟩ := kdfExtract_injective (hu_c.trans hsplit)
    exact ⟨hs'', hi''⟩
  · rcases hQ with ⟨j_v, b_v, hv_eq⟩ | hv_eq
    · have heq := hu_c.symm.trans hv_eq
      rw [hcj, leafB_pqxdhKdf_ck_eq, leafB_createChain_snd_eq] at heq
      have hroot := (leafB_ckOut_align heq).2.2
      have hlbl := (leafB_hkdfBlock2_inj hroot).2
      exact absurd hlbl pqxdhLabel_ne_whisperRatchet_rk
    · have heq := hu_c.symm.trans hv_eq
      rw [hcj, leafB_pqxdhKdf_ck_eq, hkeys_eq, leafB_pqxdhKdf_rk_eq] at heq
      exact absurd heq (leafB_ckOut_ne_hkdfBlock1 b_u _ _ _ _ j_u)

private theorem leafB_peel_bobQ_of_view_none
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {ms : List Move} {p : PreKeyFields} {x' : PreKeyRep}
    {keys' : PQXDH.HandshakeKeys} (msg' : TRSignalMsg)
    (hreach : ReachableTrace (runTraceMoves r ms))
    (hkeys : bobKeys r p x' = some keys')
    (hv : (DY.X25519.normalizeX25519Key x'.ek).view? DY.DiffieHellman.DhPk.SubF = none)
    {s₁ i₁ : DY.Bytes}
    (hu : (KdfExtract.kdfExtract s₁ i₁).AttackerKnows (runTraceMoves r ms))
    (hQ : (∃ (j : Nat) (b : Bool),
      KdfExtract.kdfExtract s₁ i₁ =
        leafB_ckOut b (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j)) ∨
      KdfExtract.kdfExtract s₁ i₁ = keys'.rk)
    (h7 : ∀ b1, (gamma' i S g (Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3)))).shape ≠
      (gamma' i S g i₁).shape) :
    s₁.AttackerKnows (runTraceMoves r ms) ∧ i₁.AttackerKnows (runTraceMoves r ms) := by
  obtain ⟨s', i', hu_eq, _, hi, hprov⟩ := leafB_peel_outer i S g hreach hu rfl
  obtain ⟨rfl, rfl⟩ := kdfExtract_injective hu_eq.symm
  rcases hprov with hH | ⟨b1, rfl⟩ | ⟨hs', hi'⟩
  · obtain ⟨ikm, _, hkeys_eq⟩ := bobKeys_eq_some_iff_bobPreKeyIkm r p x' keys' hkeys
    rcases hH with ⟨me, st, idx, hst, hu_eq | hu_eq | ⟨c, hc, hu_eq⟩⟩ | ⟨k, ses, pk, n, rIdx, src, hev⟩
    · obtain ⟨rk1, k, j_u, _, hrk⟩ := stCksIsCreateChain_of_stored hreach hst
      rcases hQ with ⟨j_v, b_v, hv_eq⟩ | hv_eq
      · have heq := hu_eq.symm.trans hv_eq
        rw [hrk, leafB_createChain_fst_eq, leafB_createChain_snd_eq] at heq
        exact absurd heq.symm (leafB_ckOut_ne_hkdfBlock1 b_v _ _ _ _ j_v)
      · have heq := hu_eq.symm.trans hv_eq
        rw [hrk, leafB_createChain_fst_eq, hkeys_eq, leafB_pqxdhKdf_rk_eq] at heq
        exact absurd (leafB_hkdfBlock1_inj heq).2.symm pqxdhLabel_ne_whisperRatchet_rk
    · rcases hQ with ⟨j_v, b_v, hv_eq⟩ | hv_eq
      · have hsp : SpineRk (LoggedIkmRk (runTraceMoves r ms)) true st.cks :=
          (spStateRk_of_trStoredAt (traceOkR_runTrace r ms) hst).cks
        rw [← hu_eq, hv_eq] at hsp
        exact False.elim (leafB_not_spineRk_bobChain_ckOut_of_view_none i S g hne hkeys hv j_v b_v hsp)
      · obtain ⟨rk1, k, j_u, hcks, _⟩ := stCksIsCreateChain_of_stored hreach hst
        have heq : leafB_ckOut false (chainKeyAt (createChain rk1 k st.dhs).2 j_u) = keys'.rk := by
          simpa [leafB_ckOut, ← hcks] using hu_eq.symm.trans hv_eq
        rw [leafB_createChain_snd_eq, hkeys_eq, leafB_pqxdhKdf_rk_eq] at heq
        exact absurd heq (leafB_ckOut_ne_hkdfBlock1 false _ _ _ _ j_u)
    · exact leafB_peel_bobQ_of_recvChainSpine i S g hne hkeys hv
        ((stRkSpine_of_stored hreach hst).2 c hc) false hQ hu_eq
    · obtain ⟨c, hc, hu_eq⟩ :=
        (jRkSpine_reachable hreach (DY.Trace.le_refl (runTraceMoves r ms))).2 k ses pk n _ rIdx src hev
      exact leafB_peel_bobQ_of_recvChainSpine i S g hne hkeys hv
        (activeRecvChainSpine_imp_recvChainSpine hc) true hQ hu_eq
  · exact absurd hi (h7 b1)
  · exact ⟨hs', hi'⟩

private theorem leafB_bobKeys_of_opkSel {r : ProtocolSetup} {p : PreKeyFields} {opk : Option DY.Bytes}
    (hsel : OpkSel r p opk) (x : PreKeyRep) :
    bobKeys r p x = some (bobKeysOf r x opk) := by
  unfold bobKeys Symbolic.Swarm.Stage1Trials.bobOpk?
  rcases hsel with ⟨hpk, rfl⟩ | ⟨hw, hpk, rfl⟩
  · simp [hpk]
  · simp [hpk, hw]

private theorem leafB_tr_bobKeys_eq (r : ProtocolSetup) (p : PreKeyFields) (q : PreKeyRep) :
    TR.bobKeys r p q = bobKeys r p q := by
  unfold TR.bobKeys bobKeys Symbolic.Swarm.Stage1Trials.bobOpk? bobKeysOf
  cases p.preKeyId with
  | none => rfl
  | some id =>
    by_cases h1 : r.withOpk = true <;> by_cases h2 : id = r.opkId <;>
      simp [h1, h2, Bind.bind, Option.bind, Pure.pure, Option.map]

private theorem leafB_peel_chainKeyAt_of_view_none
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {ms : List Move} {p : PreKeyFields} {x' : PreKeyRep}
    {keys' : PQXDH.HandshakeKeys} (msg' : TRSignalMsg)
    (hreach : ReachableTrace (runTraceMoves r ms))
    (hkeys : bobKeys r p x' = some keys')
    (hv : (DY.X25519.normalizeX25519Key x'.ek).view? DY.DiffieHellman.DhPk.SubF = none) :
    ∀ j : Nat,
      (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j).AttackerKnows (runTraceMoves r ms) →
      (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2.AttackerKnows (runTraceMoves r ms) := by
  intro j
  induction j with
  | zero => intro h; exact h
  | succ j ih =>
    intro h
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    have hstep := leafB_peel_bobQ_of_view_none i S g hne msg' hreach hkeys hv h
      (.inl ⟨j + 1, false,
        (chainKeyAt_succ_eq_kdfCk_fst (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2 j).symm⟩)
      (leafB_no7_lit i S g (ByteArray.mk #[2]))
    exact ih hstep.1

private theorem leafB_agree_sk_ak_of_view_none
    {T : ExecTrace} (hreach : ReachableTrace T)
    {pk sk : DY.Bytes}
    (hv : (DY.X25519.normalizeX25519Key pk).view? DY.DiffieHellman.DhPk.SubF = none)
    (h : (PQXDH.agree pk sk).AttackerKnows T) :
    sk.AttackerKnows T := by
  rcases agree_attackerKnows_inv hreach h with hsk | ⟨s, hs, _⟩
  · exact hsk.2
  · rw [hs] at hv
    dsimp only [DY.DiffieHellman.dhPk] at hv
    rw [DY.BytesView.view_pack] at hv
    cases hv

private theorem leafB_peel_hmac_dh
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hreach : ReachableTrace T) {rk pk sk : DY.Bytes}
    (h : (KdfExtract.kdfExtract rk (dh pk sk)).AttackerKnows T) :
    rk.AttackerKnows T ∧ (dh pk sk).AttackerKnows T := by
  rcases kdfInputValidProv_of_attackerKnows_reachable hreach h with
    ⟨hrk', hdk'⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨_, heq, _⟩ | ⟨_, heq, _⟩ | ⟨_, heq⟩
  · exact ⟨hrk', hdk'⟩
  · exact absurd (congrArg (fun t => (gamma' i S g t).shape) heq.symm)
      (leafB_shape_literal_ne_dh i S g _ _ _)
  · exact absurd (congrArg (fun t => (gamma' i S g t).shape) heq.symm)
      (leafB_shape_literal_ne_dh i S g _ _ _)
  · exact absurd (congrArg (fun t => (gamma' i S g t).shape) heq.symm)
      (leafB_shape_concat_ne_dh i S g _ _ _ _)
  · exact absurd (congrArg (fun t => (gamma' i S g t).shape) heq.symm)
      (leafB_shape_concat_ne_dh i S g _ _ _ _)
  · exact absurd (congrArg (fun t => (gamma' i S g t).shape) heq.symm)
      (leafB_shape_concat_ne_dh i S g _ _ _ _)
  · exact absurd (congrArg (fun t => (gamma' i S g t).shape) heq.symm)
      (leafB_shape_concat_ne_dh i S g _ _ _ _)

private theorem leafB_peel_hmac_pqxdhIkm
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hreach : ReachableTrace T)
    (pk sk dh2 dh3 : DY.Bytes) (dh4 : Option DY.Bytes) (ss : DY.Bytes)
    (h : (KdfExtract.kdfExtract zeroSalt
      (PQXDH.pqxdhIkm (PQXDH.agree pk sk) dh2 dh3 dh4 ss)).AttackerKnows T) :
    (PQXDH.pqxdhIkm (PQXDH.agree pk sk) dh2 dh3 dh4 ss).AttackerKnows T := by
  unfold PQXDH.pqxdhIkm PQXDH.agree at h ⊢
  rcases kdfInputValidProv_of_attackerKnows_reachable hreach h with
    ⟨_, hk'⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨_, heq, _⟩ | ⟨_, heq, _⟩ | ⟨_, heq⟩
  · exact hk'
  · exact absurd (congrArg (fun t => (gamma' i S g t).shape) heq.symm)
      (leafB_shape_literal_ne_concat i S g _ _ _)
  · exact absurd (congrArg (fun t => (gamma' i S g t).shape) heq.symm)
      (leafB_shape_literal_ne_concat i S g _ _ _)
  · exact absurd (leafB_shape_concat_inj i S g (congrArg (fun t => (gamma' i S g t).shape) heq.symm)).1
      (leafB_shape_lit_wr_ne_disc i S g)
  · exact absurd (leafB_shape_concat_inj i S g (leafB_shape_concat_inj i S g
      (congrArg (fun t => (gamma' i S g t).shape) heq.symm)).2).1
      (leafB_shape_literal_ne_dh i S g _ _ _)
  · exact absurd (leafB_shape_concat_inj i S g (leafB_shape_concat_inj i S g
      (congrArg (fun t => (gamma' i S g t).shape) heq.symm)).2).1
      (leafB_shape_literal_ne_dh i S g _ _ _)
  · exact absurd (leafB_shape_concat_inj i S g (leafB_shape_concat_inj i S g
      (congrArg (fun t => (gamma' i S g t).shape) heq.symm)).2).1
      (leafB_shape_literal_ne_dh i S g _ _ _)

private theorem leafB_peel_seed_to_rk_d_of_view_none
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {ms : List Move} {p : PreKeyFields} {x' : PreKeyRep}
    {keys' : PQXDH.HandshakeKeys} {msg' : TRSignalMsg} {seed' : DY.Bytes} {c' : RecvChain}
    (hreach : ReachableTrace (runTraceMoves r ms))
    (hkeys : bobKeys r p x' = some keys')
    (hcmk : consumeMessageKey (bobChain r keys' msg') msg'.counter = some (seed', c'))
    (hv : (DY.X25519.normalizeX25519Key x'.ek).view? DY.DiffieHellman.DhPk.SubF = none)
    (hseed_ak : seed'.AttackerKnows (runTraceMoves r ms)) :
    keys'.rk.AttackerKnows (runTraceMoves r ms) ∧
      (dh (DY.X25519.normalizeX25519Key msg'.ratchetKey) (setupSecret r 2)).AttackerKnows (runTraceMoves r ms) := by
  let T := runTraceMoves r ms
  have hseed_eq : seed' = KdfExtract.kdfExtract
      (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2
        (msg'.counter.toNat - (bobChain r keys' msg').index.toNat)) (litByte 1) :=
    (consumeMessageKey_eq_spine hcmk).1
  have hseed_ak' : (KdfExtract.kdfExtract
      (chainKeyAt (createChain keys'.rk msg'.ratchetKey (setupSecret r 2)).2
        (msg'.counter.toNat - (bobChain r keys' msg').index.toNat)) (litByte 1)).AttackerKnows T := by
    rw [← hseed_eq]; exact hseed_ak
  have hckj_ak := (leafB_peel_bobQ_of_view_none i S g hne msg' hreach hkeys hv hseed_ak'
    (.inl ⟨msg'.counter.toNat - (bobChain r keys' msg').index.toNat, true, rfl⟩)
    (leafB_no7_lit i S g (ByteArray.mk #[1]))).1
  have hcc_ak := leafB_peel_chainKeyAt_of_view_none i S g hne msg' hreach hkeys hv
    (msg'.counter.toNat - (bobChain r keys' msg').index.toNat) hckj_ak
  have hcc_ak' : (KdfExtract.kdfExtract
      (hmac keys'.rk (dh (DY.X25519.normalizeX25519Key msg'.ratchetKey) (setupSecret r 2)))
      (Concat.concat (hkdfBlock1 (hmac keys'.rk (dh (DY.X25519.normalizeX25519Key msg'.ratchetKey) (setupSecret r 2))) (lit "WhisperRatchet"))
        (Concat.concat (lit "WhisperRatchet") (litByte 2)))).AttackerKnows T := hcc_ak
  have hrkd_ak : (KdfExtract.kdfExtract keys'.rk
      (dh (DY.X25519.normalizeX25519Key msg'.ratchetKey) (setupSecret r 2))).AttackerKnows T :=
    (leafB_peel_bobQ_of_view_none i S g hne msg' hreach hkeys hv hcc_ak'
      (.inl ⟨0, false, rfl⟩)
      (leafB_no7_wr2 i S g (hkdfBlock1 (hmac keys'.rk (dh (DY.X25519.normalizeX25519Key msg'.ratchetKey) (setupSecret r 2))) (lit "WhisperRatchet")))).1
  exact leafB_peel_hmac_dh i S g hreach hrkd_ak

private theorem leafB_pqxdhIkm_swap_ek_ak
    {T : ExecTrace} (hreach : ReachableTrace T)
    (dh1 pk sk1 sk2 : DY.Bytes) (opk : Option DY.Bytes) (ss ek_x : DY.Bytes)
    (hv : (DY.X25519.normalizeX25519Key pk).view? DY.DiffieHellman.DhPk.SubF = none)
    (hek_x_ak : ek_x.AttackerKnows T)
    (hikm : (PQXDH.pqxdhIkm dh1 (PQXDH.agree pk sk1) (PQXDH.agree pk sk2)
      (opk.map (PQXDH.agree pk ·)) ss).AttackerKnows T) :
    (PQXDH.pqxdhIkm dh1 (PQXDH.agree ek_x sk1) (PQXDH.agree ek_x sk2)
      (opk.map (PQXDH.agree ek_x ·)) ss).AttackerKnows T := by
  obtain ⟨hdisc_ak, hk1⟩ := leafB_ak_split hikm
  obtain ⟨hdh1_ak, hk2⟩ := leafB_ak_split hk1
  obtain ⟨hdh2_ak, hk3⟩ := leafB_ak_split hk2
  obtain ⟨hdh3_ak, hR_ak⟩ := leafB_ak_split hk3
  have hsk1_ak : sk1.AttackerKnows T := leafB_agree_sk_ak_of_view_none hreach hv hdh2_ak
  have hsk2_ak : sk2.AttackerKnows T := leafB_agree_sk_ak_of_view_none hreach hv hdh3_ak
  have hek_x_key_ak : (DY.X25519.normalizeX25519Key ek_x).AttackerKnows T :=
    attackerKnows_x25519Key hek_x_ak
  have hdh20_ak : (PQXDH.agree ek_x sk1).AttackerKnows T :=
    DiffieHellman.attacker_knows_dh _ _ _ hek_x_key_ak hsk1_ak
  have hdh30_ak : (PQXDH.agree ek_x sk2).AttackerKnows T :=
    DiffieHellman.attacker_knows_dh _ _ _ hek_x_key_ak hsk2_ak
  cases opk with
  | none =>
    exact leafB_ak_concat hdisc_ak
      (leafB_ak_concat hdh1_ak (leafB_ak_concat hdh20_ak (leafB_ak_concat hdh30_ak hR_ak)))
  | some o =>
    obtain ⟨hdh4_ak, hss_ak⟩ := leafB_ak_split hR_ak
    have ho_ak : o.AttackerKnows T := leafB_agree_sk_ak_of_view_none hreach hv hdh4_ak
    have hdh40_ak : (PQXDH.agree ek_x o).AttackerKnows T :=
      DiffieHellman.attacker_knows_dh _ _ _ hek_x_key_ak ho_ak
    exact leafB_ak_concat hdisc_ak (leafB_ak_concat hdh1_ak (leafB_ak_concat hdh20_ak
      (leafB_ak_concat hdh30_ak (leafB_ak_concat hdh40_ak hss_ak))))

private theorem leafB_peel_seed_to_seed0_of_view_none
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {ms : List Move} {p : PreKeyFields} {x' : PreKeyRep}
    {keys' : PQXDH.HandshakeKeys} {msg' : TRSignalMsg} {seed' : DY.Bytes} {c' : RecvChain}
    (hreach : ReachableTrace (runTraceMoves r ms))
    (hkeys : bobKeys r p x' = some keys')
    (hcmk : consumeMessageKey (bobChain r keys' msg') msg'.counter = some (seed', c'))
    (hv : (DY.X25519.normalizeX25519Key x'.ek).view? DY.DiffieHellman.DhPk.SubF = none)
    (hseed_ak : seed'.AttackerKnows (runTraceMoves r ms))
    {ek_x : DY.Bytes} (hek_x_ak : ek_x.AttackerKnows (runTraceMoves r ms)) :
    ∃ opk, OpkSel r p opk ∧
      (kdfCk (chainKeyAt (createChain (bobKeysOf r { ek := ek_x, ct := x'.ct, msg := x'.msg } opk).rk
        msg'.ratchetKey (setupSecret r 2)).2 msg'.counter.toNat)).2.AttackerKnows (runTraceMoves r ms) := by
  let T := runTraceMoves r ms
  obtain ⟨opk, hsel, hkeys_eq⟩ := bobKeys_unpack r p x' keys' hkeys
  have hrk_d_pair := leafB_peel_seed_to_rk_d_of_view_none i S g hne hreach hkeys hcmk hv hseed_ak
  let ss := (PQXDH.errToOption (DY.PQKem.kemDecap (setupSecret r 4) x'.ct)).getD
    (DY.PQKem.kemRejKey (setupSecret r 4) x'.ct)
  have hrk'_eq : keys'.rk = KdfExtract.kdfExtract
      (hmac zeroSalt (PQXDH.pqxdhIkm (PQXDH.agree (setupPublic r 0) (setupSecret r 2))
        (PQXDH.agree x'.ek (setupSecret r 1))
        (PQXDH.agree x'.ek (setupSecret r 2)) (opk.map (PQXDH.agree x'.ek ·)) ss))
      (Concat.concat pqxdhLabel (litByte 1)) := by
    rw [hkeys_eq]; rfl
  have hrk'_ak : (KdfExtract.kdfExtract
      (hmac zeroSalt (PQXDH.pqxdhIkm (PQXDH.agree (setupPublic r 0) (setupSecret r 2))
        (PQXDH.agree x'.ek (setupSecret r 1))
        (PQXDH.agree x'.ek (setupSecret r 2)) (opk.map (PQXDH.agree x'.ek ·)) ss))
      (Concat.concat pqxdhLabel (litByte 1))).AttackerKnows T := by
    rw [← hrk'_eq]; exact hrk_d_pair.1
  have hprk_ak : (KdfExtract.kdfExtract zeroSalt
      (PQXDH.pqxdhIkm (PQXDH.agree (setupPublic r 0) (setupSecret r 2))
        (PQXDH.agree x'.ek (setupSecret r 1))
        (PQXDH.agree x'.ek (setupSecret r 2)) (opk.map (PQXDH.agree x'.ek ·)) ss)).AttackerKnows T :=
    (leafB_peel_bobQ_of_view_none i S g hne msg' hreach hkeys hv hrk'_ak
      (.inr hrk'_eq.symm) (leafB_no7_x1 i S g pqxdhLabel)).1
  have hikm'_ak := leafB_peel_hmac_pqxdhIkm i S g hreach (setupPublic r 0) (setupSecret r 2)
    (PQXDH.agree x'.ek (setupSecret r 1)) (PQXDH.agree x'.ek (setupSecret r 2))
    (opk.map (PQXDH.agree x'.ek ·)) ss hprk_ak
  have hikm0_ak := leafB_pqxdhIkm_swap_ek_ak hreach (PQXDH.agree (setupPublic r 0) (setupSecret r 2))
    x'.ek (setupSecret r 1) (setupSecret r 2) opk ss ek_x hv hek_x_ak hikm'_ak
  have hzero_ak : zeroSalt.AttackerKnows T := leafB_ak_lit (ByteArray.mk (Array.replicate 32 0))
  have hpq_lbl_ak : pqxdhLabel.AttackerKnows T := leafB_ak_lit _
  have hrk0_ak : (bobKeysOf r { ek := ek_x, ct := x'.ct, msg := x'.msg } opk).rk.AttackerKnows T :=
    leafB_ak_hkdfBlock1 (leafB_ak_hmac hzero_ak hikm0_ak) hpq_lbl_ak
  have hwr_lbl_ak : (lit "WhisperRatchet").AttackerKnows T := leafB_ak_lit "WhisperRatchet".toUTF8
  have hcc0_ak : (createChain (bobKeysOf r { ek := ek_x, ct := x'.ct, msg := x'.msg } opk).rk
      msg'.ratchetKey (setupSecret r 2)).2.AttackerKnows T :=
    leafB_ak_hkdfBlock2 (leafB_ak_hmac hrk0_ak hrk_d_pair.2) hwr_lbl_ak
  have hck0_ak : (chainKeyAt (createChain (bobKeysOf r { ek := ek_x, ct := x'.ct, msg := x'.msg } opk).rk
      msg'.ratchetKey (setupSecret r 2)).2 msg'.counter.toNat).AttackerKnows T :=
    attackerKnows_chainKeyAt_srk msg'.counter.toNat hcc0_ak
  have h1_ak : (litByte 1).AttackerKnows T := leafB_ak_lit (ByteArray.mk #[1])
  have hseed0_ak : (kdfCk (chainKeyAt (createChain (bobKeysOf r { ek := ek_x, ct := x'.ct, msg := x'.msg } opk).rk
      msg'.ratchetKey (setupSecret r 2)).2 msg'.counter.toNat)).2.AttackerKnows T :=
    leafB_ak_hmac hck0_ak h1_ak
  exact ⟨opk, hsel, hseed0_ak⟩

/-! ## Canonical Representation for Attacker-Known Seeds -/

set_option linter.unusedVariables false in
/-- Constructs a canonical pre-key representation `x` matching the accepted wire bytes and
decrypted plaintext when Bob's receive seed `seed'` is attacker-known. -/
theorem rpk_seed_ak_exactRep
    {interpretation : ExternInterpretation} {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    {b ct_wire pt : HwBytes} {p : PreKeyFields} {x' : PreKeyRep} {msg' : TRSignalMsg}
    {keys' : PQXDH.HandshakeKeys} {seed' salt' st'' : DY.Bytes} {c' : TripleRatchet.RecvChain}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (hpubcanon : X25519PubCanonical interpretation ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionShiftsRejected interpretation)
    (hmp : MatchedPrefix interpretation r S who g ms acc)
    (hp : parsePreKeyWire b = some p)
    (hnk : ¬ KyberMismatch interpretation r p)
    (hct_wire : p.kyberCiphertext = some (kyberKey ct_wire))
    (hct_len : ct_wire.length = 1568)
    (hopk_ok : p.preKeyId = none ∨ (r.withOpk = true ∧ p.preKeyId = some r.opkId))
    (hx' : x' ∈ preKeyRepresentations interpretation r S g ms b)
    (hnbsc : ¬ BobSessionStartCollidesOrImplicitRejects interpretation r S g ms p x')
    (hkeys : bobKeys r p x' = some keys')
    (hparse : parseTrSignalMsg x'.msg = some msg')
    (hcmk : TripleRatchet.consumeMessageKey (bobChain r keys' msg') msg'.counter = some (seed', c'))
    (hspqr : DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys'.pqr TripleRatchet.spqrB2A)
      msg'.pqRatchet (preKeySpqrIndex p) = some (st'', salt'))
    (hbss : TR.bobSaltSeed r p x' = some (salt', seed'))
    (hek_len : (gamma interpretation S g x'.ek).length = 32)
    (hek_canon : DY.X25519.leValue ((gamma interpretation S g x'.ek).map BitVec.toNat) < DY.X25519.p25519)
    (hek_notlow : DY.X25519.isLowOrderKey ((gamma interpretation S g x'.ek).map BitVec.toNat) = false ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionFree interpretation (gamma interpretation S g x'.ek))
    (hlow' : TripleRatchet.x25519LowOrder msg'.ratchetKey = false)
    (hctr'_le : msg'.counter.toNat ≤ TripleRatchet.maxForwardJumps)
    (hmac_T_gamma : gamma interpretation S g
      (TripleRatchet.computeMac (TripleRatchet.trMsgKeys salt' seed').macKey
        (PQXDH.serializedIk (setupPublic r 0))
        (PQXDH.serializedIk (setupPublic r 2)) msg'.wire) =
      gamma interpretation S g msg'.mac)
    (hdec_wire : interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
      [gamma interpretation S g msg'.ciphertext,
       gamma interpretation S g (TripleRatchet.trMsgKeys salt' seed').cipherKey,
       (gamma interpretation S g (TripleRatchet.trMsgKeys salt' seed').iv).take 16] = some pt)
    (hpq_ne : gamma interpretation S g msg'.pqRatchet ≠ [])
    (hseed_ak : seed'.AttackerKnows (runTraceMoves r ms)) :
    ∃ (x : PreKeyRep) (msg : TRSignalMsg) (salt seed pqSalt m : DY.Bytes),
      x ∈ preKeyRepresentations interpretation r S g ms b ∧
      PQXDH.isCanonicalKey x.ek = true ∧
      parseTrSignalMsg x.msg = some msg ∧
      TripleRatchet.x25519LowOrder msg.ratchetKey = false ∧
      TR.bobSaltSeed r p x = some (salt, seed) ∧
      pqSalt.AttackerKnows (runTraceMoves r ms) ∧
      msg.mac = TripleRatchet.computeMac (TripleRatchet.trMsgKeys pqSalt seed).macKey
        (PQXDH.serializedIk (setupPublic r 0))
        (PQXDH.serializedIk (setupPublic r 2)) msg.wire ∧
      PQXDH.errToOption (DY.SymEnc.symDec
        (TripleRatchet.trMsgKeys pqSalt seed).cipherKey
        (TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some m ∧
      gamma interpretation S g m = pt := by
  have hne : r.alice ≠ r.bob := hwf.1
  have hreach : ReachableTrace (runTraceMoves r ms) := hmp.2.1.2.2.1.1
  have hx'_mem := hx'
  obtain ⟨hek'_ak, _, _, _, _⟩ := hx'
  cases hv : (DY.X25519.normalizeX25519Key x'.ek).view? DY.DiffieHellman.DhPk.SubF with
  | some s =>
    have hek_key : DY.X25519.normalizeX25519Key x'.ek = DY.DiffieHellman.dhPk s.sk := by
      have hpv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF (DY.X25519.normalizeX25519Key x'.ek)
      rw [hv] at hpv
      exact hpv.symm
    let ek_x := DY.X25519.normalizeX25519Key x'.ek
    have hek_x_ak : ek_x.AttackerKnows (runTraceMoves r ms) :=
      attackerKnows_x25519Key hek'_ak
    have hek_x_gam : gamma interpretation S g ek_x = gamma interpretation S g x'.ek :=
      leaf_gamma_x25519Key_eq interpretation S g hEq hpubcanon.1 hpubcanon.2
        x'.ek s.sk hek_key hek_canon hek_notlow.2
    have hdhPk_var : (DY.DiffieHellman.dhPk s.sk).view? DY.X25519.Variant.SubF = none := by
      dsimp only [DY.DiffieHellman.dhPk]
      exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
    have hdhPk_norm : DY.X25519.normalizeX25519Key (DY.DiffieHellman.dhPk s.sk) = DY.DiffieHellman.dhPk s.sk := by
      unfold DY.X25519.normalizeX25519Key
      rw [hdhPk_var]
    have hek_x_can : PQXDH.isCanonicalKey ek_x = true := by
      dsimp only [ek_x]
      rw [hek_key]
      unfold PQXDH.isCanonicalKey PQXDH.x25519LowOrder
      rw [hdhPk_var, hdhPk_norm]
      dsimp only [DY.Literal.bytesToLiteral, DY.DiffieHellman.dhPk]
      rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _]
      rfl
    have hbss0 : TR.bobSaltSeed r p { ek := ek_x, ct := x'.ct, msg := x'.msg } = some (salt', seed') := by
      rw [← hbss]
      unfold TR.bobSaltSeed
      have hbk : TR.bobKeys r p { ek := ek_x, ct := x'.ct, msg := x'.msg } = TR.bobKeys r p x' := by
        have hkey_idem : DY.X25519.normalizeX25519Key ek_x = DY.X25519.normalizeX25519Key x'.ek := by
          dsimp only [ek_x]; rw [hek_key, hdhPk_norm]
        have hagr : ∀ sk, PQXDH.agree ek_x sk = PQXDH.agree x'.ek sk := by
          intro sk; unfold PQXDH.agree; rw [hkey_idem]
        have hbkOf : bobKeysOf r { ek := ek_x, ct := x'.ct, msg := x'.msg } = bobKeysOf r x' := by
          funext opk
          unfold bobKeysOf
          simp only [Option.map, hagr]
        rw [leafB_tr_bobKeys_eq, leafB_tr_bobKeys_eq]
        unfold bobKeys
        rw [hbkOf]
      rw [hbk]
    exact leaf_forged_exactRep_of_ek hwf hEq hmp hp hnk hct_wire hct_len hopk_ok
      hx'_mem hparse hbss hlow' hctr'_le hmac_T_gamma hdec_wire hpq_ne
      hek_x_ak hek_x_gam hek_x_can hbss0 hseed_ak
  | none =>
    let ek_x := litOf (gamma interpretation S g x'.ek)
    have hek_x_ak : ek_x.AttackerKnows (runTraceMoves r ms) :=
      TR.RecvRep.knows_litOf _ _
    have hek_x_gam : gamma interpretation S g ek_x = gamma interpretation S g x'.ek :=
      TR.RecvRep.gamma_litOf interpretation S g _
    have hek_x_can : PQXDH.isCanonicalKey ek_x = true :=
      leaf_isCanonicalKey_litOf _ hek_notlow.1
    obtain ⟨opk, hsel, hseed0_ak⟩ :=
      leafB_peel_seed_to_seed0_of_view_none interpretation S g hne hreach hkeys hcmk hv hseed_ak hek_x_ak
    let x0 : PreKeyRep := { ek := ek_x, ct := x'.ct, msg := x'.msg }
    let keys0 := bobKeysOf r x0 opk
    have hbk0 : TR.bobKeys r p x0 = some keys0 := by
      rw [leafB_tr_bobKeys_eq]
      exact leafB_bobKeys_of_opkSel hsel x0
    obtain ⟨c0, hcmk0⟩ :=
      TR.consumeMessageKey_index_zero msg'.ratchetKey
        (createChain keys0.rk msg'.ratchetKey (setupSecret r 2)).2 msg'.counter hctr'_le 2
    obtain ⟨st0, salt0, hspqr0, _⟩ :=
      TR.spqrRecv_init_b2a_of_gamma_ne_nil interpretation S g keys0.pqr msg'.pqRatchet (preKeySpqrIndex p) hpq_ne
    let seed0 := (kdfCk (chainKeyAt (createChain keys0.rk msg'.ratchetKey (setupSecret r 2)).2
      msg'.counter.toNat)).2
    have hbss0 : TR.bobSaltSeed r p x0 = some (salt0, seed0) := by
      unfold TR.bobSaltSeed TR.bobChain
      have hparse0 : parseTrSignalMsg x0.msg = some msg' := hparse
      simp only [hbk0, hparse0, Bind.bind, Option.bind, Pure.pure]
      rw [hcmk0]
      dsimp only
      rw [hspqr0]
    exact leaf_forged_exactRep_of_ek hwf hEq hmp hp hnk hct_wire hct_len hopk_ok
      hx'_mem hparse hbss hlow' hctr'_le hmac_T_gamma hdec_wire hpq_ne
      hek_x_ak hek_x_gam hek_x_can hbss0 hseed0_ak

end Symbolic.Swarm.CREF
