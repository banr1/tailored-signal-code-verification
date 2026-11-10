/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Comparse.Basic
import Comparse.Formats.Basic
import Comparse.Formats.Derived
import DY.Comparse
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.X25519
import DY.Trace.BaseAttackerKnowledge
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
import Batteries.Tactic.SeqFocus
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.Comparse.Basic
import Symbolic.DYBridge.DY.Comparse
import Symbolic.DYBridge.DY.EquationalTheory.Literal
import Symbolic.DYBridge.DY.EquationalTheory.Concat
import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.EquationalTheory.Sign
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge

/-!
# Attacker-Known Diffie-Hellman Inversion (`DhSafe`)

Defines the `DhSafe` structural invariant on reachable composed traces and proves
`dhPack_attackerKnows_inv`, `dhPk_attackerKnows_inv`, `dh_attackerKnows_inv`, and
`agree_attackerKnows_inv`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyDir KeyComponent createChain
  consumeMessageKey computeMac setRecvChain findRecvChain recvChainFor kdfCk chainKeyAt
  messageVersion x25519LowOrder maxReceiverChains)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles
  PreKeyMsgHandles pqxdhKdf opkUsedB registerIdentity registerCorruptIdentity genSignedPrekey
  genPQPrekey genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK compromiseOPK invertDH
  invertKEM)
open Symbolic.Swarm.COMPOSED.CompTermAlgebra (kemDecap_eq_some_iff)
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompPresPQXDH

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Unsealed container helpers -/

section UnsealedDhHelpers
unseal DY.Bytes

private theorem pack_inj_dh {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    {x₁ x₂ : SubF DY.Bytes} (h : BytesView.pack x₁ = BytesView.pack x₂) : x₁ = x₂ := by
  have h1 : DY.Bytes.view? (BytesView.pack x₁) SubF = some x₁ := DY.BytesView.view_pack (SubF := SubF) x₁
  have h2 : DY.Bytes.view? (BytesView.pack x₂) SubF = some x₂ := DY.BytesView.view_pack (SubF := SubF) x₂
  rw [h, h2] at h1; injection h1 with h1; exact h1.symm

private theorem symEnc_inj_dh {k₁ iv₁ m₁ k₂ iv₂ m₂ : DY.Bytes}
    (h : SymEnc.symEnc k₁ iv₁ m₁ = SymEnc.symEnc k₂ iv₂ m₂) : k₁ = k₂ ∧ iv₁ = iv₂ ∧ m₁ = m₂ := by
  have hinj : ({ key := k₁, iv := iv₁, msg := m₁ } : DY.SymEnc.Enc.SubF DY.Bytes) = { key := k₂, iv := iv₂, msg := m₂ } := pack_inj_dh h
  injection hinj with h1 h2 h3; exact ⟨h1, h2, h3⟩

private theorem concat_inj_dh {l₁ r₁ l₂ r₂ : DY.Bytes}
    (h : Concat.concat l₁ r₁ = Concat.concat l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  have hinj : ({ lhs := l₁, rhs := r₁ } : DY.Concat.Concat.SubF DY.Bytes) = { lhs := l₂, rhs := r₂ } := pack_inj_dh h
  injection hinj with h1 h2; exact ⟨h1, h2⟩

private theorem dhPk_inj_dh {sk₁ sk₂ : DY.Bytes}
    (h : DiffieHellman.dhPk sk₁ = DiffieHellman.dhPk sk₂) : sk₁ = sk₂ := by
  have hinj : ({ sk := sk₁ } : DY.DiffieHellman.DhPk.SubF DY.Bytes) = { sk := sk₂ } := pack_inj_dh h
  injection hinj

private theorem kemPk_inj_dh {sk₁ sk₂ : DY.Bytes}
    (h : PQKem.kemPk sk₁ = PQKem.kemPk sk₂) : sk₁ = sk₂ := by
  have hinj : ({ sk := sk₁ } : DY.PQKem.Pk.SubF DY.Bytes) = { sk := sk₂ } := pack_inj_dh h
  injection hinj

private theorem dh_eq_pack_dh (p s : DY.Bytes) :
    ∃ pk' sk', DiffieHellman.dh p s = ({ pk := pk', sk := sk' } : DiffieHellman.Dh.SubF DY.Bytes).pack := by
  dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh]
  split <;> [split <;> exact ⟨_, _, rfl⟩; exact ⟨_, _, rfl⟩]

private theorem spqrSend_snd_fst_eq_dh (st coins : DY.Bytes) :
    (∃ k p i, (Spqr.spqrSend st coins).2.1 = Spqr.spqrChainKey k p i) ∨
    (∃ x : Spqr.SendKey.SubF DY.Bytes, (Spqr.spqrSend st coins).2.1 = x.pack) := by
  dsimp only [Spqr.spqrSend]; split <;> [exact .inl ⟨_, _, _, rfl⟩; exact .inr ⟨_, rfl⟩]

private theorem spqrRecv_snd_eq_dh {st msg : DY.Bytes} {idx : UInt32} {r : DY.Bytes × DY.Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) :
    r.2 = Spqr.zeroKey ∨ (∃ k p i, r.2 = Spqr.spqrChainKey k p i) ∨
    (∃ x : Spqr.RecvKey.SubF DY.Bytes, r.2 = x.pack) := by
  unfold Spqr.spqrRecv at hrecv; split at hrecv; · cases hrecv
  split at hrecv <;>
    [(split at hrecv <;> [skip; cases hrecv]; injection hrecv with hr; rw [← hr]; dsimp only;
      split <;> [exact .inl rfl; exact .inr (.inl ⟨_, _, _, rfl⟩)]);
     (injection hrecv with hr; rw [← hr]; exact .inr (.inr ⟨_, rfl⟩))]

end UnsealedDhHelpers

/-! ## `DhSafe` inductive predicate and inversion lemmas -/

/-- Dh-safety: the `dh`/`dhPk` nodes reachable through the destructible spine are attacker-built
(or honest `dhPk (randTerm _ 32)`). `kdfExtract`/`trunc8` are atoms. -/
inductive DhSafe (T : ExecTrace) : DY.Bytes → Prop
  | atom {b : DY.Bytes} :
      DY.Bytes.view? b DY.DiffieHellman.DhPk.SubF = none →
      DY.Bytes.view? b DY.DiffieHellman.Dh.SubF = none →
      DY.Bytes.view? b DY.Concat.Concat.SubF = none →
      DY.Bytes.view? b DY.SymEnc.Enc.SubF = none →
      DY.Bytes.view? b DY.TrWire.TrWireMsg.SubF = none →
      DY.Bytes.view? b DY.X25519.Variant.SubF = none →
      DY.Bytes.view? b DY.Spqr.InitState.SubF = none →
      DY.Bytes.view? b DY.Spqr.SendState.SubF = none →
      DY.Bytes.view? b DY.Spqr.RecvState.SubF = none →
      DY.Bytes.view? b DY.PQKem.Pk.SubF = none →
      DhSafe T b
  | dhPk {sk : DY.Bytes} :
      DhSafe T sk → (sk.AttackerKnows T ∨ ∃ n, sk = randTerm n 32) →
      DhSafe T (DiffieHellman.dhPk sk)
  | kemPk {sk : DY.Bytes} :
      DhSafe T sk → DhSafe T (PQKem.kemPk sk)
  | dh (x : DiffieHellman.Dh.SubF DY.Bytes) :
      (∃ p0 s0, x.pack = DiffieHellman.dh p0 s0 ∧ p0.AttackerKnows T ∧ s0.AttackerKnows T) →
      DhSafe T x.pack
  | concat {l r : DY.Bytes} :
      DhSafe T l → DhSafe T r → DhSafe T (Concat.concat l r)
  | symEnc {k iv m : DY.Bytes} :
      DhSafe T m → DhSafe T (SymEnc.symEnc k iv m)
  | trWireMsg (x : TrWire.TrWireMsg.SubF DY.Bytes) :
      DhSafe T x.senderRatchetKey → DhSafe T x.ciphertext → DhSafe T x.pqRatchet →
      DhSafe T x.pack
  | variant (x : X25519.Variant.SubF DY.Bytes) :
      DhSafe T x.key → DhSafe T x.pack
  | spqrInit (x : Spqr.InitState.SubF DY.Bytes) :
      DhSafe T x.authKey → DhSafe T x.params → DhSafe T x.pack
  | spqrSendState (x : Spqr.SendState.SubF DY.Bytes) :
      DhSafe T x.st → DhSafe T x.coins → DhSafe T x.pack
  | spqrRecvState (x : Spqr.RecvState.SubF DY.Bytes) :
      DhSafe T x.st → DhSafe T x.msg → DhSafe T x.pack

section UnsealedDhSafeLemmas
unseal DY.Bytes

theorem dhSafe_random (T : ExecTrace) (r : DY.Random.SubF DY.Bytes) :
    DhSafe T (DY.Random.Random.pack r) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem dhSafe_literal (T : ExecTrace) (b : ByteArray) :
    DhSafe T (Literal.literalToBytes b) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem dhSafe_kdfExtract (T : ExecTrace) (s i : DY.Bytes) :
    DhSafe T (KdfExtract.kdfExtract s i) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem dhSafe_trunc8 (T : ExecTrace) (inp : DY.Bytes) :
    DhSafe T (Trunc.trunc8 inp) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem dhSafe_kemEncap_fst (T : ExecTrace) (pk e : DY.Bytes) :
    DhSafe T (PQKem.kemEncap pk e).1 := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem dhSafe_kemEncap_snd (T : ExecTrace) (pk e : DY.Bytes) :
    DhSafe T (PQKem.kemEncap pk e).2 := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

private theorem dhSafe_kemRejKey (T : ExecTrace) (sk ct : DY.Bytes) :
    DhSafe T (PQKem.kemRejKey sk ct) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem dhSafe_vk (T : ExecTrace) (sk : DY.Bytes) :
    DhSafe T (Signature.vk sk) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem dhSafe_sign (T : ExecTrace) (sk m r : DY.Bytes) :
    DhSafe T (Signature.sign sk m r) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem dhSafe_spqrChainKey (T : ExecTrace) (k p i : DY.Bytes) :
    DhSafe T (Spqr.spqrChainKey k p i) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem dhSafe_spqrSend_state {T : ExecTrace} {st coins : DY.Bytes}
    (hst : DhSafe T st) (hc : DhSafe T coins) :
    DhSafe T (Spqr.spqrSend st coins).1 :=
  DhSafe.spqrSendState { st := st, coins := coins } hst hc

theorem dhSafe_spqrSend_key (T : ExecTrace) (st coins : DY.Bytes) :
    DhSafe T (Spqr.spqrSend st coins).2.1 := by
  rcases spqrSend_snd_fst_eq_dh st coins with ⟨k, p, i, heq⟩ | ⟨x, heq⟩ <;> rw [heq]
  · exact dhSafe_spqrChainKey T k p i
  · refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem dhSafe_spqrSend_msg (T : ExecTrace) (st coins : DY.Bytes) :
    DhSafe T (Spqr.spqrSend st coins).2.2 := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem dhSafe_spqrRecv_state {T : ExecTrace} {st msg : DY.Bytes} {idx : UInt32} {r : DY.Bytes × DY.Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) (hst : DhSafe T st) (hmsg : DhSafe T msg) :
    DhSafe T r.1 := by
  rw [Spqr.spqrRecv_state st msg idx r hrecv]
  exact DhSafe.spqrRecvState { st := st, msg := msg } hst hmsg

theorem dhSafe_spqrRecv_key {T : ExecTrace} {st msg : DY.Bytes} {idx : UInt32} {r : DY.Bytes × DY.Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) :
    DhSafe T r.2 := by
  rcases spqrRecv_snd_eq_dh hrecv with heq | ⟨k, p, i, heq⟩ | ⟨x, heq⟩ <;> rw [heq]
  · exact dhSafe_literal T _
  · exact dhSafe_spqrChainKey T k p i
  · refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem dhSafe_dhPk_iff {T : ExecTrace} (sk : DY.Bytes) :
    DhSafe T (DiffieHellman.dhPk sk) ↔ DhSafe T sk ∧ (sk.AttackerKnows T ∨ ∃ n, sk = randTerm n 32) := by
  refine ⟨fun hs => ?_, fun ⟨hsk, h⟩ => DhSafe.dhPk hsk h⟩
  generalize hx : DiffieHellman.dhPk sk = x at hs
  have hview : DY.Bytes.view? x DY.DiffieHellman.DhPk.SubF = some { sk := sk } :=
    hx ▸ DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := sk }
  cases hs
  case atom hdp _ _ _ _ _ _ _ _ _ => rw [hdp] at hview; contradiction
  case dhPk hsk h => have heq := dhPk_inj_dh hx; subst heq; exact ⟨hsk, h⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem dhSafe_kemPk_iff {T : ExecTrace} (sk : DY.Bytes) :
    DhSafe T (PQKem.kemPk sk) ↔ DhSafe T sk := by
  refine ⟨fun hs => ?_, DhSafe.kemPk⟩
  generalize hx : PQKem.kemPk sk = x at hs
  have hview : DY.Bytes.view? x DY.PQKem.Pk.SubF = some { sk := sk } :=
    hx ▸ DY.BytesView.view_pack (SubF := DY.PQKem.Pk.SubF) { sk := sk }
  cases hs
  case atom _ _ _ _ _ _ _ _ _ hkp => rw [hkp] at hview; contradiction
  case kemPk h => have hsk := kemPk_inj_dh hx; subst hsk; exact h
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem dhSafe_dh_iff {T : ExecTrace} (d : DiffieHellman.Dh.SubF DY.Bytes) :
    DhSafe T d.pack ↔ (∃ p0 s0, d.pack = DiffieHellman.dh p0 s0 ∧ p0.AttackerKnows T ∧ s0.AttackerKnows T) := by
  refine ⟨fun hs => ?_, DhSafe.dh d⟩
  generalize hx : d.pack = x at hs
  have hview : DY.Bytes.view? x DY.DiffieHellman.Dh.SubF = some d :=
    hx ▸ DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) d
  cases hs
  case atom _ hd _ _ _ _ _ _ _ _ => rw [hd] at hview; contradiction
  case dh d' h => have hd := pack_inj_dh hx; subst hd; exact h
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem dhSafe_concat_iff {T : ExecTrace} (l r : DY.Bytes) :
    DhSafe T (Concat.concat l r) ↔ DhSafe T l ∧ DhSafe T r := by
  refine ⟨fun hs => ?_, fun ⟨hl, hr⟩ => DhSafe.concat hl hr⟩
  generalize hx : Concat.concat l r = x at hs
  have hview : DY.Bytes.view? x DY.Concat.Concat.SubF = some { lhs := l, rhs := r } :=
    hx ▸ DY.BytesView.view_pack (SubF := DY.Concat.Concat.SubF) { lhs := l, rhs := r }
  cases hs
  case atom _ _ hc _ _ _ _ _ _ _ => rw [hc] at hview; contradiction
  case concat hl hr => obtain ⟨hl', hr'⟩ := concat_inj_dh hx; subst hl'; subst hr'; exact ⟨hl, hr⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem dhSafe_symEnc_iff {T : ExecTrace} (k iv m : DY.Bytes) :
    DhSafe T (SymEnc.symEnc k iv m) ↔ DhSafe T m := by
  refine ⟨fun hs => ?_, DhSafe.symEnc⟩
  generalize hx : SymEnc.symEnc k iv m = x at hs
  have hview : DY.Bytes.view? x DY.SymEnc.Enc.SubF = some { key := k, iv := iv, msg := m } :=
    hx ▸ DY.BytesView.view_pack (SubF := DY.SymEnc.Enc.SubF) { key := k, iv := iv, msg := m }
  cases hs
  case atom _ _ _ he _ _ _ _ _ _ => rw [he] at hview; contradiction
  case symEnc hm => obtain ⟨_, _, hm'⟩ := symEnc_inj_dh hx; subst hm'; exact hm
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem dhSafe_trWireMsg_iff {T : ExecTrace} (w : TrWire.TrWireMsg.SubF DY.Bytes) :
    DhSafe T w.pack ↔ DhSafe T w.senderRatchetKey ∧ DhSafe T w.ciphertext ∧ DhSafe T w.pqRatchet := by
  refine ⟨fun hs => ?_, fun ⟨h1, h2, h3⟩ => DhSafe.trWireMsg w h1 h2 h3⟩
  generalize hx : w.pack = x at hs
  have hview : DY.Bytes.view? x DY.TrWire.TrWireMsg.SubF = some w :=
    hx ▸ DY.BytesView.view_pack (SubF := DY.TrWire.TrWireMsg.SubF) w
  cases hs
  case atom _ _ _ _ htw _ _ _ _ _ => rw [htw] at hview; contradiction
  case trWireMsg w' h1 h2 h3 => have hw := pack_inj_dh hx; subst hw; exact ⟨h1, h2, h3⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem dhSafe_variant_iff {T : ExecTrace} (v : X25519.Variant.SubF DY.Bytes) :
    DhSafe T v.pack ↔ DhSafe T v.key := by
  refine ⟨fun hs => ?_, DhSafe.variant v⟩
  generalize hx : v.pack = x at hs
  have hview : DY.Bytes.view? x DY.X25519.Variant.SubF = some v :=
    hx ▸ DY.BytesView.view_pack (SubF := DY.X25519.Variant.SubF) v
  cases hs
  case atom _ _ _ _ _ hv _ _ _ _ => rw [hv] at hview; contradiction
  case variant v' hk => have hv := pack_inj_dh hx; subst hv; exact hk
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem dhSafe_spqrInit_iff {T : ExecTrace} (x : Spqr.InitState.SubF DY.Bytes) :
    DhSafe T x.pack ↔ DhSafe T x.authKey ∧ DhSafe T x.params := by
  refine ⟨fun hs => ?_, fun ⟨hk, hp⟩ => DhSafe.spqrInit x hk hp⟩
  generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.InitState.SubF = some x :=
    hx ▸ DY.BytesView.view_pack (SubF := DY.Spqr.InitState.SubF) x
  cases hs
  case atom _ _ _ _ _ _ hi _ _ _ => rw [hi] at hview; contradiction
  case spqrInit x' hk hp => have hx' := pack_inj_dh hx; subst hx'; exact ⟨hk, hp⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem dhSafe_spqrSendState_iff {T : ExecTrace} (x : Spqr.SendState.SubF DY.Bytes) :
    DhSafe T x.pack ↔ DhSafe T x.st ∧ DhSafe T x.coins := by
  refine ⟨fun hs => ?_, fun ⟨hst, hc⟩ => DhSafe.spqrSendState x hst hc⟩
  generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.SendState.SubF = some x :=
    hx ▸ DY.BytesView.view_pack (SubF := DY.Spqr.SendState.SubF) x
  cases hs
  case atom _ _ _ _ _ _ _ hs' _ _ => rw [hs'] at hview; contradiction
  case spqrSendState x' hst hc => have hx' := pack_inj_dh hx; subst hx'; exact ⟨hst, hc⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem dhSafe_spqrRecvState_iff {T : ExecTrace} (x : Spqr.RecvState.SubF DY.Bytes) :
    DhSafe T x.pack ↔ DhSafe T x.st ∧ DhSafe T x.msg := by
  refine ⟨fun hs => ?_, fun ⟨hst, hm⟩ => DhSafe.spqrRecvState x hst hm⟩
  generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.RecvState.SubF = some x :=
    hx ▸ DY.BytesView.view_pack (SubF := DY.Spqr.RecvState.SubF) x
  cases hs
  case atom _ _ _ _ _ _ _ _ hr _ => rw [hr] at hview; contradiction
  case spqrRecvState x' hst hm => have hx' := pack_inj_dh hx; subst hx'; exact ⟨hst, hm⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem dhSafe_dh_pack_inv {T : ExecTrace} {pk₀ sk₀ : DY.Bytes}
    (h : DhSafe T (({ pk := pk₀, sk := sk₀ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)) :
    (pk₀.AttackerKnows T ∧ sk₀.AttackerKnows T) ∨
    (∃ c : DY.Bytes, pk₀ = DiffieHellman.dhPk c ∧ c.AttackerKnows T ∧ (DiffieHellman.dhPk sk₀).AttackerKnows T) := by
  obtain ⟨p0, s0, heq, hp0_ak, hs0_ak⟩ := (dhSafe_dh_iff { pk := pk₀, sk := sk₀ }).mp h
  unfold DiffieHellman.CanDH.dh instCanDHBytes at heq; dsimp only at heq
  have hpack := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF p0
  rcases hv : p0.view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a0⟩⟩
  · rw [hv] at heq; dsimp only at heq
    have hinj := pack_inj_dh heq; injection hinj with h1 h2; subst h1; subst h2
    exact .inl ⟨hp0_ak, hs0_ak⟩
  · rw [hv] at hpack heq; dsimp only at hpack heq
    split at heq <;>
      (have hinj := pack_inj_dh heq; injection hinj with h1 h2; subst h1; subst h2; rw [← hpack] at hp0_ak) <;>
      [exact .inl ⟨hp0_ak, hs0_ak⟩; exact .inr ⟨s0, rfl, hs0_ak, hp0_ak⟩]

theorem dhSafe_dh_inv {T : ExecTrace} {pk sk : DY.Bytes}
    (h : DhSafe T (DiffieHellman.dh pk sk)) :
    (pk.AttackerKnows T ∧ sk.AttackerKnows T) ∨
    (∃ c : DY.Bytes, pk = DiffieHellman.dhPk c ∧ c.AttackerKnows T ∧ (DiffieHellman.dhPk sk).AttackerKnows T) := by
  unfold DiffieHellman.CanDH.dh instCanDHBytes at h; dsimp only at h
  have hpack := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk
  rcases hv : pk.view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a⟩⟩
  · rw [hv] at h; dsimp only at h
    exact dhSafe_dh_pack_inv h
  · rw [hv] at hpack h; dsimp only at hpack h
    have hpk_eq : pk = dhPk a := hpack.symm
    split at h
    · rcases dhSafe_dh_pack_inv h with ⟨hpk_ak, hsk_ak⟩ | ⟨s0, hs0_eq, hs0_ak, hdhPk_sk_ak⟩
      · exact .inl ⟨hpk_eq ▸ hpk_ak, hsk_ak⟩
      · exact .inr ⟨s0, hpk_eq.trans hs0_eq, hs0_ak, hdhPk_sk_ak⟩
    · rcases dhSafe_dh_pack_inv h with ⟨hdhPk_sk_ak, ha_ak⟩ | ⟨s0, hs0_eq, hs0_ak, hdhPk_a_ak⟩
      · exact .inr ⟨a, hpk_eq, ha_ak, hdhPk_sk_ak⟩
      · have hsk_eq : sk = s0 := dhPk_inj_dh hs0_eq
        exact .inl ⟨hpk_eq ▸ hdhPk_a_ak, hsk_eq ▸ hs0_ak⟩

end UnsealedDhSafeLemmas

theorem dhSafe_x25519Key {T : ExecTrace} {pk : DY.Bytes} (h : DhSafe T pk) :
    DhSafe T (X25519.normalizeX25519Key pk) := by
  unfold X25519.normalizeX25519Key; have hpack := DY.Bytes.pack_view? X25519.Variant.SubF pk
  rcases hv : pk.view? X25519.Variant.SubF with _ | x; · exact h
  rw [hv] at hpack; dsimp only at hpack; rw [← hpack] at h
  exact (dhSafe_variant_iff x).mp h

theorem dhSafe_x25519TorsionVariant {T : ExecTrace} {key : DY.Bytes} (v : Fin 4) (t : Fin 8 := 0)
    (h : DhSafe T key) : DhSafe T (X25519.x25519TorsionVariant key v t) := by
  dsimp only [X25519.x25519TorsionVariant]
  split
  · exact dhSafe_x25519Key h
  · exact DhSafe.variant { key := X25519.normalizeX25519Key key, variation := v, torsion := t } (dhSafe_x25519Key h)

/-! ## Closure of `DhSafe` under `AttackerKnows` -/

set_option maxHeartbeats 400000 in
theorem attackerKnows_imp_dhSafe {tr T : ExecTrace} (hle : tr ≤ T)
    (h_base : ∀ msg, Trace.BaseAttackerKnows tr msg → DhSafe T msg)
    {b : DY.Bytes} (hak : b.AttackerKnows tr) : DhSafe T b := by
  suffices h : b.AttackerKnows tr ∧ DhSafe T b from h.2
  refine DY.Bytes.AttackerKnows.is_least_fixpoint (fun x => x.AttackerKnows tr ∧ DhSafe T x) b tr ?_ ?_ hak
  · change SubAttackerKnowledge.Implies DY.Libsignal.Composed.attackerKnowledge (fun x => x.AttackerKnows tr ∧ DhSafe T x)
    dsimp [DY.Libsignal.Composed.attackerKnowledge]; apply SubAttackerKnowledge.combine.implies
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, _⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Random.attackerKnowledge]
      intro x hx; rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at hx; exact hx.elim
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Literal.attackerKnowledge]
      apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | n, _⟩ <;> [skip; omega]
      intro x hx; dsimp [Literal.attackerKnowledge.internal] at hx
      rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at hx
      rcases hx with ⟨bs, rfl⟩; exact ⟨Literal.attacker_knows_literalToBytes bs tr, dhSafe_literal T bs⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Concat.attackerKnowledge]
      apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | n, _⟩ <;> try omega
      · intro x hx; dsimp [Concat.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at hx
        rcases hx with ⟨lhs, rhs, rfl, ⟨hl_ak, hl_s⟩, ⟨hr_ak, hr_s⟩⟩
        exact ⟨Concat.attacker_knows_concat lhs rhs tr hl_ak hr_ak, DhSafe.concat hl_s hr_s⟩
      · intro x hx; dsimp [Concat.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at hx
        rcases hx with ⟨inp, rhs, i, hsplit, ⟨hinp_ak, hinp_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Concat.splitLeft.attackerKnowledge x tr
          (by rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred]; exact ⟨inp, rhs, i, hsplit, hinp_ak⟩),
          ((dhSafe_concat_iff x rhs).mp (Concat.concat_split inp i x rhs hsplit.symm ▸ hinp_s)).1⟩
      · intro x hx; dsimp [Concat.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hx
        rcases hx with ⟨inp, lhs, i, hsplit, ⟨hinp_ak, hinp_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Concat.splitRight.attackerKnowledge x tr
          (by rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred]; exact ⟨inp, lhs, i, hsplit, hinp_ak⟩),
          ((dhSafe_concat_iff lhs x).mp (Concat.concat_split inp i lhs x hsplit.symm ▸ hinp_s)).2⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DiffieHellman.attackerKnowledge]
      apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
      · intro x hx; dsimp [DiffieHellman.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hx
        rcases hx with ⟨sk, rfl, ⟨hsk_ak, hsk_s⟩⟩
        exact ⟨DiffieHellman.attacker_knows_dhPk sk tr hsk_ak,
          DhSafe.dhPk hsk_s (.inl (DY.Bytes.AttackerKnows_le sk tr T hle hsk_ak))⟩
      · intro x hx; dsimp [DiffieHellman.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hx
        rcases hx with ⟨pk, sk, rfl, ⟨hpk_ak, _⟩, ⟨hsk_ak, _⟩⟩
        obtain ⟨p₀, s₀, hdheq⟩ := dh_eq_pack_dh pk sk
        refine ⟨DiffieHellman.attacker_knows_dh pk sk tr hpk_ak hsk_ak, ?_⟩; rw [hdheq]
        exact DhSafe.dh { pk := p₀, sk := s₀ }
          ⟨pk, sk, hdheq.symm, DY.Bytes.AttackerKnows_le pk tr T hle hpk_ak, DY.Bytes.AttackerKnows_le sk tr T hle hsk_ak⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, KdfExtract.attackerKnowledge]
      apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | n, _⟩ <;> [skip; omega]
      intro x hx; dsimp [KdfExtract.attackerKnowledge.internal] at hx
      rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hx
      rcases hx with ⟨salt, ikm, rfl, ⟨hs_ak, _⟩, ⟨hi_ak, _⟩⟩
      exact ⟨KdfExtract.attacker_knows_kdfExtract salt ikm tr hs_ak hi_ak, dhSafe_kdfExtract T salt ikm⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, SymEnc.attackerKnowledge]
      apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
      · rintro x ⟨k, iv, msg, rfl, ⟨hk_ak, _⟩, ⟨hiv_ak, _⟩, ⟨hm_ak, hm_s⟩⟩
        exact ⟨SymEnc.attacker_knows_symEnc k iv msg tr hk_ak hiv_ak hm_ak, DhSafe.symEnc hm_s⟩
      · rintro x ⟨key, iv, ct, hdec, ⟨hk_ak, _⟩, ⟨hiv_ak, _⟩, ⟨hct_ak, hct_s⟩⟩
        have heq := SymEnc.symDec_eq_some key iv ct x hdec.symm; rw [heq] at hct_s
        exact ⟨SymEnc.attacker_knows_symDec key iv ct x tr hk_ak hiv_ak hct_ak hdec.symm,
          (dhSafe_symEnc_iff key iv x).mp hct_s⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Trunc.attackerKnowledge]
      apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | n, _⟩ <;> [skip; omega]
      rintro x ⟨m, rfl, ⟨hm_ak, _⟩⟩; exact ⟨Trunc.attacker_knows_trunc8 m tr hm_ak, dhSafe_trunc8 T m⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, X25519.attackerKnowledge]
      apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
      · rintro x ⟨key, v, t, rfl, ⟨hk_ak, hk_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove X25519.x25519Variant.attackerKnowledge _ tr ⟨key, v, t, rfl, hk_ak⟩,
          dhSafe_x25519TorsionVariant v t hk_s⟩
      · rintro x ⟨v, ⟨hv_ak, hv_s⟩, rfl⟩
        exact ⟨DY.Bytes.AttackerKnows.prove X25519.normalizeX25519Key.attackerKnowledge _ tr ⟨v, hv_ak, rfl⟩,
          (dhSafe_variant_iff v).mp hv_s⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, PQKem.attackerKnowledge]
      apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | _ | _ | n, _⟩ <;> try omega
      · rintro x ⟨sk, rfl, ⟨hsk_ak, hsk_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove PQKem.kemPk.attackerKnowledge _ tr ⟨sk, rfl, hsk_ak⟩, DhSafe.kemPk hsk_s⟩
      · rintro x ⟨pk, e, rhs, heq, ⟨hpk_ak, _⟩, ⟨he_ak, _⟩⟩
        refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemEncapCipher.attackerKnowledge x tr ⟨pk, e, rhs, heq, hpk_ak, he_ak⟩, ?_⟩
        have h1 : x = (PQKem.kemEncap pk e).1 := congrArg Prod.fst heq; rw [h1]; exact dhSafe_kemEncap_fst T pk e
      · rintro x ⟨pk, e, lhs, heq, ⟨hpk_ak, _⟩, ⟨he_ak, _⟩⟩
        refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemEncapSS.attackerKnowledge x tr ⟨pk, e, lhs, heq, hpk_ak, he_ak⟩, ?_⟩
        have h2 : x = (PQKem.kemEncap pk e).2 := congrArg Prod.snd heq; rw [h2]; exact dhSafe_kemEncap_snd T pk e
      · rintro x ⟨sk, ct, hdec, ⟨hsk_ak, _⟩, ⟨hct_ak, _⟩⟩
        refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemDecap.attackerKnowledge x tr ⟨sk, ct, hdec, hsk_ak, hct_ak⟩, ?_⟩
        obtain ⟨e, _, rfl⟩ := Symbolic.Swarm.COMPOSED.CompTermAlgebra.kemDecap_eq_some_iff.mp hdec.symm
        exact dhSafe_kemEncap_snd T (PQKem.kemPk sk) e
      · rintro x ⟨sk, ct, rfl, ⟨hsk_ak, _⟩, ⟨hct_ak, _⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove PQKem.kemRejKey.attackerKnowledge _ tr ⟨sk, ct, rfl, hsk_ak, hct_ak⟩,
          dhSafe_kemRejKey T sk ct⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Signature.attackerKnowledge]
      apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
      · intro x hx; dsimp [Signature.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hx
        rcases hx with ⟨sk, rfl, ⟨hsk_ak, _⟩⟩
        exact ⟨Signature.attacker_knows_vk sk tr hsk_ak, dhSafe_vk T sk⟩
      · intro x hx; dsimp [Signature.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hx
        rcases hx with ⟨sk, m, r, rfl, ⟨hsk_ak, _⟩, ⟨hm_ak, _⟩, ⟨hr_ak, _⟩⟩
        exact ⟨Signature.attacker_knows_sign sk m r tr hsk_ak hm_ak hr_ak, dhSafe_sign T sk m r⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Spqr.attackerKnowledge]
      apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, _⟩ <;> try omega
      · rintro x ⟨authKey, params, rfl, ⟨hk_ak, hk_s⟩, ⟨hp_ak, hp_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrInit.attackerKnowledge _ tr ⟨authKey, params, rfl, hk_ak, hp_ak⟩,
          DhSafe.spqrInit { authKey := authKey, params := params } hk_s hp_s⟩
      · rintro x ⟨authKey, params, idx, rfl, ⟨hk_ak, _⟩, ⟨hp_ak, _⟩, ⟨hi_ak, _⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrChainKey.attackerKnowledge _ tr ⟨authKey, params, idx, rfl, hk_ak, hp_ak, hi_ak⟩,
          dhSafe_spqrChainKey T authKey params idx⟩
      · rintro x ⟨st, coins, rfl, ⟨hst_ak, hst_s⟩, ⟨hc_ak, hc_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendState.attackerKnowledge _ tr ⟨st, coins, rfl, hst_ak, hc_ak⟩,
          dhSafe_spqrSend_state hst_s hc_s⟩
      · rintro x ⟨st, coins, rfl, ⟨hst_ak, _⟩, ⟨hc_ak, _⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendKey.attackerKnowledge _ tr ⟨st, coins, rfl, hst_ak, hc_ak⟩,
          dhSafe_spqrSend_key T st coins⟩
      · rintro x ⟨st, coins, rfl, ⟨hst_ak, _⟩, ⟨hc_ak, _⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendMsg.attackerKnowledge _ tr ⟨st, coins, rfl, hst_ak, hc_ak⟩,
          dhSafe_spqrSend_msg T st coins⟩
      · rintro x ⟨st, msg, idx, r, hrecv, rfl, ⟨hst_ak, hst_s⟩, ⟨hm_ak, hm_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrRecvState.attackerKnowledge _ tr ⟨st, msg, idx, r, hrecv, rfl, hst_ak, hm_ak⟩,
          dhSafe_spqrRecv_state hrecv hst_s hm_s⟩
      · rintro x ⟨st, msg, idx, r, hrecv, rfl, ⟨hst_ak, _⟩, ⟨hm_ak, _⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrRecvKey.attackerKnowledge _ tr ⟨st, msg, idx, r, hrecv, rfl, hst_ak, hm_ak⟩,
          dhSafe_spqrRecv_key hrecv⟩
      · rintro x (⟨s, ⟨hs_ak, hs_s⟩, harg⟩ | ⟨s, ⟨hs_ak, hs_s⟩, harg⟩ | ⟨s, ⟨hs_ak, hs_s⟩, harg⟩)
        · have hargs := (dhSafe_spqrInit_iff s).mp hs_s
          refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge x tr (.inl ⟨s, hs_ak, harg⟩), ?_⟩
          rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
        · have hargs := (dhSafe_spqrSendState_iff s).mp hs_s
          refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge x tr (.inr (.inl ⟨s, hs_ak, harg⟩)), ?_⟩
          rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
        · have hargs := (dhSafe_spqrRecvState_iff s).mp hs_s
          refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge x tr (.inr (.inr ⟨s, hs_ak, harg⟩)), ?_⟩
          rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, TrWire.attackerKnowledge]
      apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
      · rintro x ⟨w, rfl, ⟨h1_ak, h1_s⟩, ⟨h2_ak, h2_s⟩, ⟨h3_ak, h3_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove TrWire.trWireMsg.attackerKnowledge _ tr ⟨w, rfl, h1_ak, h2_ak, h3_ak⟩,
          DhSafe.trWireMsg w h1_s h2_s h3_s⟩
      · rintro x ⟨w, ⟨hw_ak, hw_s⟩, hmem⟩; have hargs_s := (dhSafe_trWireMsg_iff w).mp hw_s
        refine ⟨DY.Bytes.AttackerKnows.prove TrWire.trWireMsgArg.attackerKnowledge x tr ⟨w, hw_ak, hmem⟩, ?_⟩
        rcases hmem with rfl | rfl | rfl
        exacts [hargs_s.1, hargs_s.2.1, hargs_s.2.2]
    · omega
  · intro x hx
    simp [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hx
    exact ⟨DY.Bytes.AttackerKnows.prove_from_base x tr hx, h_base x hx⟩

/-! ## Monotonicity, key-schedule helpers, and `DhSafeCoreInv` preservation -/

theorem DhSafe.mono {T T' : ExecTrace} (hle : T ≤ T') {b : DY.Bytes}
    (h : DhSafe T b) : DhSafe T' b := by
  induction h with
  | atom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact .atom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | dhPk _ h ih =>
    exact .dhPk ih (h.imp (fun hak => DY.Bytes.AttackerKnows_le _ T T' hle hak) id)
  | kemPk _ ih => exact .kemPk ih
  | dh x h =>
    obtain ⟨p0, s0, heq, hp0, hs0⟩ := h
    exact .dh x ⟨p0, s0, heq, DY.Bytes.AttackerKnows_le _ T T' hle hp0, DY.Bytes.AttackerKnows_le _ T T' hle hs0⟩
  | concat _ _ ih1 ih2 => exact .concat ih1 ih2
  | symEnc _ ih => exact .symEnc ih
  | trWireMsg x _ _ _ ih1 ih2 ih3 => exact .trWireMsg x ih1 ih2 ih3
  | variant x _ ih => exact .variant x ih
  | spqrInit x _ _ ih1 ih2 => exact .spqrInit x ih1 ih2
  | spqrSendState x _ _ ih1 ih2 => exact .spqrSendState x ih1 ih2
  | spqrRecvState x _ _ ih1 ih2 => exact .spqrRecvState x ih1 ih2

theorem dhSafe_dhPk_rand (T : ExecTrace) (t : Nat) :
    DhSafe T (DiffieHellman.dhPk (randTerm t 32)) :=
  .dhPk (dhSafe_random T { timestamp := t, size := 32 }) (.inr ⟨t, rfl⟩)

theorem dhSafe_kdfCk_fst (T : ExecTrace) (ck : DY.Bytes) :
    DhSafe T (kdfCk ck).1 := dhSafe_kdfExtract T _ _
theorem dhSafe_kdfCk_snd (T : ExecTrace) (ck : DY.Bytes) :
    DhSafe T (kdfCk ck).2 := dhSafe_kdfExtract T _ _
theorem dhSafe_createChain_fst (T : ExecTrace) (rk pk sk : DY.Bytes) :
    DhSafe T (createChain rk pk sk).1 := dhSafe_kdfExtract T _ _
theorem dhSafe_createChain_snd (T : ExecTrace) (rk pk sk : DY.Bytes) :
    DhSafe T (createChain rk pk sk).2 := dhSafe_kdfExtract T _ _
theorem dhSafe_pqxdhKdf_ck (T : ExecTrace) (ikm : DY.Bytes) :
    DhSafe T (pqxdhKdf ikm).ck := dhSafe_kdfExtract T _ _
theorem dhSafe_pqxdhKdf_pqr (T : ExecTrace) (ikm : DY.Bytes) :
    DhSafe T (pqxdhKdf ikm).pqr := dhSafe_kdfExtract T _ _

theorem dhSafe_chainKeyAt_succ {T : ExecTrace} {ck0 x : DY.Bytes} {n : Nat}
    (hx : x = chainKeyAt ck0 (n + 1)) : DhSafe T x := by
  subst hx
  rw [Symbolic.Swarm.COMPOSED.CompTermAlgebra.chainKeyAt_succ_eq_kdfCk_fst]
  exact dhSafe_kdfCk_fst T _

theorem dhSafe_of_eq_chainKeyAt_createChain_snd {T : ExecTrace} {rk pk sk x : DY.Bytes} {n : Nat}
    (hx : x = chainKeyAt (createChain rk pk sk).2 n) : DhSafe T x := by
  cases n with
  | zero => subst hx; exact dhSafe_createChain_snd T rk pk sk
  | succ n => exact dhSafe_chainKeyAt_succ hx

theorem dhSafe_of_eq_chainKeyAt_pqxdhKdf_ck {T : ExecTrace} {ikm x : DY.Bytes} {n : Nat}
    (hx : x = chainKeyAt (pqxdhKdf ikm).ck n) : DhSafe T x := by
  cases n with
  | zero => subst hx; exact dhSafe_pqxdhKdf_ck T ikm
  | succ n => exact dhSafe_chainKeyAt_succ hx

theorem dhSafe_trHonestWireMsg {T : ExecTrace} {rk ct pqMsg : DY.Bytes} (ns pn : UInt32)
    (hrk : DhSafe T rk) (hct : DhSafe T ct) (hpq : DhSafe T pqMsg) :
    DhSafe T (trHonestWireMsg rk ns pn ct pqMsg) :=
  .trWireMsg
    { version := messageVersion, senderRatchetKey := rk, counter := ns,
      previousCounter := pn, ciphertext := ct, pqRatchet := pqMsg,
      encodingVariation := DY.TrWire.canonicalVariation }
    hrk hct hpq

theorem dhSafe_computeMac_honest (T : ExecTrace) (pqSalt seed myIk peerIk a : DY.Bytes)
    (ns pn : UInt32) (m pqMsg : DY.Bytes) :
    DhSafe T (computeMac (trMsgKeys pqSalt seed).macKey myIk peerIk
      (trHonestWireMsg (dhPk a) ns pn
        (SymEnc.symEnc (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv m) pqMsg)) :=
  dhSafe_trunc8 T _

structure DhSafeCoreInv (tr : ExecTrace) : Prop where
  baseSafe : ∀ b, tr.BaseAttackerKnows b → DhSafe tr b
  spqrSafe : ∀ me st idx, TRStoredAt tr me st idx → DhSafe tr st.spqr

theorem dhSafeCoreInv_nil : DhSafeCoreInv Trace.nil :=
  { baseSafe := fun b h => False.elim (Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1 b ▸ h)
    spqrSafe := fun _ _ _ h => by
      unfold TRStoredAt at h; rw [Trace.at?_eq_some] at h
      exact False.elim (Symbolic.DYBridge.DY.Trace.nil_length_not_lt _ h.1) }

theorem DhSafeCoreInv.of_attackerKnows {tr : ExecTrace} (hc : DhSafeCoreInv tr) {b : DY.Bytes} (hk : b.AttackerKnows tr) :
    DhSafe tr b := attackerKnows_imp_dhSafe (Trace.le_refl tr) hc.baseSafe hk

theorem DhSafeCoreInv.append_rnd {tr : ExecTrace} (hc : DhSafeCoreInv tr) (n : Nat) : DhSafeCoreInv (tr.append (RndE n)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_rnd tr n b).mp hb)).mono (Trace.append_le tr _),
   fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem DhSafeCoreInv.append_ev {tr : ExecTrace} (hc : DhSafeCoreInv tr) (ev : PQXDHEvent) : DhSafeCoreInv (tr.append (EvE ev)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_pqEv tr ev b).mp hb)).mono (Trace.append_le tr _),
   fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem DhSafeCoreInv.append_trEv {tr : ExecTrace} (hc : DhSafeCoreInv tr) (ev : TREvent) : DhSafeCoreInv (tr.append (TREvE ev)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_trEv tr ev b).mp hb)).mono (Trace.append_le tr _),
   fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem DhSafeCoreInv.append_cEv {tr : ExecTrace} (hc : DhSafeCoreInv tr) (ev : ComposedEvent) : DhSafeCoreInv (tr.append (CEvE ev)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_cEv tr ev b).mp hb)).mono (Trace.append_le tr _),
   fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem DhSafeCoreInv.append_st {tr : ExecTrace} (hc : DhSafeCoreInv tr) (me : Participant) (st : PQXDHState) :
    DhSafeCoreInv (tr.append (StE me st)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_pqSt tr me st b).mp hb)).mono (Trace.append_le tr _),
   fun me' st' idx hst => (hc.spqrSafe me' st' idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem DhSafeCoreInv.append_net {tr : ExecTrace} (hc : DhSafeCoreInv tr) {msg : DY.Bytes}
    (hmsg : DhSafe (tr.append (NetE msg)) msg) : DhSafeCoreInv (tr.append (NetE msg)) := by
  have hle : tr ≤ tr.append (NetE msg) := Trace.append_le tr (NetE msg)
  refine ⟨fun b hb => ?_, fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩
  rcases (CompTrace.baseAttackerKnows_append_net tr msg b).mp hb with rfl | hb' <;> [exact hmsg; exact (hc.baseSafe b hb').mono hle]

theorem DhSafeCoreInv.append_net_of_safe {tr : ExecTrace} (hc : DhSafeCoreInv tr) {msg : DY.Bytes}
    (hmsg : DhSafe tr msg) : DhSafeCoreInv (tr.append (NetE msg)) :=
  hc.append_net (hmsg.mono (Trace.append_le tr (NetE msg)))

theorem DhSafeCoreInv.append_net_rnd {tr : ExecTrace} (hc : DhSafeCoreInv tr) (t n : Nat) :
    DhSafeCoreInv (tr.append (NetE (CompTrace.mkRand t n))) :=
  hc.append_net (dhSafe_random _ { timestamp := t, size := n })

theorem DhSafeCoreInv.append_trSt {tr : ExecTrace} (hc : DhSafeCoreInv tr)
    {me : Participant} {st : TRState} (hspqr : DhSafe tr st.spqr) :
    DhSafeCoreInv (tr.append (TRStE me st)) := by
  have hle : tr ≤ tr.append (TRStE me st) := Trace.append_le tr (TRStE me st)
  refine ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_trSt tr me st b).mp hb)).mono hle,
    fun me' st' idx hst => ?_⟩
  rcases CompInv.CompPresBob.trStoredAt_append_same hst with ⟨_, hst'⟩ | ⟨_, _, rfl⟩
  · exact (hc.spqrSafe me' st' idx hst').mono hle
  · exact hspqr.mono hle

theorem DhSafeCoreInv.logSkippedKeys_preserves (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32) (tr : ExecTrace),
      DhSafeCoreInv tr → DhSafeCoreInv ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k).run tr).2.val
  | 0, _, _, _, hc => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [Traceful.run_pure]; exact hc
  | k + 1, ck, n, tr, hc => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    exact DhSafeCoreInv.logSkippedKeys_preserves s pk rIdx src k (kdfCk ck).1 (n + 1) _ (hc.append_trEv _)

theorem DhSafeCoreInv.append_logMessageKeyAndStore {tr : ExecTrace} (hc : DhSafeCoreInv tr)
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : DY.Bytes)
    (n : UInt32) (rIdx prev : Nat) (st : TRState) (hspqr : DhSafe tr st.spqr) :
    DhSafeCoreInv ((DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx prev st).run tr).2.val := by
  rw [CompPresTRExp.run_logMessageKeyAndStore_snd]
  exact (hc.append_trEv _).append_trSt (hspqr.mono (Trace.append_le tr _))

theorem parseTrSignalMsg_pqRatchet_dhSafe {T : ExecTrace} {t : DY.Bytes} {msg : TRSignalMsg}
    (ht : DhSafe T t) (hparse : parseTrSignalMsg t = some msg) : DhSafe T msg.pqRatchet := by
  unfold parseTrSignalMsg at hparse
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at hparse
  rcases hparse with ⟨⟨wire, mac⟩, hsplit, x, hx, rfl⟩; dsimp only at hx ⊢
  rw [← Concat.concat_split t (t.length - Trunc.trunc8Length) wire mac hsplit] at ht
  have hwire : DhSafe T wire := ((dhSafe_concat_iff wire mac).mp ht).1
  rw [TrWire.trWireMsg_of_fields? hx] at hwire; exact ((dhSafe_trWireMsg_iff x).mp hwire).2.2

theorem dhSafe_receiveSignalMsg_at {tr : ExecTrace} (hc : DhSafeCoreInv tr) {α : Type}
    (msgIdx : Nat) {f : TRSignalMsg → Traceful α}
    (hf : ∀ msg, DhSafe tr msg.pqRatchet → DhSafeCoreInv ((f msg).run tr).2.val) :
    DhSafeCoreInv (((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at msgIdx tr hc fun raw _ hraw => ?_
  rcases hparse : parseTrSignalMsg raw with _ | msg
  · dsimp only; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hc
  dsimp only; rw [CompTrace.run_bind_assoc_snd]
  exact CompTrace.bind_guardP_at _ tr hc fun _ =>
    hf msg (parseTrSignalMsg_pqRatchet_dhSafe (hc.of_attackerKnows hraw) hparse)

theorem dhSafe_preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) (tr : ExecTrace) (hc : DhSafeCoreInv tr) :
    DhSafeCoreInv ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hc (hc.append_rnd 32)
    fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ => ?_
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let hs := aliceOut tr ikA ikBPk spkPk pqPk opk
  let tr1 := tr.append (RndE 32); let tr2 := tr1.append (RndE 32)
  let dhsA := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr2.length 32
  let stA : TRState :=
    { peer := b, myIk := DY.Libsignal.PQXDH.serializedIk hs.ikA, peerIk := DY.Libsignal.PQXDH.serializedIk hs.ikB,
      rk := (createChain hs.keys.rk hs.spk dhsA).1, dhs := dhsA, cks := (createChain hs.keys.rk hs.spk dhsA).2,
      ns := 0, pn := 0,
      sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk,
      initiator := true, rIdx := 1,
      recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }],
      spqr := Spqr.spqrInit hs.keys.pqr spqrA2B }
  let tr3 := tr2.append (RndE 32); let tr4 := tr3.append (NetE hs.ek); let tr5 := tr4.append (NetE hs.ct)
  let tr6 := tr5.append (EvE (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys))
  let tr7 := tr6.append (TREvE (TREvent.InitSession a b (DiffieHellman.dhPk dhsA) hs.spk))
  let tr8 := tr7.append (CEvE (ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length))
  rw [CompTrace.run_genRand_bind_snd]; dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, htl,
    CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  change DhSafeCoreInv (tr8.append (TRStE a stA))
  have hc3 : DhSafeCoreInv tr3 := ((hc.append_rnd 32).append_rnd 32).append_rnd 32
  have hc4 : DhSafeCoreInv tr4 := hc3.append_net_of_safe (dhSafe_dhPk_rand _ _)
  have hc5 : DhSafeCoreInv tr5 := hc4.append_net_of_safe (dhSafe_kemEncap_fst _ pqPk _)
  have hc8 : DhSafeCoreInv tr8 := ((hc5.append_ev _).append_trEv _).append_cEv _
  have hpqr : DhSafe tr8 hs.keys.pqr := by
    dsimp [hs, aliceOut, DY.Libsignal.PQXDH.aliceAgreement]; exact dhSafe_pqxdhKdf_pqr tr8 _
  exact hc8.append_trSt (.spqrInit { authKey := hs.keys.pqr, params := spqrA2B } hpqr (dhSafe_literal _ _))

theorem dhSafe_bobStart_commit {tr : ExecTrace} (hc : DhSafeCoreInv tr)
    (b a : Participant) (sB sS sQ : DY.Bytes) (o : Option DY.Bytes) (ikA ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (dhs spqr' seed pqSalt m : DY.Bytes) (c' : RecvChain) (hspqr : DhSafe tr spqr') :
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    DhSafeCoreInv (((do
      let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
      ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (DiffieHellman.dhPk sB) ikA
        (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys)
      if true then
        ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
        ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
      ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
      let skipped := msg.counter.toNat - c.index.toNat
      let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
        msg.counter c.rIdx childIdx
        { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val) := by
  intro st c; let doneIdx := tr.length
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let tr₁ := tr.append (EvE (.BobDone b a (DiffieHellman.dhPk sB) ikA
    (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys))
  let tr₂ := tr₁.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
  let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
  let tr₄ := tr₃.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
  have hc₄ : DhSafeCoreInv tr₄ := (((hc.append_ev _).append_trEv _).append_trEv _).append_cEv _
  have hle₀₄ : tr ≤ tr₄ := Trace.le_trans _ _ _ (Trace.append_le tr _)
    (Trace.le_trans _ _ _ (Trace.append_le tr₁ _) (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _)))
  let skipped := msg.counter.toNat - c.index.toNat; let childIdx := tr₄.length + skipped + 2
  let skipAct := DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
  let restAct : Unit → Traceful Nat := fun _ => do
    ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
      msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }
  rw [htl, CompPresTRExp.run_logEvent_bind_snd]; simp only [↓reduceIte]
  rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, htl]
  change DhSafeCoreInv (((skipAct >>= restAct).run tr₄).2.val)
  rw [CompInv.CompPresBob.run_logSkippedKeys_bind_snd]
  let tr₅ := (skipAct.run tr₄).2.val; have hle₄₅ : tr₄ ≤ tr₅ := (skipAct.run tr₄).2.property
  have hc₅ : DhSafeCoreInv tr₅ := DhSafeCoreInv.logSkippedKeys_preserves (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx skipped c.chainKey c.index tr₄ hc₄
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  have hc₆ : DhSafeCoreInv tr₆ := hc₅.append_trEv _
  have hle₀₆ : tr ≤ tr₆ := Trace.le_trans _ _ _ hle₀₄ (Trace.le_trans _ _ _ hle₄₅ (Trace.append_le tr₅ _))
  dsimp only [restAct]; rw [CompPresTRExp.run_logEvent_bind_snd]
  exact hc₆.append_logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
    msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' } (hspqr.mono hle₀₆)

theorem dhSafe_preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : DhSafeCoreInv tr) :
    DhSafeCoreInv ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hc
    fun sB sS sQ o ikA _ ek ct _ keys _ _ _ _ _ _ _ _ hbob => ?_
  refine dhSafe_receiveSignalMsg_at hc mh.msg fun msg hpq => ?_; dsimp only
  refine CompInv.CompPresBob.bind_ensureReceiverChain_bobInitSt
    a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey tr hc fun _ => ?_
  let dhs := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32
  let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
  let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
  let tr₁ := tr.append (RndE 32); have hc₁ : DhSafeCoreInv tr₁ := hc.append_rnd 32
  rcases hConsume : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · dsimp only; rw [Traceful.run_failure]; exact hc₁
  dsimp only; rcases hSpqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
  · dsimp only; rw [Traceful.run_failure]; exact hc₁
  dsimp only
  have hkeys_eq : ∃ ikm, keys = DY.Libsignal.PQXDH.pqxdhKdf ikm := by
    dsimp only [DY.Libsignal.PQXDH.bobAgreement, Option.pure_def] at hbob
    injection hbob with h; exact ⟨_, h.symm⟩
  obtain ⟨_, hkeys_eq⟩ := hkeys_eq
  have hle₀₁ : tr ≤ tr₁ := Trace.append_le tr _
  have hpqr₁ : DhSafe tr₁ keys.pqr := by rw [hkeys_eq]; exact dhSafe_pqxdhKdf_pqr tr₁ _
  have hspqr₁ : DhSafe tr₁ spqr' :=
    dhSafe_spqrRecv_state hSpqr (.spqrInit { authKey := keys.pqr, params := spqrB2A } hpqr₁ (dhSafe_literal _ _)) (hpq.mono hle₀₁)
  let tr₂ := tr₁.append (NetE key); have hle₁₂ : tr₁ ≤ tr₂ := Trace.append_le tr₁ _
  have hc₂ : DhSafeCoreInv tr₂ := hc₁.append_net_of_safe (dhSafe_spqrRecv_key hSpqr)
  have hspqr₂ : DhSafe tr₂ spqr' := hspqr₁.mono hle₁₂
  rw [CompPresTRExp.run_sendMessage_bind_snd]
  change DhSafeCoreInv (((Network.receiveMessage pqIdx >>= fun pqSalt =>
    DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed >>= fun m => _).run tr₂).2.val)
  refine CompTrace.bind_receiveMessage_at pqIdx tr₂ hc₂ fun pqSalt _ _ => ?_
  refine CompInv.CompPresBob.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr₂ hc₂ fun m _ => ?_
  cases o with
  | none =>
    dsimp only [Option.map]
    exact dhSafe_bobStart_commit hc₂ b a sB sS sQ none ikA ek ct keys msg dhs spqr' seed pqSalt m c' hspqr₂
  | some oSk =>
    dsimp only [Option.map]; rw [CompTrace.run_bind_snd]
    unfold DY.Libsignal.PQXDH.guardTrace; rw [Traceful.run_mk]; dsimp only
    by_cases hused : (!opkUsedB tr₂ b (DiffieHellman.dhPk oSk)) = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hused h]; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd]
      exact dhSafe_bobStart_commit (hc₂.append_ev _) b a sB sS sQ (some oSk) ikA ek ct keys msg dhs spqr' seed pqSalt m c'
        (hspqr₂.mono (Trace.append_le tr₂ _))
    · rw [ite_eq_right_iff.mpr fun h => absurd h hused]; dsimp only; exact hc₂

theorem dhSafe_preserves_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : DhSafeCoreInv tr) :
    DhSafeCoreInv ((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  obtain ⟨_, _, _, _, _, hdhs, _, _, _, _⟩ := hinv.trStOK me st stateIdx hst
  have hspqr0 : DhSafe tr st.spqr := hc.spqrSafe me st stateIdx hst
  apply CompTrace.bind_guardP_at _ tr hc; intro _
  rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_sendMessage_bind_snd]
  let m := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32; let tr1 := tr.append (RndE 32)
  let coins := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr1.length coinsLen; let tr2 := tr1.append (RndE coinsLen)
  let key := (Spqr.spqrSend st.spqr coins).2.1; let tr3 := tr2.append (NetE key)
  have hc3 : DhSafeCoreInv tr3 := ((hc.append_rnd 32).append_rnd coinsLen).append_net_of_safe (dhSafe_spqrSend_key tr2 st.spqr coins)
  have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 (Trace.append_le tr _) (Trace.append_le tr1 _)) (Trace.append_le tr2 _)
  apply CompTrace.bind_receiveMessage_at pqIdx tr3 hc3; intro pqSalt _ _
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    CompPresTRExp.run_logMessageKeyAndStore_bind_snd, CompPresTRExp.run_sendMessage_snd]
  let tr4 := tr3.append (TREvE (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m))
  have hc4 : DhSafeCoreInv tr4 := hc3.append_trEv _
  have hle04 : tr ≤ tr4 := Trace.le_trans tr tr3 tr4 hle03 (Trace.append_le tr3 _)
  let st' : TRState := { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 }
  have hspqr'_safe4 : DhSafe tr4 st'.spqr := dhSafe_spqrSend_state (hspqr0.mono hle04) (dhSafe_random tr4 _)
  have hc6 : DhSafeCoreInv ((DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) .sender (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st').run tr4).2.val :=
    hc4.append_logMessageKeyAndStore me (st.sessionInfo me) .sender
      (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st' hspqr'_safe4
  rw [CompPresTRExp.run_logMessageKeyAndStore_snd] at hc6
  let tr5 := tr4.append (TREvE (TREvent.MessageKey (st.sessionInfo me) .sender
    (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx))
  let tr6 := tr5.append (TRStE me st')
  have hdhs_safe : DhSafe tr6 (DiffieHellman.dhPk st.dhs) := by
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩ <;> [rw [hdhs_eq]; rw [hdhs_eq]] <;> exact dhSafe_dhPk_rand tr6 _
  let mk := trMsgKeys pqSalt (kdfCk st.cks).2
  let wire := DY.Libsignal.TripleRatchet.trHonestWireMsg (DiffieHellman.dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc mk.cipherKey mk.iv m) (Spqr.spqrSend st.spqr coins).2.2
  have hwire_safe6 : DhSafe tr6 wire :=
    dhSafe_trHonestWireMsg st.ns st.pn hdhs_safe (.symEnc (dhSafe_random tr6 _)) (dhSafe_spqrSend_msg tr6 st.spqr coins)
  exact hc6.append_net_of_safe (.concat hwire_safe6 (dhSafe_computeMac_honest tr6 pqSalt (kdfCk st.cks).2
    st.myIk st.peerIk st.dhs st.ns st.pn m (Spqr.spqrSend st.spqr coins).2.2))

theorem dhSafe_preserves_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : DhSafeCoreInv tr) :
    DhSafeCoreInv ((DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  have hspqr0 : DhSafe tr st.spqr := hc.spqrSafe me st stateIdx hst
  apply dhSafe_receiveSignalMsg_at hc msgIdx; intro msg hpq_safe
  apply CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc; intro ⟨ev⟩ _
  cases ev with
  | SkippedKeyStored s pk n seed rIdx _sourceStateIdx =>
    dsimp only; apply CompTrace.bind_guardP_at _ tr hc; intro _
    apply CompPresTRExp.bind_guardTrace_at _ tr hc; intro _
    rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
    let tr1 := tr.append (NetE key); have hc1 : DhSafeCoreInv tr1 := hc.append_net_of_safe (dhSafe_spqrRecv_key hspqr_recv)
    have hle01 : tr ≤ tr1 := Trace.append_le tr _
    apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1; intro pqSalt _ _
    apply CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1; intro m
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    let tr2 := tr1.append (TREvE (TREvent.SkippedKeyUsed s skippedKeyEventIdx))
    let tr3 := tr2.append (TREvE (TREvent.Received me st.peer pk n m))
    have hc3 : DhSafeCoreInv tr3 := (hc1.append_trEv _).append_trEv _
    have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 hle01 (Trace.append_le tr1 _)) (Trace.append_le tr2 _)
    exact hc3.append_logMessageKeyAndStore me s .receiver seed pqSalt n rIdx stateIdx { st with spqr := spqr' } ((dhSafe_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle03)
  | _ => dsimp only; rw [Traceful.run_failure]; exact hc

theorem dhSafe_preserves_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : DhSafeCoreInv tr) :
    DhSafeCoreInv ((DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  have hspqr0 : DhSafe tr st.spqr := hc.spqrSafe me st stateIdx hst
  apply dhSafe_receiveSignalMsg_at hc msgIdx; intro msg hpq_safe
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor
  rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c
  · dsimp only; rcases hlow : x25519LowOrder msg.ratchetKey with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte, DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_bind_assoc_snd]
      apply CompTrace.bind_guardP_at _ tr hc; intro _
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_genRand_bind_snd, CompTrace.run_pure_bind_snd, CompTrace.run_pure_bind_snd]
      let tr1 := tr.append (RndE 32); have hc1 : DhSafeCoreInv tr1 := hc.append_rnd 32
      have hle01 : tr ≤ tr1 := Trace.append_le tr _
      let dhs' := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32
      let rk1 := (createChain st.rk msg.ratchetKey st.dhs).1; let ckr := (createChain st.rk msg.ratchetKey st.dhs).2
      let rk2 := (createChain rk1 msg.ratchetKey dhs').1; let cks2 := (createChain rk1 msg.ratchetKey dhs').2
      let c_new : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := ckr, index := 0, rIdx := st.rIdx + 2 }
      let recv1 := (st.recv ++ [c_new]).drop ((st.recv.length + 1) - maxReceiverChains)
      let pn1 := if st.ns = 0 then 0 else st.ns - 1
      let st1 : TRState := { st with rk := rk2, dhs := dhs', cks := cks2, ns := 0, pn := pn1, rIdx := st.rIdx + 2, recv := recv1 }
      rcases hcons : consumeMessageKey c_new msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hc1
      dsimp only; rcases hspqr_recv : Spqr.spqrRecv st1.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hc1
      dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
      let tr2 := tr1.append (NetE key); have hc2 : DhSafeCoreInv tr2 := hc1.append_net_of_safe (dhSafe_spqrRecv_key hspqr_recv)
      have hle02 : tr ≤ tr2 := Trace.le_trans tr tr1 tr2 hle01 (Trace.append_le tr1 _)
      apply CompTrace.bind_receiveMessage_at pqIdx tr2 hc2; intro pqSalt _ _
      apply CompPresTRExp.bind_verifyMacAndDecrypt_at st1 msg pqSalt seed tr2 hc2; intro m
      simp only [↓reduceIte]; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
        CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompTrace.run_bind_snd]
      let tr3 := tr2.append (TREvE (TREvent.DHRatchet me st1.peer msg.ratchetKey (DiffieHellman.dhPk st1.dhs)))
      let tr4 := tr3.append (TREvE (TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2)))
      have hc4 : DhSafeCoreInv tr4 := (hc2.append_trEv _).append_trEv _
      have hle04 : tr ≤ tr4 := Trace.le_trans tr tr2 tr4 hle02 (Trace.le_trans tr2 tr3 tr4 (Trace.append_le tr2 _) (Trace.append_le tr3 _))
      have hc5 := DhSafeCoreInv.logSkippedKeys_preserves (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
        (msg.counter.toNat - c_new.index.toNat) c_new.chainKey c_new.index tr4 hc4
      have hle45 := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
        c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4).2.property
      rcases hsk_res : (DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
          c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4 with ⟨_ | u, tr5_sub⟩
      · rw [hsk_res] at hc5; exact hc5
      · rw [hsk_res] at hc5 hle45; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
        let tr6 := tr5_sub.val.append (TREvE (TREvent.Received me st1.peer msg.ratchetKey msg.counter m))
        have hc6 : DhSafeCoreInv tr6 := hc5.append_trEv _
        have hle06 : tr ≤ tr6 := Trace.le_trans tr tr4 tr6 hle04 (Trace.le_trans tr4 tr5_sub.val tr6 hle45 (Trace.append_le tr5_sub.val _))
        exact hc6.append_logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt msg.counter
          c_new.rIdx stateIdx { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
          ((dhSafe_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle06)
    · simp only [↓reduceIte]; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hc
  · dsimp only; rw [CompTrace.run_pure_bind_snd]
    rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
    let tr1 := tr.append (NetE key); have hc1 : DhSafeCoreInv tr1 := hc.append_net_of_safe (dhSafe_spqrRecv_key hspqr_recv)
    have hle01 : tr ≤ tr1 := Trace.append_le tr _
    apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1; intro pqSalt _ _
    apply CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1; intro m
    simp only [Bool.false_eq_true, ↓reduceIte]; rw [CompTrace.run_bind_snd]
    have hc2 := DhSafeCoreInv.logSkippedKeys_preserves (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
      (msg.counter.toNat - c.index.toNat) c.chainKey c.index tr1 hc1
    have hle12 := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
      c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1).2.property
    rcases hsk_res : (DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
        c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1 with ⟨_ | u, tr2_sub⟩
    · rw [hsk_res] at hc2; exact hc2
    · rw [hsk_res] at hc2 hle12; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
      let tr3 := tr2_sub.val.append (TREvE (TREvent.Received me st.peer msg.ratchetKey msg.counter m))
      have hc3 : DhSafeCoreInv tr3 := hc2.append_trEv _
      have hle03 : tr ≤ tr3 := Trace.le_trans tr tr1 tr3 hle01 (Trace.le_trans tr1 tr2_sub.val tr3 hle12 (Trace.append_le tr2_sub.val _))
      exact hc3.append_logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter
        c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }
        ((dhSafe_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle03)

private theorem dhSafe_of_eq_createChain_fst {T : ExecTrace} {rk pk sk x : DY.Bytes}
    (hx : x = (createChain rk pk sk).1) : DhSafe T x := by
  subst hx; exact dhSafe_createChain_fst T rk pk sk

theorem dhSafe_preserves_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : DhSafeCoreInv tr) :
    DhSafeCoreInv ((DY.Libsignal.TripleRatchet.exposeKey me stateIdx k).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  obtain ⟨_, keys, _, hkeys, _, hdhs, _, hrk, hcks, hrecv⟩ := hinv.trStOK me st stateIdx hst
  cases k with
  | rk =>
    dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    obtain ⟨r, p, s, hrk_eq⟩ := hrk
    exact (hc.append_trEv _).append_net_of_safe (dhSafe_of_eq_createChain_fst hrk_eq)
  | dhs =>
    dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedDHs (st.sessionInfo me) st.dhs st.rIdx)
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩
    · rw [hdhs_eq] at hc1 ⊢; exact hc1.append_net_rnd (t + 2) 32
    · rw [hdhs_eq] at hc1 ⊢; exact hc1.append_net_rnd t 32
  | cks =>
    dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    obtain ⟨rkChain, pk, sk, n, _, hcks_eq⟩ := hcks
    exact (hc.append_trEv _).append_net_of_safe (dhSafe_of_eq_chainKeyAt_createChain_snd hcks_eq)
  | ckr pk =>
    dsimp only; rcases hfind : findRecvChain st.recv pk with _ | c; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; have hc_mem : c ∈ st.recv := CompPresTRExp.findRecvChain_mem hfind
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    let tr1 := tr.append (TREvE (TREvent.ExposedCKr (st.sessionInfo me) c.chainKey c.index c.rIdx))
    have hc1 : DhSafeCoreInv tr1 := hc.append_trEv _
    refine hc1.append_net_of_safe ?_
    obtain ⟨ikm, hikm⟩ := CompInv.CompPubInv.handshakeKeysAt_eq_pqxdhKdf hinv hkeys
    rcases hrecv c hc_mem with ⟨_, _, hck⟩ | ⟨n, _, _, hck⟩ | ⟨rkChain, pk', sk', n, _, hck⟩
    · exact dhSafe_of_eq_chainKeyAt_pqxdhKdf_ck (n := 0) (by rw [hck, hikm]; rfl)
    · exact dhSafe_of_eq_chainKeyAt_pqxdhKdf_ck (n := n + 1) (by rw [hck, hikm])
    · exact dhSafe_of_eq_chainKeyAt_createChain_snd hck

theorem dhSafe_preserves_exposeSkipped (skippedKeyEventIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : DhSafeCoreInv tr) :
    DhSafeCoreInv ((DY.Libsignal.TripleRatchet.exposeSkipped skippedKeyEventIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  apply CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc; intro ⟨ev⟩ he
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    dsimp only
    obtain ⟨_, _, _, _, hseed⟩ := hinv.skipOK s pk n seed rIdx src skippedKeyEventIdx
      (by rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1])
    apply CompPresTRExp.bind_guardTrace_at _ tr hc; intro _
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    let tr1 := tr.append (TREvE (TREvent.ExposedMK s seed n rIdx))
    have hc1 : DhSafeCoreInv tr1 := hc.append_trEv _
    have hseed_shape : ∃ c, seed = (kdfCk c).2 := by rcases hseed with ⟨m, rfl⟩ | ⟨_, _, _, m, _, rfl⟩ <;> exact ⟨_, rfl⟩
    obtain ⟨c, rfl⟩ := hseed_shape
    exact hc1.append_net_of_safe (dhSafe_kdfCk_snd tr1 c)
  | _ => dsimp only; rw [Traceful.run_failure]; exact hc

theorem dhSafeCoreInv_of_reachable {tr : ExecTrace} (hr : ReachableTrace tr) : DhSafeCoreInv tr := by
  induction hr with
  | Base => exact dhSafeCoreInv_nil
  | Step input hPre hReachPre hc =>
    have hinv : SpqrInv _ := spqrInv_of_reachable _ hReachPre
    have hst_bind : ∀ {S α : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
        (p : Participant) (s : S) (k : Nat → Traceful α) (t : ExecTrace),
        ((PersistentLocalState.storeLocalState p s >>= k).run t).2.val =
          ((k t.length).run (t.append (⟨⟨p, s⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState S)))).2.val :=
      fun p s k t => by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
        rw [CompTrace.run_bind_snd, Traceful.run_mk]
    have hst_snd : ∀ {S : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
        (p : Participant) (s : S) (t : ExecTrace),
        ((PersistentLocalState.storeLocalState p s).run t).2.val =
          t.append (⟨⟨p, s⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState S)) :=
      fun p s t => by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
    have hlog_snd : ∀ {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)] (ev : E) (t : ExecTrace),
        ((ProtocolEvent.logEvent ev).run t).2.val = t.append (⟨ev⟩ : ProtocolEvent.ExecEntryT E) := fun ev t => by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
      rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
    rcases input with ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k, _⟩, inp⟩
    · change DY.Bytes at inp; change DhSafeCoreInv ((Network.sendMessage inp).run _).2.val; rw [CompPresTRExp.run_sendMessage_snd]
      exact hc.append_net_of_safe (hc.of_attackerKnows hPre)
    · change Participant at inp; change DhSafeCoreInv ((registerIdentity inp).run _).2.val; unfold registerIdentity
      refine bind_guardOnTrace_at _ _ hc fun _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, hst_snd]
      exact ((((hc.append_rnd 32).append_ev _).append_net_of_safe
        (dhSafe_dhPk_rand _ _)).append_net_of_safe (dhSafe_vk _ _)).append_st inp _
    · rcases inp with ⟨p, skIdx⟩; change DhSafeCoreInv ((registerCorruptIdentity p skIdx).run _).2.val; unfold registerCorruptIdentity
      refine bind_guardOnTrace_at _ _ hc fun _ => bind_receiveMessage_at skIdx _ hc fun _ _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, hlog_snd]; exact (hc.append_ev _).append_ev _
    · rcases inp with ⟨b, idStateIdx⟩; change DhSafeCoreInv ((genSignedPrekey b idStateIdx).run _).2.val; unfold genSignedPrekey
      refine bind_getKey_at b idStateIdx .identity _ hc fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact (((((hc.append_rnd 32).append_rnd 64).append_ev _).append_st b _).append_net_of_safe
        (dhSafe_dhPk_rand _ _)).append_net_of_safe (dhSafe_sign _ _ _ _)
    · rcases inp with ⟨b, idStateIdx⟩; change DhSafeCoreInv ((genPQPrekey b idStateIdx).run _).2.val; unfold genPQPrekey
      refine bind_getKey_at b idStateIdx .identity _ hc fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact (((((hc.append_rnd 64).append_rnd 64).append_ev _).append_st b _).append_net_of_safe
        (.kemPk (dhSafe_random _ _))).append_net_of_safe (dhSafe_sign _ _ _ _)
    · change Participant at inp; change DhSafeCoreInv ((genOneTimePrekey inp).run _).2.val; unfold genOneTimePrekey
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd, hst_bind,
        CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact (((hc.append_rnd 32).append_ev _).append_st inp _).append_net_of_safe (dhSafe_dhPk_rand _ _)
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩; exact dhSafe_preserves_aliceStart a b idStateIdx regIdxB bh _ hc
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩; exact dhSafe_preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩; exact dhSafe_preserves_messageEncrypt me stateIdx coinsLen pqIdx _ hinv hc
    · rcases inp with ⟨me, stateIdx⟩; change DhSafeCoreInv ((DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx).run _).2.val
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
      refine CompTrace.bind_getLocalState_tr_at me stateIdx _ hc fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, Traceful.run_failure]; exact hc.append_rnd 32
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩; exact dhSafe_preserves_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩; exact dhSafe_preserves_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, k⟩; exact dhSafe_preserves_exposeKey me stateIdx k _ hinv hc
    · rcases inp with ⟨me, stateIdx⟩; change DhSafeCoreInv ((DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx).run _).2.val
      unfold DY.Libsignal.TripleRatchet.exposeSpqr
      apply CompTrace.bind_getLocalState_tr_at me stateIdx _ hc; intro st hst
      rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
      exact (hc.append_trEv _).append_net_of_safe ((hc.spqrSafe me st stateIdx hst).mono (Trace.append_le _ _))
    · exact dhSafe_preserves_exposeSkipped inp _ hinv hc
    · rcases inp with ⟨p, stateIdx⟩; change DhSafeCoreInv ((compromiseIK p stateIdx).run _).2.val; unfold compromiseIK
      refine bind_getKey_at p stateIdx .identity _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _⟩ := hinv.stOK p { kind := .identity, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]; exact (hc.append_ev _).append_net_rnd t 32
    · rcases inp with ⟨b, stateIdx⟩; change DhSafeCoreInv ((compromiseSPK b stateIdx).run _).2.val; unfold compromiseSPK
      refine bind_getKey_at b stateIdx .signedPrekey _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .signedPrekey, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]; exact (hc.append_ev _).append_net_rnd t 32
    · rcases inp with ⟨b, stateIdx⟩; change DhSafeCoreInv ((compromisePQSPK b stateIdx).run _).2.val; unfold compromisePQSPK
      refine bind_getKey_at b stateIdx .pqPrekey _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .pqPrekey, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]; exact (hc.append_ev _).append_net_rnd t 64
    · rcases inp with ⟨b, stateIdx⟩; change DhSafeCoreInv ((compromiseOPK b stateIdx).run _).2.val; unfold compromiseOPK
      refine bind_getKey_at b stateIdx .oneTimePrekey _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _⟩ := hinv.stOK b { kind := .oneTimePrekey, sk := sk } stateIdx hst
      refine CompPresPQXDH.Preserves.bind_guardOnTrace _ (fun _ hc _ => ?_) _ hc
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]; exact (hc.append_ev _).append_net_rnd t 32
    · change DhSafeCoreInv ((DY.Libsignal.PQXDH.breakDH).run _).2.val; unfold DY.Libsignal.PQXDH.breakDH
      rw [hlog_snd]; exact hc.append_ev _
    · change DhSafeCoreInv ((DY.Libsignal.PQXDH.breakKEM).run _).2.val; unfold DY.Libsignal.PQXDH.breakKEM
      rw [hlog_snd]; exact hc.append_ev _
    · change Nat at inp; change DhSafeCoreInv ((invertDH inp).run _).2.val; unfold invertDH
      refine CompPresPQXDH.Preserves.bind_guardOnTrace DY.Libsignal.PQXDH.brokenDHB (fun tr hc _ => ?_) _ hc
      refine bind_receiveMessage_at inp tr hc fun pk _ hpk => ?_
      have hpk_safe : DhSafe tr (X25519.normalizeX25519Key pk) := dhSafe_x25519Key (hc.of_attackerKnows hpk)
      rcases hdh : DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
      · dsimp only; rw [Traceful.run_failure]; exact hc
      dsimp only; rw [CompPresTRExp.run_sendMessage_snd]; rw [dhSkOf_eq_some hdh] at hpk_safe
      exact hc.append_net_of_safe ((dhSafe_dhPk_iff sk).mp hpk_safe).1
    · change Nat at inp; change DhSafeCoreInv ((invertKEM inp).run _).2.val; unfold invertKEM
      refine CompPresPQXDH.Preserves.bind_guardOnTrace DY.Libsignal.PQXDH.brokenKEMB (fun tr hc _ => ?_) _ hc
      refine bind_receiveMessage_at inp tr hc fun pk _ hpk => ?_
      have hpk_safe : DhSafe tr pk := hc.of_attackerKnows hpk
      rcases hkem : PQKem.invertKemPublicKey pk with _ | sk
      · dsimp only [liftM, monadLift, MonadLift.monadLift]; rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; exact hc
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [CompPresTRExp.run_sendMessage_snd]
      rw [kemPkInvert_eq_some hkem] at hpk_safe; exact hc.append_net_of_safe ((dhSafe_kemPk_iff sk).mp hpk_safe)
    · omega

/-! ## Reachable-trace inversion theorems -/

/-- Trace-level invariant packaging `DhSafe tr b` for all `b.AttackerKnows tr`. -/
structure DhSafeInv (tr : ExecTrace) : Prop where
  safe : ∀ b, b.AttackerKnows tr → DhSafe tr b

theorem dhSafeInv_of_reachable {tr : ExecTrace} (hr : ReachableTrace tr) : DhSafeInv tr :=
  ⟨fun _ hAK => (dhSafeCoreInv_of_reachable hr).of_attackerKnows hAK⟩

theorem dhSafe_of_attackerKnows_reachable {T : ExecTrace} (hT : ReachableTrace T)
    {b : DY.Bytes} (hAK : b.AttackerKnows T) : DhSafe T b :=
  (dhSafeInv_of_reachable hT).safe b hAK

/-- If `{ pk := pk, sk := sk }.pack` is attacker-known on a reachable trace `T`, then either `pk`
and `sk` are both attacker-known, or `pk = dhPk c` with `c` and `dhPk sk` both attacker-known. -/
theorem dhPack_attackerKnows_inv {T : ExecTrace} (hT : ReachableTrace T) {pk sk : DY.Bytes}
    (hk : (({ pk := pk, sk := sk } : DiffieHellman.Dh.SubF DY.Bytes).pack).AttackerKnows T) :
    (pk.AttackerKnows T ∧ sk.AttackerKnows T) ∨
    (∃ c, pk = DiffieHellman.dhPk c ∧ c.AttackerKnows T ∧ (DiffieHellman.dhPk sk).AttackerKnows T) :=
  dhSafe_dh_pack_inv (dhSafe_of_attackerKnows_reachable hT hk)

/-- If `DiffieHellman.dhPk z` is attacker-known on a reachable trace `T`, then either
`z.AttackerKnows T` or `z = randTerm n 32` for some `n`. -/
theorem dhPk_attackerKnows_inv {T : ExecTrace} (hT : ReachableTrace T) {z : DY.Bytes}
    (hk : (DiffieHellman.dhPk z).AttackerKnows T) :
    z.AttackerKnows T ∨ ∃ n, z = randTerm n 32 :=
  ((dhSafe_dhPk_iff z).mp (dhSafe_of_attackerKnows_reachable hT hk)).2

theorem dh_attackerKnows_inv {T : ExecTrace} (hT : ReachableTrace T)
    {pk sk : DY.Bytes} (hk : (DiffieHellman.dh pk sk).AttackerKnows T) :
    (pk.AttackerKnows T ∧ sk.AttackerKnows T) ∨
    (∃ c, pk = DiffieHellman.dhPk c ∧ c.AttackerKnows T ∧ (DiffieHellman.dhPk sk).AttackerKnows T) :=
  dhSafe_dh_inv (dhSafe_of_attackerKnows_reachable hT hk)

theorem agree_attackerKnows_inv {T : ExecTrace} (hT : ReachableTrace T)
    {pk sk : DY.Bytes} (hk : (DY.Libsignal.PQXDH.agree pk sk).AttackerKnows T) :
    ((X25519.normalizeX25519Key pk).AttackerKnows T ∧ sk.AttackerKnows T) ∨
    (∃ c, X25519.normalizeX25519Key pk = DiffieHellman.dhPk c ∧ c.AttackerKnows T ∧ (DiffieHellman.dhPk sk).AttackerKnows T) :=
  dh_attackerKnows_inv hT hk

end Symbolic.Swarm.CREF.TR.G1
