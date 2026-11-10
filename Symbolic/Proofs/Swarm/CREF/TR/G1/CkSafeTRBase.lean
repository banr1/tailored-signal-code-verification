/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.LitKeyKnown
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
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc
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

/-!
# Structural Chain-Key Safety (`SafeCkTR`)

Defines `TruncOKCkTR`, `KdfOKTR`, and `SafeCkTR` over the composed term algebra with the `0x02`
chain-key KDF clause restricted to `StoredCkTR`, and proves monotonicity and closure under
`AttackerKnowledge`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (createChain computeMac hmac kdfCk chainKeyAt lit litByte
  messageVersion)
open DY.Libsignal.PQXDH (pqxdhKdf)
open Symbolic.Swarm.COMPOSED.CompTermAlgebra (kemDecap_eq_some_iff)
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED.CompRatchet

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Unsealed injectivity helpers -/

section UnsealedInjectivity
unseal DY.Bytes

private theorem symEnc_inj_ck {k₁ iv₁ m₁ k₂ iv₂ m₂ : DY.Bytes}
    (h : SymEnc.symEnc k₁ iv₁ m₁ = SymEnc.symEnc k₂ iv₂ m₂) : k₁ = k₂ ∧ iv₁ = iv₂ ∧ m₁ = m₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.SymEnc.Enc.SubF) { key := k₁, iv := iv₁, msg := m₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.SymEnc.Enc.SubF) { key := k₂, iv := iv₂, msg := m₂ }
  change DY.Bytes.view? (SymEnc.symEnc k₁ iv₁ m₁) _ = _ at h1
  change DY.Bytes.view? (SymEnc.symEnc k₂ iv₂ m₂) _ = _ at h2
  rw [h, h2] at h1; injection h1 with h1; cases h1; exact ⟨rfl, rfl, rfl⟩

private theorem trWireMsg_pack_inj_ck {w₁ w₂ : TrWire.TrWireMsg.SubF DY.Bytes} (h : w₁.pack = w₂.pack) : w₁ = w₂ := by
  have h1 : DY.Bytes.view? w₁.pack DY.TrWire.TrWireMsg.SubF = some w₁ := DY.BytesView.view_pack w₁
  have h2 : DY.Bytes.view? w₂.pack DY.TrWire.TrWireMsg.SubF = some w₂ := DY.BytesView.view_pack w₂
  rw [h, h2] at h1; injection h1 with h1; exact h1.symm

private theorem variant_pack_inj_ck {v₁ v₂ : X25519.Variant.SubF DY.Bytes} (h : v₁.pack = v₂.pack) : v₁ = v₂ := by
  have h1 : DY.Bytes.view? v₁.pack DY.X25519.Variant.SubF = some v₁ := DY.BytesView.view_pack v₁
  have h2 : DY.Bytes.view? v₂.pack DY.X25519.Variant.SubF = some v₂ := DY.BytesView.view_pack v₂
  rw [h, h2] at h1; injection h1 with h1; exact h1.symm

private theorem dhPk_inj_tr_ck {s₁ s₂ : DY.Bytes} (h : DiffieHellman.dhPk s₁ = DiffieHellman.dhPk s₂) : s₁ = s₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := s₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := s₂ }
  change DY.Bytes.view? (DiffieHellman.dhPk s₁) _ = _ at h1
  change DY.Bytes.view? (DiffieHellman.dhPk s₂) _ = _ at h2
  rw [h, h2] at h1; injection h1 with h1; cases h1; rfl

private theorem kemPk_inj_tr_ck {s₁ s₂ : DY.Bytes} (h : PQKem.kemPk s₁ = PQKem.kemPk s₂) : s₁ = s₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.PQKem.Pk.SubF) { sk := s₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.PQKem.Pk.SubF) { sk := s₂ }
  change DY.Bytes.view? (PQKem.kemPk s₁) _ = _ at h1
  change DY.Bytes.view? (PQKem.kemPk s₂) _ = _ at h2
  rw [h, h2] at h1; injection h1 with h1; cases h1; rfl

private theorem dh_eq_pack_ck (p s : DY.Bytes) :
    ∃ pk' sk', DiffieHellman.dh p s = ({ pk := pk', sk := sk' } : DiffieHellman.Dh.SubF DY.Bytes).pack := by
  dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh]; split <;> [split <;> exact ⟨_, _, rfl⟩; exact ⟨_, _, rfl⟩]

private theorem spqrSend_snd_fst_eq_ck (st coins : DY.Bytes) :
    (∃ k p i, (Spqr.spqrSend st coins).2.1 = Spqr.spqrChainKey k p i) ∨
    (∃ x : Spqr.SendKey.SubF DY.Bytes, (Spqr.spqrSend st coins).2.1 = x.pack) := by
  dsimp only [Spqr.spqrSend]; split <;> [exact .inl ⟨_, _, _, rfl⟩; exact .inr ⟨_, rfl⟩]

private theorem spqrRecv_snd_eq_ck {st msg : DY.Bytes} {idx : UInt32} {r : DY.Bytes × DY.Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) :
    r.2 = Spqr.zeroKey ∨ (∃ k p i, r.2 = Spqr.spqrChainKey k p i) ∨
    (∃ x : Spqr.RecvKey.SubF DY.Bytes, r.2 = x.pack) := by
  unfold Spqr.spqrRecv at hrecv; split at hrecv
  · cases hrecv
  · split at hrecv
    · split at hrecv
      · injection hrecv with hr; rw [← hr]; dsimp only; split
        · exact .inl rfl
        · exact .inr (.inl ⟨_, _, _, rfl⟩)
      · cases hrecv
    · injection hrecv with hr; rw [← hr]; exact .inr (.inr ⟨_, rfl⟩)

private theorem concat_inj_ck {l₁ r₁ l₂ r₂ : DY.Bytes}
    (h : Concat.concat l₁ r₁ = Concat.concat l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.Concat.Concat.SubF) { lhs := l₁, rhs := r₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.Concat.Concat.SubF) { lhs := l₂, rhs := r₂ }
  change DY.Bytes.view? (Concat.concat l₁ r₁) _ = _ at h1
  change DY.Bytes.view? (Concat.concat l₂ r₂) _ = _ at h2
  rw [h, h2] at h1; injection h1 with h1; cases h1; exact ⟨rfl, rfl⟩

private theorem kdfExtract_inj_ck {s₁ i₁ s₂ i₂ : DY.Bytes}
    (h : KdfExtract.kdfExtract s₁ i₁ = KdfExtract.kdfExtract s₂ i₂) : s₁ = s₂ ∧ i₁ = i₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) { salt := s₁, ikm := i₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) { salt := s₂, ikm := i₂ }
  change DY.Bytes.view? (KdfExtract.kdfExtract s₁ i₁) _ = _ at h1
  change DY.Bytes.view? (KdfExtract.kdfExtract s₂ i₂) _ = _ at h2
  rw [h, h2] at h1; injection h1 with h1; cases h1; exact ⟨rfl, rfl⟩

private theorem spqrInit_pack_inj_ck {x₁ x₂ : Spqr.InitState.SubF DY.Bytes} (h : x₁.pack = x₂.pack) : x₁ = x₂ := by
  have h1 : DY.Bytes.view? x₁.pack DY.Spqr.InitState.SubF = some x₁ := DY.BytesView.view_pack x₁
  have h2 : DY.Bytes.view? x₂.pack DY.Spqr.InitState.SubF = some x₂ := DY.BytesView.view_pack x₂
  rw [h, h2] at h1; injection h1 with h1; exact h1.symm

private theorem spqrSendState_pack_inj_ck {x₁ x₂ : Spqr.SendState.SubF DY.Bytes} (h : x₁.pack = x₂.pack) : x₁ = x₂ := by
  have h1 : DY.Bytes.view? x₁.pack DY.Spqr.SendState.SubF = some x₁ := DY.BytesView.view_pack x₁
  have h2 : DY.Bytes.view? x₂.pack DY.Spqr.SendState.SubF = some x₂ := DY.BytesView.view_pack x₂
  rw [h, h2] at h1; injection h1 with h1; exact h1.symm

private theorem spqrRecvState_pack_inj_ck {x₁ x₂ : Spqr.RecvState.SubF DY.Bytes} (h : x₁.pack = x₂.pack) : x₁ = x₂ := by
  have h1 : DY.Bytes.view? x₁.pack DY.Spqr.RecvState.SubF = some x₁ := DY.BytesView.view_pack x₁
  have h2 : DY.Bytes.view? x₂.pack DY.Spqr.RecvState.SubF = some x₂ := DY.BytesView.view_pack x₂
  rw [h, h2] at h1; injection h1 with h1; exact h1.symm

end UnsealedInjectivity

/-! ## `TruncOKCkTR`, `KdfOKTR`, and `SafeCkTR` -/

/-- Every `Trunc.trunc8 inp` reachable by destructors from `AttackerKnows T` either has
`inp.AttackerKnows T` or was produced by `messageEncrypt` with an honest `SymEnc.symEnc` ciphertext
and a Diffie-Hellman public key ratchet key `dhPk a`. -/
def TruncOKCkTR (T : ExecTrace) (inp : DY.Bytes) : Prop :=
  inp.AttackerKnows T ∨
  ∃ pqSalt seed myIk peerIk a ns pn m pqMsg,
    inp = hmac (trMsgKeys pqSalt seed).macKey
      (Concat.concat myIk (Concat.concat peerIk
        (trHonestWireMsg (dhPk a) ns pn
          (SymEnc.symEnc (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv m) pqMsg)))

/-- Every `KdfExtract.kdfExtract s i` reachable by destructors from `AttackerKnows T` either has
both `s` and `i` attacker-known on `T`, or was produced by `kdfCk` (`0x01` with `SkippedKeyStored`,
or `0x02` with the result stored as a chain key), `createChain` (`"WhisperRatchet"` block 1 or 2), or `pqxdhKdf` (`pqxdhLabel` block 2 or 3). -/
def KdfOKTR (T : ExecTrace) (s i : DY.Bytes) : Prop :=
  (s.AttackerKnows T ∧ i.AttackerKnows T) ∨
  (i = litByte 0x01 ∧ ∃ j ses pk n rIdx src,
      T.EventLoggedAt (TREvent.SkippedKeyStored ses pk n (KdfExtract.kdfExtract s i) rIdx src) j) ∨
  (i = litByte 0x02 ∧ StoredCkTR T (KdfExtract.kdfExtract s i)) ∨
  i = Concat.concat (lit "WhisperRatchet") (litByte 1) ∨
  ∃ b1, IsRatchetOrPqxdhBlock23 b1 i

/-- Structural safety predicate for `DY.Libsignal.Composed` tracking `KdfExtract.kdfExtract`
and `Trunc.trunc8` subterms reachable by destructors and `invertDH`/`invertKEM`. -/
inductive SafeCkTR (T : ExecTrace) : DY.Bytes → Prop
  | atom {b : DY.Bytes} :
      DY.Bytes.view? b DY.Concat.Concat.SubF = none →
      DY.Bytes.view? b DY.KdfExtract.KdfExtract.SubF = none →
      DY.Bytes.view? b DY.SymEnc.Enc.SubF = none →
      DY.Bytes.view? b DY.Trunc.Trunc8.SubF = none →
      DY.Bytes.view? b DY.TrWire.TrWireMsg.SubF = none →
      DY.Bytes.view? b DY.X25519.Variant.SubF = none →
      DY.Bytes.view? b DY.Spqr.InitState.SubF = none →
      DY.Bytes.view? b DY.Spqr.SendState.SubF = none →
      DY.Bytes.view? b DY.Spqr.RecvState.SubF = none →
      DY.Bytes.view? b DY.DiffieHellman.DhPk.SubF = none →
      DY.Bytes.view? b DY.PQKem.Pk.SubF = none →
      SafeCkTR T b
  | concat {l r : DY.Bytes} :
      SafeCkTR T l → SafeCkTR T r → SafeCkTR T (Concat.concat l r)
  | kdfExtract {s i : DY.Bytes} :
      KdfOKTR T s i → SafeCkTR T (KdfExtract.kdfExtract s i)
  | symEnc {k iv m : DY.Bytes} :
      SafeCkTR T m → SafeCkTR T (SymEnc.symEnc k iv m)
  | trunc8 {inp : DY.Bytes} :
      TruncOKCkTR T inp → SafeCkTR T (Trunc.trunc8 inp)
  | trWireMsg (x : TrWire.TrWireMsg.SubF DY.Bytes) :
      SafeCkTR T x.senderRatchetKey →
      SafeCkTR T x.ciphertext → SafeCkTR T x.pqRatchet →
      SafeCkTR T x.pack
  | variant (x : X25519.Variant.SubF DY.Bytes) :
      SafeCkTR T x.key → SafeCkTR T x.pack
  | spqrInit (x : Spqr.InitState.SubF DY.Bytes) :
      SafeCkTR T x.authKey → SafeCkTR T x.params → SafeCkTR T x.pack
  | spqrSendState (x : Spqr.SendState.SubF DY.Bytes) :
      SafeCkTR T x.st → SafeCkTR T x.coins → SafeCkTR T x.pack
  | spqrRecvState (x : Spqr.RecvState.SubF DY.Bytes) :
      SafeCkTR T x.st → SafeCkTR T x.msg → SafeCkTR T x.pack
  | dhPk {sk : DY.Bytes} :
      SafeCkTR T sk → SafeCkTR T (DiffieHellman.dhPk sk)
  | kemPk {sk : DY.Bytes} :
      SafeCkTR T sk → SafeCkTR T (PQKem.kemPk sk)

section UnsealedHelpers
unseal DY.Bytes

theorem safeCkTR_random (T : ExecTrace) (r : DY.Random.SubF DY.Bytes) :
    SafeCkTR T (DY.Random.Random.pack r) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem safeCkTR_literal (T : ExecTrace) (b : ByteArray) :
    SafeCkTR T (Literal.literalToBytes b) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem safeCkTR_dh (T : ExecTrace) (pk sk : DY.Bytes) :
    SafeCkTR T (DiffieHellman.dh pk sk) := by
  obtain ⟨p₀, s₀, hdheq⟩ := dh_eq_pack_ck pk sk; rw [hdheq]
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem safeCkTR_kemEncap_fst (T : ExecTrace) (pk e : DY.Bytes) :
    SafeCkTR T (PQKem.kemEncap pk e).1 := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem safeCkTR_kemEncap_snd (T : ExecTrace) (pk e : DY.Bytes) :
    SafeCkTR T (PQKem.kemEncap pk e).2 := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

private theorem safeCkTR_kemRejKey (T : ExecTrace) (sk ct : DY.Bytes) :
    SafeCkTR T (PQKem.kemRejKey sk ct) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem safeCkTR_vk (T : ExecTrace) (sk : DY.Bytes) :
    SafeCkTR T (Signature.vk sk) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem safeCkTR_sign (T : ExecTrace) (sk nonce msg : DY.Bytes) :
    SafeCkTR T (Signature.sign sk nonce msg) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem safeCkTR_spqrChainKey (T : ExecTrace) (k p i : DY.Bytes) :
    SafeCkTR T (Spqr.spqrChainKey k p i) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem safeCkTR_spqrSend_state {T : ExecTrace} {st coins : DY.Bytes}
    (hst : SafeCkTR T st) (hc : SafeCkTR T coins) :
    SafeCkTR T (Spqr.spqrSend st coins).1 :=
  SafeCkTR.spqrSendState { st := st, coins := coins } hst hc

theorem safeCkTR_spqrSend_key (T : ExecTrace) (st coins : DY.Bytes) :
    SafeCkTR T (Spqr.spqrSend st coins).2.1 := by
  rcases spqrSend_snd_fst_eq_ck st coins with ⟨k, p, i, heq⟩ | ⟨x, heq⟩
  · rw [heq]; exact safeCkTR_spqrChainKey T k p i
  · rw [heq]
    refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem safeCkTR_spqrSend_msg (T : ExecTrace) (st coins : DY.Bytes) :
    SafeCkTR T (Spqr.spqrSend st coins).2.2 := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem safeCkTR_spqrRecv_state {T : ExecTrace} {st msg : DY.Bytes} {idx : UInt32}
    {r : DY.Bytes × DY.Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r)
    (hst : SafeCkTR T st) (hmsg : SafeCkTR T msg) : SafeCkTR T r.1 := by
  rw [Spqr.spqrRecv_state st msg idx r hrecv]
  exact SafeCkTR.spqrRecvState { st := st, msg := msg } hst hmsg

theorem safeCkTR_spqrRecv_key {T : ExecTrace} {st msg : DY.Bytes} {idx : UInt32}
    {r : DY.Bytes × DY.Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r) : SafeCkTR T r.2 := by
  rcases spqrRecv_snd_eq_ck hrecv with heq | ⟨k, p, i, heq⟩ | ⟨x, heq⟩
  · rw [heq]; exact safeCkTR_literal T _
  · rw [heq]; exact safeCkTR_spqrChainKey T k p i
  · rw [heq]
    refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem safeCkTR_concat_iff {T : ExecTrace} (l r : DY.Bytes) :
    SafeCkTR T (Concat.concat l r) ↔ SafeCkTR T l ∧ SafeCkTR T r := by
  refine ⟨fun hs => ?_, fun ⟨hl, hr⟩ => SafeCkTR.concat hl hr⟩
  generalize hx : Concat.concat l r = x at hs
  have hview : DY.Bytes.view? x DY.Concat.Concat.SubF = some { lhs := l, rhs := r } := by
    rw [← hx]; exact DY.BytesView.view_pack (SubF := DY.Concat.Concat.SubF) { lhs := l, rhs := r }
  cases hs
  case atom hc _ _ _ _ _ _ _ _ _ _ => rw [hc] at hview; contradiction
  case concat hl hr => rcases concat_inj_ck hx with ⟨rfl, rfl⟩; exact ⟨hl, hr⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem safeCkTR_kdfExtract_iff {T : ExecTrace} (s i : DY.Bytes) :
    SafeCkTR T (KdfExtract.kdfExtract s i) ↔ KdfOKTR T s i := by
  refine ⟨fun hs => ?_, SafeCkTR.kdfExtract⟩
  generalize hx : KdfExtract.kdfExtract s i = x at hs
  have hview : DY.Bytes.view? x DY.KdfExtract.KdfExtract.SubF = some { salt := s, ikm := i } := by
    rw [← hx]; exact DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) { salt := s, ikm := i }
  cases hs
  case atom _ hk _ _ _ _ _ _ _ _ _ => rw [hk] at hview; contradiction
  case kdfExtract h => rcases kdfExtract_inj_ck hx with ⟨rfl, rfl⟩; exact h
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem safeCkTR_symEnc_iff {T : ExecTrace} (k iv m : DY.Bytes) :
    SafeCkTR T (SymEnc.symEnc k iv m) ↔ SafeCkTR T m := by
  refine ⟨fun hs => ?_, SafeCkTR.symEnc⟩
  generalize hx : SymEnc.symEnc k iv m = x at hs
  have hview : DY.Bytes.view? x DY.SymEnc.Enc.SubF = some { key := k, iv := iv, msg := m } := by
    rw [← hx]; exact DY.BytesView.view_pack (SubF := DY.SymEnc.Enc.SubF) { key := k, iv := iv, msg := m }
  cases hs
  case atom _ _ he _ _ _ _ _ _ _ _ => rw [he] at hview; contradiction
  case symEnc hm => rcases symEnc_inj_ck hx with ⟨rfl, rfl, rfl⟩; exact hm
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem safeCkTR_trWireMsg_iff {T : ExecTrace} (w : TrWire.TrWireMsg.SubF DY.Bytes) :
    SafeCkTR T w.pack ↔
      SafeCkTR T w.senderRatchetKey ∧ SafeCkTR T w.ciphertext ∧ SafeCkTR T w.pqRatchet := by
  refine ⟨fun hs => ?_, fun ⟨h1, h2, h3⟩ => SafeCkTR.trWireMsg w h1 h2 h3⟩
  generalize hx : w.pack = x at hs
  have hview : DY.Bytes.view? x DY.TrWire.TrWireMsg.SubF = some w := by rw [← hx]; exact DY.BytesView.view_pack w
  cases hs
  case atom _ _ _ _ htw _ _ _ _ _ _ => rw [htw] at hview; contradiction
  case trWireMsg w' h1 h2 h3 => obtain rfl := trWireMsg_pack_inj_ck hx; exact ⟨h1, h2, h3⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem safeCkTR_variant_iff {T : ExecTrace} (v : X25519.Variant.SubF DY.Bytes) :
    SafeCkTR T v.pack ↔ SafeCkTR T v.key := by
  refine ⟨fun hs => ?_, SafeCkTR.variant v⟩
  generalize hx : v.pack = x at hs
  have hview : DY.Bytes.view? x DY.X25519.Variant.SubF = some v := by rw [← hx]; exact DY.BytesView.view_pack v
  cases hs
  case atom _ _ _ _ _ hv _ _ _ _ _ => rw [hv] at hview; contradiction
  case variant v' hk => obtain rfl := variant_pack_inj_ck hx; exact hk
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem safeCkTR_spqrInit_iff {T : ExecTrace} (x : Spqr.InitState.SubF DY.Bytes) :
    SafeCkTR T x.pack ↔ SafeCkTR T x.authKey ∧ SafeCkTR T x.params := by
  refine ⟨fun hs => ?_, fun ⟨hk, hp⟩ => SafeCkTR.spqrInit x hk hp⟩
  generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.InitState.SubF = some x := by rw [← hx]; exact DY.BytesView.view_pack x
  cases hs
  case atom _ _ _ _ _ _ hi _ _ _ _ => rw [hi] at hview; contradiction
  case spqrInit x' hk hp => obtain rfl := spqrInit_pack_inj_ck hx; exact ⟨hk, hp⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem safeCkTR_spqrSendState_iff {T : ExecTrace} (x : Spqr.SendState.SubF DY.Bytes) :
    SafeCkTR T x.pack ↔ SafeCkTR T x.st ∧ SafeCkTR T x.coins := by
  refine ⟨fun hs => ?_, fun ⟨hst, hc⟩ => SafeCkTR.spqrSendState x hst hc⟩
  generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.SendState.SubF = some x := by rw [← hx]; exact DY.BytesView.view_pack x
  cases hs
  case atom _ _ _ _ _ _ _ hss _ _ _ => rw [hss] at hview; contradiction
  case spqrSendState x' hst hc => obtain rfl := spqrSendState_pack_inj_ck hx; exact ⟨hst, hc⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem safeCkTR_spqrRecvState_iff {T : ExecTrace} (x : Spqr.RecvState.SubF DY.Bytes) :
    SafeCkTR T x.pack ↔ SafeCkTR T x.st ∧ SafeCkTR T x.msg := by
  refine ⟨fun hs => ?_, fun ⟨hst, hm⟩ => SafeCkTR.spqrRecvState x hst hm⟩
  generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.RecvState.SubF = some x := by rw [← hx]; exact DY.BytesView.view_pack x
  cases hs
  case atom _ _ _ _ _ _ _ _ hrs _ _ => rw [hrs] at hview; contradiction
  case spqrRecvState x' hst hm => obtain rfl := spqrRecvState_pack_inj_ck hx; exact ⟨hst, hm⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem safeCkTR_dhPk_iff {T : ExecTrace} (sk : DY.Bytes) :
    SafeCkTR T (DiffieHellman.dhPk sk) ↔ SafeCkTR T sk := by
  refine ⟨fun hs => ?_, SafeCkTR.dhPk⟩
  generalize hx : DiffieHellman.dhPk sk = y at hs
  have hview : DY.Bytes.view? y DY.DiffieHellman.DhPk.SubF = some { sk := sk } := by
    rw [← hx]; exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := sk }
  cases hs
  case atom _ _ _ _ _ _ _ _ _ hd _ => rw [hd] at hview; contradiction
  case dhPk hsk => obtain rfl := dhPk_inj_tr_ck hx; exact hsk
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem safeCkTR_kemPk_iff {T : ExecTrace} (sk : DY.Bytes) :
    SafeCkTR T (PQKem.kemPk sk) ↔ SafeCkTR T sk := by
  refine ⟨fun hs => ?_, SafeCkTR.kemPk⟩
  generalize hx : PQKem.kemPk sk = y at hs
  have hview : DY.Bytes.view? y DY.PQKem.Pk.SubF = some { sk := sk } := by
    rw [← hx]; exact DY.BytesView.view_pack (SubF := DY.PQKem.Pk.SubF) { sk := sk }
  cases hs
  case atom _ _ _ _ _ _ _ _ _ _ hk => rw [hk] at hview; contradiction
  case kemPk hsk => obtain rfl := kemPk_inj_tr_ck hx; exact hsk
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem safeCkTR_x25519Key {T : ExecTrace} {pk : DY.Bytes} (h : SafeCkTR T pk) :
    SafeCkTR T (X25519.normalizeX25519Key pk) := by
  unfold X25519.normalizeX25519Key; have hpack := DY.Bytes.pack_view? X25519.Variant.SubF pk
  rcases hv : pk.view? X25519.Variant.SubF with _ | x
  · exact h
  · rw [hv] at hpack; dsimp only at hpack; rw [← hpack] at h; exact (safeCkTR_variant_iff x).mp h

theorem safeCkTR_x25519TorsionVariant {T : ExecTrace} {key : DY.Bytes} (v : Fin 4) (t : Fin 8 := 0)
    (h : SafeCkTR T key) : SafeCkTR T (X25519.x25519TorsionVariant key v t) := by
  dsimp only [X25519.x25519TorsionVariant]
  split
  · exact safeCkTR_x25519Key h
  · exact SafeCkTR.variant { key := X25519.normalizeX25519Key key, variation := v, torsion := t } (safeCkTR_x25519Key h)

end UnsealedHelpers

/-! ## Monotonicity and closure under `AttackerKnowledge` -/

theorem StoredCkTR.mono {T T' : ExecTrace} (hle : T ≤ T') {x : DY.Bytes}
    (h : StoredCkTR T x) : StoredCkTR T' x := by
  obtain ⟨p, st, i, hat, hx⟩ := h
  exact ⟨p, st, i, Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle hat, hx⟩

theorem KdfOKTR.mono {T T' : ExecTrace} (hle : T ≤ T') {s i : DY.Bytes}
    (h : KdfOKTR T s i) : KdfOKTR T' s i := by
  rcases h with ⟨hs, hi⟩ | ⟨h01, j, ses, pk, n, rIdx, src, hev⟩ | ⟨h02, hst⟩ | hwr1 | hwr2
  · exact .inl ⟨DY.Bytes.AttackerKnows_le s T T' hle hs, DY.Bytes.AttackerKnows_le i T T' hle hi⟩
  · exact .inr (.inl ⟨h01, j, ses, pk, n, rIdx, src, evAt_mono hle hev⟩)
  · exact .inr (.inr (.inl ⟨h02, hst.mono hle⟩))
  · exact .inr (.inr (.inr (.inl hwr1)))
  · exact .inr (.inr (.inr (.inr hwr2)))

theorem TruncOKCkTR.mono {T T' : ExecTrace} (hle : T ≤ T') {inp : DY.Bytes}
    (h : TruncOKCkTR T inp) : TruncOKCkTR T' inp :=
  h.imp (DY.Bytes.AttackerKnows_le inp T T' hle) id

theorem SafeCkTR.mono {T T' : ExecTrace} (hle : T ≤ T') {b : DY.Bytes}
    (h : SafeCkTR T b) : SafeCkTR T' b := by
  induction h with
  | atom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 => exact .atom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  | concat _ _ ih1 ih2 => exact .concat ih1 ih2
  | kdfExtract h => exact .kdfExtract (h.mono hle)
  | symEnc _ ih => exact .symEnc ih
  | trunc8 h => exact .trunc8 (h.mono hle)
  | trWireMsg x _ _ _ ih1 ih2 ih3 => exact .trWireMsg x ih1 ih2 ih3
  | variant x _ ih => exact .variant x ih
  | spqrInit x _ _ ih1 ih2 => exact .spqrInit x ih1 ih2
  | spqrSendState x _ _ ih1 ih2 => exact .spqrSendState x ih1 ih2
  | spqrRecvState x _ _ ih1 ih2 => exact .spqrRecvState x ih1 ih2
  | dhPk _ ih => exact .dhPk ih
  | kemPk _ ih => exact .kemPk ih

def AGCkTR (T : ExecTrace) (b : DY.Bytes) : Prop :=
  b.AttackerKnows T ∧ SafeCkTR T b

set_option maxHeartbeats 400000 in
theorem agCkTR_closed_under_attackerKnowledge (T : ExecTrace) :
    SubAttackerKnowledge.Implies AttackerKnowledge.attackerKnowledge (AGCkTR T) := by
  change SubAttackerKnowledge.Implies
    DY.Libsignal.Composed.attackerKnowledge (AGCkTR T)
  dsimp [DY.Libsignal.Composed.attackerKnowledge]
  apply SubAttackerKnowledge.combine.implies
  rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, hlt⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Random.attackerKnowledge]
    intro b hb; rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at hb; exact hb.elim
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Literal.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | n, _⟩
    · intro b hb; dsimp [Literal.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at hb
      rcases hb with ⟨bs, rfl⟩; exact ⟨Literal.attacker_knows_literalToBytes bs T, safeCkTR_literal T bs⟩
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Concat.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | n, _⟩
    · intro b hb; dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at hb
      rcases hb with ⟨lhs, rhs, rfl, ⟨hl_ak, hl_s⟩, ⟨hr_ak, hr_s⟩⟩
      exact ⟨Concat.attacker_knows_concat lhs rhs T hl_ak hr_ak, SafeCkTR.concat hl_s hr_s⟩
    · intro b hb; dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, rhs, i, hsplit, ⟨hinp_ak, hinp_s⟩⟩
      have heq := Concat.concat_split inp i b rhs hsplit.symm
      exact ⟨DY.Bytes.AttackerKnows.prove Concat.splitLeft.attackerKnowledge b T
        (by rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred]; exact ⟨inp, rhs, i, hsplit, hinp_ak⟩),
        ((safeCkTR_concat_iff b rhs).mp (heq ▸ hinp_s)).1⟩
    · intro b hb; dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, lhs, i, hsplit, ⟨hinp_ak, hinp_s⟩⟩
      have heq := Concat.concat_split inp i lhs b hsplit.symm
      exact ⟨DY.Bytes.AttackerKnows.prove Concat.splitRight.attackerKnowledge b T
        (by rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred]; exact ⟨inp, lhs, i, hsplit, hinp_ak⟩),
        ((safeCkTR_concat_iff lhs b).mp (heq ▸ hinp_s)).2⟩
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DiffieHellman.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩
    · intro b hb; dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, ⟨hsk_ak, hsk_s⟩⟩
      exact ⟨DiffieHellman.attacker_knows_dhPk sk T hsk_ak, SafeCkTR.dhPk hsk_s⟩
    · intro b hb; dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hb
      rcases hb with ⟨pk, sk, rfl, ⟨hpk_ak, _⟩, ⟨hsk_ak, _⟩⟩
      exact ⟨DiffieHellman.attacker_knows_dh pk sk T hpk_ak hsk_ak, safeCkTR_dh T pk sk⟩
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, KdfExtract.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | n, _⟩
    · intro b hb; dsimp [KdfExtract.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hb
      rcases hb with ⟨salt, ikm, rfl, ⟨hs_ak, _⟩, ⟨hi_ak, _⟩⟩
      exact ⟨KdfExtract.attacker_knows_kdfExtract salt ikm T hs_ak hi_ak,
        SafeCkTR.kdfExtract (.inl ⟨hs_ak, hi_ak⟩)⟩
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, SymEnc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩
    · rintro b ⟨k, iv, msg, rfl, ⟨hk_ak, _⟩, ⟨hiv_ak, _⟩, ⟨hm_ak, hm_s⟩⟩
      exact ⟨SymEnc.attacker_knows_symEnc k iv msg T hk_ak hiv_ak hm_ak, SafeCkTR.symEnc hm_s⟩
    · rintro b ⟨key, iv, ct, hdec, ⟨hk_ak, _⟩, ⟨hiv_ak, _⟩, ⟨hct_ak, hct_s⟩⟩
      have heq := SymEnc.symDec_eq_some key iv ct b hdec.symm; rw [heq] at hct_s
      exact ⟨SymEnc.attacker_knows_symDec key iv ct b T hk_ak hiv_ak hct_ak hdec.symm,
        (safeCkTR_symEnc_iff key iv b).mp hct_s⟩
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Trunc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | n, _⟩
    · rintro b ⟨m, rfl, ⟨hm_ak, _⟩⟩
      exact ⟨Trunc.attacker_knows_trunc8 m T hm_ak, SafeCkTR.trunc8 (.inl hm_ak)⟩
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, X25519.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩
    · rintro b ⟨key, v, t, rfl, ⟨hk_ak, hk_s⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove X25519.x25519Variant.attackerKnowledge _ T ⟨key, v, t, rfl, hk_ak⟩,
        safeCkTR_x25519TorsionVariant v t hk_s⟩
    · rintro b ⟨v, ⟨hv_ak, hv_s⟩, rfl⟩
      exact ⟨DY.Bytes.AttackerKnows.prove X25519.normalizeX25519Key.attackerKnowledge _ T ⟨v, hv_ak, rfl⟩,
        (safeCkTR_variant_iff v).mp hv_s⟩
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, PQKem.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | _ | _ | n, _⟩
    · rintro b ⟨sk, rfl, ⟨hsk_ak, hsk_s⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove PQKem.kemPk.attackerKnowledge _ T ⟨sk, rfl, hsk_ak⟩,
        SafeCkTR.kemPk hsk_s⟩
    · rintro b ⟨pk, e, rhs, heq, ⟨hpk_ak, _⟩, ⟨he_ak, _⟩⟩
      have h1 : b = (PQKem.kemEncap pk e).1 := congrArg Prod.fst heq
      refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemEncapCipher.attackerKnowledge b T ⟨pk, e, rhs, heq, hpk_ak, he_ak⟩, ?_⟩
      rw [h1]; exact safeCkTR_kemEncap_fst T pk e
    · rintro b ⟨pk, e, lhs, heq, ⟨hpk_ak, _⟩, ⟨he_ak, _⟩⟩
      have h2 : b = (PQKem.kemEncap pk e).2 := congrArg Prod.snd heq
      refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemEncapSS.attackerKnowledge b T ⟨pk, e, lhs, heq, hpk_ak, he_ak⟩, ?_⟩
      rw [h2]; exact safeCkTR_kemEncap_snd T pk e
    · rintro b ⟨sk, ct, hdec, ⟨hsk_ak, _⟩, ⟨hct_ak, _⟩⟩
      refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemDecap.attackerKnowledge b T ⟨sk, ct, hdec, hsk_ak, hct_ak⟩, ?_⟩
      obtain ⟨e, _, rfl⟩ := kemDecap_eq_some_iff.mp hdec.symm
      exact safeCkTR_kemEncap_snd T (PQKem.kemPk sk) e
    · rintro b ⟨sk, ct, rfl, ⟨hsk_ak, _⟩, ⟨hct_ak, _⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove PQKem.kemRejKey.attackerKnowledge _ T ⟨sk, ct, rfl, hsk_ak, hct_ak⟩,
        safeCkTR_kemRejKey T sk ct⟩
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Signature.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩
    · intro b hb; dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, ⟨hsk_ak, _⟩⟩
      exact ⟨Signature.attacker_knows_vk sk T hsk_ak, safeCkTR_vk T sk⟩
    · intro b hb; dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, nonce, msg, rfl, ⟨hsk_ak, _⟩, ⟨hnonce_ak, _⟩, ⟨hmsg_ak, _⟩⟩
      exact ⟨Signature.attacker_knows_sign sk nonce msg T hsk_ak hnonce_ak hmsg_ak,
        safeCkTR_sign T sk nonce msg⟩
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Spqr.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, _⟩
    · rintro b ⟨authKey, params, rfl, ⟨hk_ak, hk_s⟩, ⟨hp_ak, hp_s⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrInit.attackerKnowledge _ T ⟨authKey, params, rfl, hk_ak, hp_ak⟩,
        SafeCkTR.spqrInit { authKey := authKey, params := params } hk_s hp_s⟩
    · rintro b ⟨authKey, params, idx, rfl, ⟨hk_ak, _⟩, ⟨hp_ak, _⟩, ⟨hi_ak, _⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrChainKey.attackerKnowledge _ T ⟨authKey, params, idx, rfl, hk_ak, hp_ak, hi_ak⟩,
        safeCkTR_spqrChainKey T authKey params idx⟩
    · rintro b ⟨st, coins, rfl, ⟨hst_ak, hst_s⟩, ⟨hc_ak, hc_s⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendState.attackerKnowledge _ T ⟨st, coins, rfl, hst_ak, hc_ak⟩,
        safeCkTR_spqrSend_state hst_s hc_s⟩
    · rintro b ⟨st, coins, rfl, ⟨hst_ak, _⟩, ⟨hc_ak, _⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendKey.attackerKnowledge _ T ⟨st, coins, rfl, hst_ak, hc_ak⟩,
        safeCkTR_spqrSend_key T st coins⟩
    · rintro b ⟨st, coins, rfl, ⟨hst_ak, _⟩, ⟨hc_ak, _⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendMsg.attackerKnowledge _ T ⟨st, coins, rfl, hst_ak, hc_ak⟩,
        safeCkTR_spqrSend_msg T st coins⟩
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, ⟨hst_ak, hst_s⟩, ⟨hm_ak, hm_s⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrRecvState.attackerKnowledge _ T ⟨st, msg, idx, r, hrecv, rfl, hst_ak, hm_ak⟩,
        safeCkTR_spqrRecv_state hrecv hst_s hm_s⟩
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, ⟨hst_ak, _⟩, ⟨hm_ak, _⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrRecvKey.attackerKnowledge _ T ⟨st, msg, idx, r, hrecv, rfl, hst_ak, hm_ak⟩,
        safeCkTR_spqrRecv_key hrecv⟩
    · rintro b (⟨s, ⟨hs_ak, hs_s⟩, harg⟩ | ⟨s, ⟨hs_ak, hs_s⟩, harg⟩ | ⟨s, ⟨hs_ak, hs_s⟩, harg⟩)
      · have hargs := (safeCkTR_spqrInit_iff s).mp hs_s
        refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge b T (.inl ⟨s, hs_ak, harg⟩), ?_⟩
        rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
      · have hargs := (safeCkTR_spqrSendState_iff s).mp hs_s
        refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge b T (.inr (.inl ⟨s, hs_ak, harg⟩)), ?_⟩
        rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
      · have hargs := (safeCkTR_spqrRecvState_iff s).mp hs_s
        refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge b T (.inr (.inr ⟨s, hs_ak, harg⟩)), ?_⟩
        rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, TrWire.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩
    · rintro b ⟨w, rfl, ⟨h1_ak, h1_s⟩, ⟨h2_ak, h2_s⟩, ⟨h3_ak, h3_s⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove TrWire.trWireMsg.attackerKnowledge _ T
          ⟨w, rfl, h1_ak, h2_ak, h3_ak⟩,
        SafeCkTR.trWireMsg w h1_s h2_s h3_s⟩
    · rintro b ⟨w, ⟨hw_ak, hw_s⟩, hmem⟩
      have hargs_s := (safeCkTR_trWireMsg_iff w).mp hw_s
      refine ⟨DY.Bytes.AttackerKnows.prove TrWire.trWireMsgArg.attackerKnowledge b T ⟨w, hw_ak, hmem⟩, ?_⟩
      rcases hmem with rfl | rfl | rfl
      exacts [hargs_s.1, hargs_s.2.1, hargs_s.2.2]
    · omega
  · omega

theorem attackerKnows_imp_safeCkTR {T : ExecTrace}
    (hbase : ∀ b : DY.Bytes, T.BaseAttackerKnows b → SafeCkTR T b)
    {b : DY.Bytes} (hAK : b.AttackerKnows T) : SafeCkTR T b := by
  refine (DY.Bytes.AttackerKnows.is_least_fixpoint (AGCkTR T) b T
    (agCkTR_closed_under_attackerKnowledge T) (fun x hx => ?_) hAK).2
  simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hx
  exact ⟨DY.Bytes.AttackerKnows.prove_from_base x T hx, hbase x hx⟩

/-! ## Key-schedule and wire-message constructor helpers -/

theorem safeCkTR_kdfCk_fst {T : ExecTrace} {ck : DY.Bytes} (h : StoredCkTR T (kdfCk ck).1) :
    SafeCkTR T (kdfCk ck).1 :=
  SafeCkTR.kdfExtract (.inr (.inr (.inl ⟨rfl, h⟩)))

theorem safeCkTR_kdfCk_snd (T : ExecTrace) (ck : DY.Bytes)
    (h : ∃ j ses pk n rIdx src, T.EventLoggedAt (TREvent.SkippedKeyStored ses pk n (kdfCk ck).2 rIdx src) j) :
    SafeCkTR T (kdfCk ck).2 :=
  SafeCkTR.kdfExtract (.inr (.inl ⟨rfl, h⟩))

theorem safeCkTR_createChain_fst (T : ExecTrace) (rk pk sk : DY.Bytes) :
    SafeCkTR T (createChain rk pk sk).1 :=
  SafeCkTR.kdfExtract (.inr (.inr (.inr (.inl rfl))))

theorem safeCkTR_createChain_snd (T : ExecTrace) (rk pk sk : DY.Bytes) :
    SafeCkTR T (createChain rk pk sk).2 :=
  SafeCkTR.kdfExtract (.inr (.inr (.inr (.inr ⟨_, .inl rfl⟩))))

theorem safeCkTR_pqxdhKdf_ck (T : ExecTrace) (ikm : DY.Bytes) :
    SafeCkTR T (pqxdhKdf ikm).ck :=
  SafeCkTR.kdfExtract (.inr (.inr (.inr (.inr ⟨_, .inr (.inl rfl)⟩))))

theorem safeCkTR_pqxdhKdf_pqr (T : ExecTrace) (ikm : DY.Bytes) :
    SafeCkTR T (pqxdhKdf ikm).pqr :=
  SafeCkTR.kdfExtract (.inr (.inr (.inr (.inr ⟨_, .inr (.inr rfl)⟩))))

/-- A stored chain key `chainKeyAt ck0 n` is safe: `n = 0` from the base, `n + 1` from the
strengthened `0x02` clause (only the final key needs to be stored). -/
theorem safeCkTR_chainKeyAt (T : ExecTrace) {ck0 : DY.Bytes} (h0 : SafeCkTR T ck0) :
    ∀ n : Nat, StoredCkTR T (chainKeyAt ck0 n) → SafeCkTR T (chainKeyAt ck0 n)
  | 0, _ => h0
  | n + 1, hst => by
    rw [Symbolic.Swarm.COMPOSED.CompTermAlgebra.chainKeyAt_succ_eq_kdfCk_fst] at hst ⊢
    exact safeCkTR_kdfCk_fst hst

theorem safeCkTR_trHonestWireMsg {T : ExecTrace} {rk ct pqMsg : DY.Bytes} (ns pn : UInt32)
    (hrk : SafeCkTR T rk) (hct : SafeCkTR T ct) (hpq : SafeCkTR T pqMsg) :
    SafeCkTR T (trHonestWireMsg rk ns pn ct pqMsg) :=
  SafeCkTR.trWireMsg
    { version := messageVersion, senderRatchetKey := rk, counter := ns,
      previousCounter := pn, ciphertext := ct, pqRatchet := pqMsg,
      encodingVariation := DY.TrWire.canonicalVariation }
    hrk hct hpq

theorem safeCkTR_computeMac_honest (T : ExecTrace) (pqSalt seed myIk peerIk a : DY.Bytes)
    (ns pn : UInt32) (m pqMsg : DY.Bytes) :
    SafeCkTR T (computeMac (trMsgKeys pqSalt seed).macKey myIk peerIk
      (trHonestWireMsg (dhPk a) ns pn
        (SymEnc.symEnc (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv m) pqMsg)) :=
  SafeCkTR.trunc8 (.inr ⟨pqSalt, seed, myIk, peerIk, a, ns, pn, m, pqMsg, rfl⟩)

end Symbolic.Swarm.CREF.TR.G1
