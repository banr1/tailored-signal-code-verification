/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
import DY.ALaCarte.Basic
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.Literal
import Symbolic.DYBridge.DY.EquationalTheory.Concat
import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.MsgKeys
import Symbolic.Specifications.Model.TripleRatchet
import Symbolic.Specifications.Model.PQXDH
import Symbolic.Specifications.Model.Composed
public import Symbolic.Proofs.Swarm.COMPOSED.CompPresBob
public import Symbolic.Specifications.Refinement.TraceExplanation
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

/-!
# Strengthened MAC Truncation Safety Invariant

Defines `TruncSafeStrong` and `TruncStrongInv` over the composed state machine, recording
constructor-site sender-state and attacker-knowledge witnesses at `messageEncrypt`, and derives
`macKdfSafe_tr_trunc8_inv_strong`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyDir KeyComponent createChain
  consumeMessageKey computeMac setRecvChain findRecvChain recvChainFor hmac kdfCk chainKeyAt
  messageVersion x25519LowOrder maxReceiverChains)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles
  PreKeyMsgHandles opkUsedB KeyKind getKey registerIdentity registerCorruptIdentity genSignedPrekey
  genPQPrekey genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK compromiseOPK invertDH
  invertKEM)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open Symbolic.Swarm.COMPOSED.CompTermAlgebra (kemDecap_eq_some_iff)
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompPresPQXDH

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

abbrev ReachableTraceStrong (T : ExecTrace) : Prop :=
  T.Reachable DY.Libsignal.Composed.reachability

abbrev TTRStEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)

/-- State `st` is stored for participant `p` at trace index `i` of `tr`. -/
def TRStateStoredAt (p : Participant) (st : TRState) (i : Nat) (tr : ExecTrace) : Prop :=
  (tr.at? i : Option TTRStEntry) = some ⟨⟨p, st⟩⟩

section UnsealedInjectivity
unseal DY.Bytes

private theorem symEnc_inj_strong {k₁ iv₁ m₁ k₂ iv₂ m₂ : DY.Bytes}
    (h : SymEnc.symEnc k₁ iv₁ m₁ = SymEnc.symEnc k₂ iv₂ m₂) : k₁ = k₂ ∧ iv₁ = iv₂ ∧ m₁ = m₂ := by
  injection Symbolic.DYBridge.DY.BytesView.pack_inj.mp h with h1 h2 h3; exact ⟨h1, h2, h3⟩

private theorem trWireMsg_pack_inj_strong {w₁ w₂ : TrWire.TrWireMsg.SubF DY.Bytes} (h : w₁.pack = w₂.pack) : w₁ = w₂ :=
  Symbolic.DYBridge.DY.BytesView.pack_inj.mp h

private theorem variant_pack_inj_strong {v₁ v₂ : X25519.Variant.SubF DY.Bytes} (h : v₁.pack = v₂.pack) : v₁ = v₂ :=
  Symbolic.DYBridge.DY.BytesView.pack_inj.mp h

private theorem dhPk_inj_strong {s₁ s₂ : DY.Bytes} (h : DiffieHellman.dhPk s₁ = DiffieHellman.dhPk s₂) : s₁ = s₂ := by
  injection Symbolic.DYBridge.DY.BytesView.pack_inj.mp h

private theorem kemPk_inj_strong {s₁ s₂ : DY.Bytes} (h : PQKem.kemPk s₁ = PQKem.kemPk s₂) : s₁ = s₂ := by
  injection Symbolic.DYBridge.DY.BytesView.pack_inj.mp h

private theorem dh_eq_pack_strong (p s : DY.Bytes) :
    ∃ pk' sk', DiffieHellman.dh p s = ({ pk := pk', sk := sk' } : DiffieHellman.Dh.SubF DY.Bytes).pack := by
  dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh]; split <;> [split <;> exact ⟨_, _, rfl⟩; exact ⟨_, _, rfl⟩]

private theorem spqrSend_snd_fst_eq_strong (st coins : DY.Bytes) :
    (∃ k p i, (Spqr.spqrSend st coins).2.1 = Spqr.spqrChainKey k p i) ∨
    (∃ x : Spqr.SendKey.SubF DY.Bytes, (Spqr.spqrSend st coins).2.1 = x.pack) := by
  dsimp only [Spqr.spqrSend]; split <;> [exact .inl ⟨_, _, _, rfl⟩; exact .inr ⟨_, rfl⟩]

private theorem spqrRecv_snd_eq_strong {st msg : DY.Bytes} {idx : UInt32} {r : DY.Bytes × DY.Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) :
    r.2 = Spqr.zeroKey ∨ (∃ k p i, r.2 = Spqr.spqrChainKey k p i) ∨
    (∃ x : Spqr.RecvKey.SubF DY.Bytes, r.2 = x.pack) := by
  unfold Spqr.spqrRecv at hrecv; split at hrecv
  · cases hrecv
  · split at hrecv
    · split at hrecv
      · injection hrecv with hr; rw [← hr]; dsimp only; split <;> [exact .inl rfl; exact .inr (.inl ⟨_, _, _, rfl⟩)]
      · cases hrecv
    · injection hrecv with hr; rw [← hr]; exact .inr (.inr ⟨_, rfl⟩)

private theorem concat_inj_strong {l₁ r₁ l₂ r₂ : DY.Bytes} (h : Concat.concat l₁ r₁ = Concat.concat l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  injection Symbolic.DYBridge.DY.BytesView.pack_inj.mp h with h1 h2; exact ⟨h1, h2⟩

private theorem spqrInit_pack_inj_strong {x₁ x₂ : Spqr.InitState.SubF DY.Bytes} (h : x₁.pack = x₂.pack) : x₁ = x₂ :=
  Symbolic.DYBridge.DY.BytesView.pack_inj.mp h

private theorem spqrSendState_pack_inj_strong {x₁ x₂ : Spqr.SendState.SubF DY.Bytes} (h : x₁.pack = x₂.pack) : x₁ = x₂ :=
  Symbolic.DYBridge.DY.BytesView.pack_inj.mp h

private theorem spqrRecvState_pack_inj_strong {x₁ x₂ : Spqr.RecvState.SubF DY.Bytes} (h : x₁.pack = x₂.pack) : x₁ = x₂ :=
  Symbolic.DYBridge.DY.BytesView.pack_inj.mp h

end UnsealedInjectivity

/-! ## `TruncInputValidTRStrong` and `TruncSafeStrong` -/

/-- Strengthened `Trunc.trunc8` input validity predicate on trace `T`, recording the constructor-site
attacker-knowability and sender-state witnesses from `TripleRatchet.messageEncrypt`. -/
def TruncInputValidTRStrong (T : ExecTrace) (inp : DY.Bytes) : Prop :=
  inp.AttackerKnows T ∨
  ∃ (pqSalt seed myIk peerIk a : DY.Bytes) (ns pn : UInt32) (m pqMsg : DY.Bytes)
    (t_s stH : Nat) (me : Participant) (st_s : TRState),
    inp = hmac (trMsgKeys pqSalt seed).macKey
      (Concat.concat myIk (Concat.concat peerIk
        (trHonestWireMsg (dhPk a) ns pn
          (SymEnc.symEnc (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv m) pqMsg))) ∧
    pqSalt.AttackerKnows T ∧
    (Concat.concat
      (trHonestWireMsg (dhPk a) ns pn
        (SymEnc.symEnc (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv m) pqMsg)
      (Trunc.trunc8 inp)).AttackerKnows T ∧
    a = randTerm t_s 32 ∧
    TRStateStoredAt me st_s stH T ∧
    st_s.myIk = myIk ∧
    st_s.peerIk = peerIk ∧
    (kdfCk st_s.cks).2 = seed

inductive TruncSafeStrong (T : ExecTrace) : DY.Bytes → Prop
  | atom {b : DY.Bytes} :
      DY.Bytes.view? b DY.Concat.Concat.SubF = none → DY.Bytes.view? b DY.SymEnc.Enc.SubF = none →
      DY.Bytes.view? b DY.Trunc.Trunc8.SubF = none →
      DY.Bytes.view? b DY.TrWire.TrWireMsg.SubF = none → DY.Bytes.view? b DY.X25519.Variant.SubF = none →
      DY.Bytes.view? b DY.Spqr.InitState.SubF = none → DY.Bytes.view? b DY.Spqr.SendState.SubF = none →
      DY.Bytes.view? b DY.Spqr.RecvState.SubF = none → DY.Bytes.view? b DY.DiffieHellman.DhPk.SubF = none →
      DY.Bytes.view? b DY.PQKem.Pk.SubF = none →
      TruncSafeStrong T b
  | concat {l r : DY.Bytes} : TruncSafeStrong T l → TruncSafeStrong T r → TruncSafeStrong T (Concat.concat l r)
  | symEnc {k iv m : DY.Bytes} : TruncSafeStrong T m → TruncSafeStrong T (SymEnc.symEnc k iv m)
  | trunc8 {inp : DY.Bytes} : TruncInputValidTRStrong T inp → TruncSafeStrong T (Trunc.trunc8 inp)
  | trWireMsg (x : TrWire.TrWireMsg.SubF DY.Bytes) :
      TruncSafeStrong T x.senderRatchetKey → TruncSafeStrong T x.ciphertext → TruncSafeStrong T x.pqRatchet →
      TruncSafeStrong T x.pack
  | variant (x : X25519.Variant.SubF DY.Bytes) : TruncSafeStrong T x.key → TruncSafeStrong T x.pack
  | spqrInit (x : Spqr.InitState.SubF DY.Bytes) : TruncSafeStrong T x.authKey → TruncSafeStrong T x.params → TruncSafeStrong T x.pack
  | spqrSendState (x : Spqr.SendState.SubF DY.Bytes) : TruncSafeStrong T x.st → TruncSafeStrong T x.coins → TruncSafeStrong T x.pack
  | spqrRecvState (x : Spqr.RecvState.SubF DY.Bytes) : TruncSafeStrong T x.st → TruncSafeStrong T x.msg → TruncSafeStrong T x.pack
  | dhPk {sk : DY.Bytes} : TruncSafeStrong T sk → TruncSafeStrong T (DiffieHellman.dhPk sk)
  | kemPk {sk : DY.Bytes} : TruncSafeStrong T sk → TruncSafeStrong T (PQKem.kemPk sk)

section UnsealedStrongHelpers
unseal DY.Bytes

theorem truncSafeStrong_random (T : ExecTrace) (r : DY.Random.SubF DY.Bytes) :
    TruncSafeStrong T (DY.Random.Random.pack r) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem truncSafeStrong_literal (T : ExecTrace) (b : ByteArray) :
    TruncSafeStrong T (Literal.literalToBytes b) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem truncSafeStrong_dh (T : ExecTrace) (pk sk : DY.Bytes) : TruncSafeStrong T (DiffieHellman.dh pk sk) := by
  obtain ⟨_, _, h⟩ := dh_eq_pack_strong pk sk; rw [h]
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem truncSafeStrong_kdfExtract (T : ExecTrace) (s i : DY.Bytes) :
    TruncSafeStrong T (KdfExtract.kdfExtract s i) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem truncSafeStrong_kemEncap_fst (T : ExecTrace) (pk e : DY.Bytes) :
    TruncSafeStrong T (PQKem.kemEncap pk e).1 := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem truncSafeStrong_kemEncap_snd (T : ExecTrace) (pk e : DY.Bytes) :
    TruncSafeStrong T (PQKem.kemEncap pk e).2 := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
private theorem truncSafeStrong_kemRejKey (T : ExecTrace) (sk ct : DY.Bytes) :
    TruncSafeStrong T (PQKem.kemRejKey sk ct) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem truncSafeStrong_vk (T : ExecTrace) (sk : DY.Bytes) :
    TruncSafeStrong T (Signature.vk sk) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem truncSafeStrong_sign (T : ExecTrace) (sk nonce msg : DY.Bytes) :
    TruncSafeStrong T (Signature.sign sk nonce msg) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem truncSafeStrong_spqrChainKey (T : ExecTrace) (k p i : DY.Bytes) :
    TruncSafeStrong T (Spqr.spqrChainKey k p i) := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem truncSafeStrong_spqrSend_state {T : ExecTrace} {st coins : DY.Bytes}
    (hst : TruncSafeStrong T st) (hc : TruncSafeStrong T coins) :
    TruncSafeStrong T (Spqr.spqrSend st coins).1 := .spqrSendState { st := st, coins := coins } hst hc
theorem truncSafeStrong_spqrSend_key (T : ExecTrace) (st coins : DY.Bytes) :
    TruncSafeStrong T (Spqr.spqrSend st coins).2.1 := by
  rcases spqrSend_snd_fst_eq_strong st coins with ⟨k, p, i, h⟩ | ⟨_, h⟩ <;> rw [h]
  · exact truncSafeStrong_spqrChainKey T k p i
  · refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem truncSafeStrong_spqrSend_msg (T : ExecTrace) (st coins : DY.Bytes) :
    TruncSafeStrong T (Spqr.spqrSend st coins).2.2 := by
  refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem truncSafeStrong_spqrRecv_state {T : ExecTrace} {st msg : DY.Bytes} {idx : UInt32}
    {r : DY.Bytes × DY.Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r)
    (hst : TruncSafeStrong T st) (hmsg : TruncSafeStrong T msg) : TruncSafeStrong T r.1 := by
  rw [Spqr.spqrRecv_state st msg idx r hrecv]; exact .spqrRecvState { st := st, msg := msg } hst hmsg
theorem truncSafeStrong_spqrRecv_key {T : ExecTrace} {st msg : DY.Bytes} {idx : UInt32}
    {r : DY.Bytes × DY.Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r) : TruncSafeStrong T r.2 := by
  rcases spqrRecv_snd_eq_strong hrecv with h | ⟨k, p, i, h⟩ | ⟨_, h⟩ <;> rw [h]
  · exact truncSafeStrong_literal T _
  · exact truncSafeStrong_spqrChainKey T k p i
  · refine .atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem truncSafeStrong_concat_iff {T : ExecTrace} (l r : DY.Bytes) :
    TruncSafeStrong T (Concat.concat l r) ↔ TruncSafeStrong T l ∧ TruncSafeStrong T r := by
  refine ⟨fun hs => ?_, fun ⟨hl, hr⟩ => .concat hl hr⟩; generalize hx : Concat.concat l r = x at hs
  have hview : DY.Bytes.view? x DY.Concat.Concat.SubF = some { lhs := l, rhs := r } := by rw [← hx]; exact DY.BytesView.view_pack _
  cases hs
  case atom hc _ _ _ _ _ _ _ _ _ => rw [hc] at hview; contradiction
  case concat hl hr => rcases concat_inj_strong hx with ⟨rfl, rfl⟩; exact ⟨hl, hr⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem truncSafeStrong_symEnc_iff {T : ExecTrace} (k iv m : DY.Bytes) :
    TruncSafeStrong T (SymEnc.symEnc k iv m) ↔ TruncSafeStrong T m := by
  refine ⟨fun hs => ?_, .symEnc⟩; generalize hx : SymEnc.symEnc k iv m = x at hs
  have hview : DY.Bytes.view? x DY.SymEnc.Enc.SubF = some { key := k, iv := iv, msg := m } := by rw [← hx]; exact DY.BytesView.view_pack _
  cases hs
  case atom _ he _ _ _ _ _ _ _ _ => rw [he] at hview; contradiction
  case symEnc hm => rcases symEnc_inj_strong hx with ⟨rfl, rfl, rfl⟩; exact hm
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem truncSafeStrong_trunc8_iff {T : ExecTrace} (inp : DY.Bytes) :
    TruncSafeStrong T (Trunc.trunc8 inp) ↔ TruncInputValidTRStrong T inp := by
  refine ⟨fun hs => ?_, .trunc8⟩; generalize hx : Trunc.trunc8 inp = x at hs
  have hview : DY.Bytes.view? x DY.Trunc.Trunc8.SubF = some { input := inp } := by rw [← hx]; exact DY.BytesView.view_pack _
  cases hs
  case atom _ _ ht _ _ _ _ _ _ _ => rw [ht] at hview; contradiction
  case trunc8 h => obtain rfl := Trunc.trunc8_inj _ _ hx; exact h
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem truncSafeStrong_trWireMsg_iff {T : ExecTrace} (w : TrWire.TrWireMsg.SubF DY.Bytes) :
    TruncSafeStrong T w.pack ↔
      TruncSafeStrong T w.senderRatchetKey ∧ TruncSafeStrong T w.ciphertext ∧ TruncSafeStrong T w.pqRatchet := by
  refine ⟨fun hs => ?_, fun ⟨h1, h2, h3⟩ => .trWireMsg w h1 h2 h3⟩; generalize hx : w.pack = x at hs
  have hview : DY.Bytes.view? x DY.TrWire.TrWireMsg.SubF = some w := by rw [← hx]; exact DY.BytesView.view_pack w
  cases hs
  case atom _ _ _ htw _ _ _ _ _ _ => rw [htw] at hview; contradiction
  case trWireMsg w' h1 h2 h3 => obtain rfl := trWireMsg_pack_inj_strong hx; exact ⟨h1, h2, h3⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem truncSafeStrong_variant_iff {T : ExecTrace} (v : X25519.Variant.SubF DY.Bytes) :
    TruncSafeStrong T v.pack ↔ TruncSafeStrong T v.key := by
  refine ⟨fun hs => ?_, .variant v⟩; generalize hx : v.pack = x at hs
  have hview : DY.Bytes.view? x DY.X25519.Variant.SubF = some v := by rw [← hx]; exact DY.BytesView.view_pack v
  cases hs
  case atom _ _ _ _ hv _ _ _ _ _ => rw [hv] at hview; contradiction
  case variant v' hk => obtain rfl := variant_pack_inj_strong hx; exact hk
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem truncSafeStrong_spqrInit_iff {T : ExecTrace} (x : Spqr.InitState.SubF DY.Bytes) :
    TruncSafeStrong T x.pack ↔ TruncSafeStrong T x.authKey ∧ TruncSafeStrong T x.params := by
  refine ⟨fun hs => ?_, fun ⟨hk, hp⟩ => .spqrInit x hk hp⟩; generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.InitState.SubF = some x := by rw [← hx]; exact DY.BytesView.view_pack x
  cases hs
  case atom _ _ _ _ _ hi _ _ _ _ => rw [hi] at hview; contradiction
  case spqrInit x' hk hp => obtain rfl := spqrInit_pack_inj_strong hx; exact ⟨hk, hp⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem truncSafeStrong_spqrSendState_iff {T : ExecTrace} (x : Spqr.SendState.SubF DY.Bytes) :
    TruncSafeStrong T x.pack ↔ TruncSafeStrong T x.st ∧ TruncSafeStrong T x.coins := by
  refine ⟨fun hs => ?_, fun ⟨hst, hc⟩ => .spqrSendState x hst hc⟩; generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.SendState.SubF = some x := by rw [← hx]; exact DY.BytesView.view_pack x
  cases hs
  case atom _ _ _ _ _ _ hs' _ _ _ => rw [hs'] at hview; contradiction
  case spqrSendState x' hst hc => obtain rfl := spqrSendState_pack_inj_strong hx; exact ⟨hst, hc⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem truncSafeStrong_spqrRecvState_iff {T : ExecTrace} (x : Spqr.RecvState.SubF DY.Bytes) :
    TruncSafeStrong T x.pack ↔ TruncSafeStrong T x.st ∧ TruncSafeStrong T x.msg := by
  refine ⟨fun hs => ?_, fun ⟨hst, hm⟩ => .spqrRecvState x hst hm⟩; generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.RecvState.SubF = some x := by rw [← hx]; exact DY.BytesView.view_pack x
  cases hs
  case atom _ _ _ _ _ _ _ hrs _ _ => rw [hrs] at hview; contradiction
  case spqrRecvState x' hst hm => obtain rfl := spqrRecvState_pack_inj_strong hx; exact ⟨hst, hm⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem truncSafeStrong_dhPk_iff {T : ExecTrace} (sk : DY.Bytes) :
    TruncSafeStrong T (DiffieHellman.dhPk sk) ↔ TruncSafeStrong T sk := by
  refine ⟨fun hs => ?_, .dhPk⟩; generalize hx : DiffieHellman.dhPk sk = y at hs
  have hview : DY.Bytes.view? y DY.DiffieHellman.DhPk.SubF = some { sk := sk } := by rw [← hx]; exact DY.BytesView.view_pack _
  cases hs
  case atom _ _ _ _ _ _ _ _ hd _ => rw [hd] at hview; contradiction
  case dhPk hsk => obtain rfl := dhPk_inj_strong hx; exact hsk
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem truncSafeStrong_kemPk_iff {T : ExecTrace} (sk : DY.Bytes) :
    TruncSafeStrong T (PQKem.kemPk sk) ↔ TruncSafeStrong T sk := by
  refine ⟨fun hs => ?_, .kemPk⟩; generalize hx : PQKem.kemPk sk = y at hs
  have hview : DY.Bytes.view? y DY.PQKem.Pk.SubF = some { sk := sk } := by rw [← hx]; exact DY.BytesView.view_pack _
  cases hs
  case atom _ _ _ _ _ _ _ _ _ hk => rw [hk] at hview; contradiction
  case kemPk hsk => obtain rfl := kemPk_inj_strong hx; exact hsk
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

theorem truncSafeStrong_x25519Key {T : ExecTrace} {pk : DY.Bytes} (h : TruncSafeStrong T pk) :
    TruncSafeStrong T (X25519.normalizeX25519Key pk) := by
  unfold X25519.normalizeX25519Key; have hpack := DY.Bytes.pack_view? X25519.Variant.SubF pk
  rcases hv : pk.view? X25519.Variant.SubF with _ | x; · exact h
  rw [hv] at hpack; dsimp only at hpack; rw [← hpack] at h; exact (truncSafeStrong_variant_iff x).mp h

theorem truncSafeStrong_x25519TorsionVariant {T : ExecTrace} {key : DY.Bytes} (v : Fin 4) (t : Fin 8 := 0)
    (h : TruncSafeStrong T key) : TruncSafeStrong T (X25519.x25519TorsionVariant key v t) := by
  dsimp only [X25519.x25519TorsionVariant]
  split
  · exact truncSafeStrong_x25519Key h
  · exact TruncSafeStrong.variant { key := X25519.normalizeX25519Key key, variation := v, torsion := t } (truncSafeStrong_x25519Key h)

end UnsealedStrongHelpers

/-! ## Monotonicity and closure under attacker knowledge -/

theorem TruncInputValidTRStrong.mono {T T' : ExecTrace} (hle : T ≤ T') {inp : DY.Bytes}
    (h : TruncInputValidTRStrong T inp) : TruncInputValidTRStrong T' inp := by
  rcases h with hinp | ⟨pqSalt, seed, myIk, peerIk, a, ns, pn, m, pqMsg, t_s, stH, me, st_s,
    hinp_eq, hpq_ak, hmsg_ak, ha_eq, hst, hmyIk, hpeerIk, hseed⟩
  · exact .inl (DY.Bytes.AttackerKnows_le inp T T' hle hinp)
  · exact .inr ⟨pqSalt, seed, myIk, peerIk, a, ns, pn, m, pqMsg, t_s, stH, me, st_s,
      hinp_eq,
      DY.Bytes.AttackerKnows_le pqSalt T T' hle hpq_ak,
      DY.Bytes.AttackerKnows_le _ T T' hle hmsg_ak,
      ha_eq,
      CompTrace.at?_le_some hle hst,
      hmyIk, hpeerIk, hseed⟩

theorem TruncSafeStrong.mono {T T' : ExecTrace} (hle : T ≤ T') {b : DY.Bytes}
    (h : TruncSafeStrong T b) : TruncSafeStrong T' b := by
  induction h with
  | atom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact .atom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | concat _ _ ih1 ih2 => exact .concat ih1 ih2
  | symEnc _ ih => exact .symEnc ih
  | trunc8 h => exact .trunc8 (h.mono hle)
  | trWireMsg x _ _ _ ih1 ih2 ih3 => exact .trWireMsg x ih1 ih2 ih3
  | variant x _ ih => exact .variant x ih
  | spqrInit x _ _ ih1 ih2 => exact .spqrInit x ih1 ih2
  | spqrSendState x _ _ ih1 ih2 => exact .spqrSendState x ih1 ih2
  | spqrRecvState x _ _ ih1 ih2 => exact .spqrRecvState x ih1 ih2
  | dhPk _ ih => exact .dhPk ih
  | kemPk _ ih => exact .kemPk ih

def AGTRStrong (T : ExecTrace) (b : DY.Bytes) : Prop := b.AttackerKnows T ∧ TruncSafeStrong T b

set_option maxHeartbeats 400000 in
theorem agtrStrong_closed_under_attackerKnowledge (T : ExecTrace) :
    SubAttackerKnowledge.Implies AttackerKnowledge.attackerKnowledge (AGTRStrong T) := by
  change SubAttackerKnowledge.Implies DY.Libsignal.Composed.attackerKnowledge (AGTRStrong T)
  dsimp [DY.Libsignal.Composed.attackerKnowledge]
  apply SubAttackerKnowledge.combine.implies
  rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, _⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Random.attackerKnowledge]
    intro b hb; rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at hb; exact hb.elim
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Literal.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | n, _⟩ <;> [skip; omega]
    intro b hb; dsimp [Literal.attackerKnowledge.internal] at hb
    rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at hb
    rcases hb with ⟨bs, rfl⟩; exact ⟨Literal.attacker_knows_literalToBytes bs T, truncSafeStrong_literal T bs⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Concat.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | n, _⟩ <;> try omega
    · intro b hb; dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at hb
      rcases hb with ⟨lhs, rhs, rfl, ⟨hl_ak, hl_s⟩, ⟨hr_ak, hr_s⟩⟩
      exact ⟨Concat.attacker_knows_concat lhs rhs T hl_ak hr_ak, .concat hl_s hr_s⟩
    · intro b hb; dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, rhs, i, hsplit, ⟨hinp_ak, hinp_s⟩⟩
      have heq := Concat.concat_split inp i b rhs hsplit.symm
      exact ⟨DY.Bytes.AttackerKnows.prove Concat.splitLeft.attackerKnowledge b T
        (by rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred]; exact ⟨inp, rhs, i, hsplit, hinp_ak⟩),
        ((truncSafeStrong_concat_iff b rhs).mp (heq ▸ hinp_s)).1⟩
    · intro b hb; dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, lhs, i, hsplit, ⟨hinp_ak, hinp_s⟩⟩
      have heq := Concat.concat_split inp i lhs b hsplit.symm
      exact ⟨DY.Bytes.AttackerKnows.prove Concat.splitRight.attackerKnowledge b T
        (by rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred]; exact ⟨inp, lhs, i, hsplit, hinp_ak⟩),
        ((truncSafeStrong_concat_iff lhs b).mp (heq ▸ hinp_s)).2⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DiffieHellman.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
    · intro b hb; dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, ⟨hsk_ak, hsk_s⟩⟩
      exact ⟨DiffieHellman.attacker_knows_dhPk sk T hsk_ak, .dhPk hsk_s⟩
    · intro b hb; dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hb
      rcases hb with ⟨pk, sk, rfl, ⟨hpk_ak, _⟩, ⟨hsk_ak, _⟩⟩
      exact ⟨DiffieHellman.attacker_knows_dh pk sk T hpk_ak hsk_ak, truncSafeStrong_dh T pk sk⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, KdfExtract.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | n, _⟩ <;> [skip; omega]
    intro b hb; dsimp [KdfExtract.attackerKnowledge.internal] at hb
    rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hb
    rcases hb with ⟨salt, ikm, rfl, ⟨hs_ak, _⟩, ⟨hi_ak, _⟩⟩
    exact ⟨KdfExtract.attacker_knows_kdfExtract salt ikm T hs_ak hi_ak, truncSafeStrong_kdfExtract T salt ikm⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, SymEnc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
    · rintro b ⟨k, iv, msg, rfl, ⟨hk_ak, _⟩, ⟨hiv_ak, _⟩, ⟨hm_ak, hm_s⟩⟩
      exact ⟨SymEnc.attacker_knows_symEnc k iv msg T hk_ak hiv_ak hm_ak, .symEnc hm_s⟩
    · rintro b ⟨key, iv, ct, hdec, ⟨hk_ak, _⟩, ⟨hiv_ak, _⟩, ⟨hct_ak, hct_s⟩⟩
      have heq := SymEnc.symDec_eq_some key iv ct b hdec.symm; rw [heq] at hct_s
      exact ⟨SymEnc.attacker_knows_symDec key iv ct b T hk_ak hiv_ak hct_ak hdec.symm,
        (truncSafeStrong_symEnc_iff key iv b).mp hct_s⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Trunc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | n, _⟩ <;> [skip; omega]
    rintro b ⟨m, rfl, ⟨hm_ak, _⟩⟩
    exact ⟨Trunc.attacker_knows_trunc8 m T hm_ak, .trunc8 (.inl hm_ak)⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, X25519.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
    · rintro b ⟨key, v, t, rfl, ⟨hk_ak, hk_s⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove X25519.x25519Variant.attackerKnowledge _ T ⟨key, v, t, rfl, hk_ak⟩,
        truncSafeStrong_x25519TorsionVariant v t hk_s⟩
    · rintro b ⟨v, ⟨hv_ak, hv_s⟩, rfl⟩
      exact ⟨DY.Bytes.AttackerKnows.prove X25519.normalizeX25519Key.attackerKnowledge _ T ⟨v, hv_ak, rfl⟩,
        (truncSafeStrong_variant_iff v).mp hv_s⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, PQKem.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | _ | _ | n, _⟩ <;> try omega
    · rintro b ⟨sk, rfl, ⟨hsk_ak, hsk_s⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove PQKem.kemPk.attackerKnowledge _ T ⟨sk, rfl, hsk_ak⟩, .kemPk hsk_s⟩
    · rintro b ⟨pk, e, rhs, heq, ⟨hpk_ak, _⟩, ⟨he_ak, _⟩⟩
      have h1 : b = (PQKem.kemEncap pk e).1 := congrArg Prod.fst heq
      refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemEncapCipher.attackerKnowledge b T ⟨pk, e, rhs, heq, hpk_ak, he_ak⟩, ?_⟩
      rw [h1]; exact truncSafeStrong_kemEncap_fst T pk e
    · rintro b ⟨pk, e, lhs, heq, ⟨hpk_ak, _⟩, ⟨he_ak, _⟩⟩
      have h2 : b = (PQKem.kemEncap pk e).2 := congrArg Prod.snd heq
      refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemEncapSS.attackerKnowledge b T ⟨pk, e, lhs, heq, hpk_ak, he_ak⟩, ?_⟩
      rw [h2]; exact truncSafeStrong_kemEncap_snd T pk e
    · rintro b ⟨sk, ct, hdec, ⟨hsk_ak, _⟩, ⟨hct_ak, _⟩⟩
      refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemDecap.attackerKnowledge b T ⟨sk, ct, hdec, hsk_ak, hct_ak⟩, ?_⟩
      obtain ⟨e, _, rfl⟩ := kemDecap_eq_some_iff.mp hdec.symm
      exact truncSafeStrong_kemEncap_snd T (PQKem.kemPk sk) e
    · rintro b ⟨sk, ct, rfl, ⟨hsk_ak, _⟩, ⟨hct_ak, _⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove PQKem.kemRejKey.attackerKnowledge _ T ⟨sk, ct, rfl, hsk_ak, hct_ak⟩,
        truncSafeStrong_kemRejKey T sk ct⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Signature.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
    · intro b hb; dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, ⟨hsk_ak, _⟩⟩
      exact ⟨Signature.attacker_knows_vk sk T hsk_ak, truncSafeStrong_vk T sk⟩
    · intro b hb; dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, nonce, msg, rfl, ⟨hsk_ak, _⟩, ⟨hnonce_ak, _⟩, ⟨hmsg_ak, _⟩⟩
      exact ⟨Signature.attacker_knows_sign sk nonce msg T hsk_ak hnonce_ak hmsg_ak, truncSafeStrong_sign T sk nonce msg⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Spqr.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, _⟩ <;> try omega
    · rintro b ⟨authKey, params, rfl, ⟨hk_ak, hk_s⟩, ⟨hp_ak, hp_s⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrInit.attackerKnowledge _ T ⟨authKey, params, rfl, hk_ak, hp_ak⟩,
        .spqrInit { authKey := authKey, params := params } hk_s hp_s⟩
    · rintro b ⟨authKey, params, idx, rfl, ⟨hk_ak, _⟩, ⟨hp_ak, _⟩, ⟨hi_ak, _⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrChainKey.attackerKnowledge _ T ⟨authKey, params, idx, rfl, hk_ak, hp_ak, hi_ak⟩,
        truncSafeStrong_spqrChainKey T authKey params idx⟩
    · rintro b ⟨st, coins, rfl, ⟨hst_ak, hst_s⟩, ⟨hc_ak, hc_s⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendState.attackerKnowledge _ T ⟨st, coins, rfl, hst_ak, hc_ak⟩,
        truncSafeStrong_spqrSend_state hst_s hc_s⟩
    · rintro b ⟨st, coins, rfl, ⟨hst_ak, _⟩, ⟨hc_ak, _⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendKey.attackerKnowledge _ T ⟨st, coins, rfl, hst_ak, hc_ak⟩,
        truncSafeStrong_spqrSend_key T st coins⟩
    · rintro b ⟨st, coins, rfl, ⟨hst_ak, _⟩, ⟨hc_ak, _⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendMsg.attackerKnowledge _ T ⟨st, coins, rfl, hst_ak, hc_ak⟩,
        truncSafeStrong_spqrSend_msg T st coins⟩
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, ⟨hst_ak, hst_s⟩, ⟨hm_ak, hm_s⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrRecvState.attackerKnowledge _ T ⟨st, msg, idx, r, hrecv, rfl, hst_ak, hm_ak⟩,
        truncSafeStrong_spqrRecv_state hrecv hst_s hm_s⟩
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, ⟨hst_ak, _⟩, ⟨hm_ak, _⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrRecvKey.attackerKnowledge _ T ⟨st, msg, idx, r, hrecv, rfl, hst_ak, hm_ak⟩,
        truncSafeStrong_spqrRecv_key hrecv⟩
    · rintro b (⟨s, ⟨hs_ak, hs_s⟩, harg⟩ | ⟨s, ⟨hs_ak, hs_s⟩, harg⟩ | ⟨s, ⟨hs_ak, hs_s⟩, harg⟩)
      · have hargs := (truncSafeStrong_spqrInit_iff s).mp hs_s
        refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge b T (.inl ⟨s, hs_ak, harg⟩), ?_⟩
        rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
      · have hargs := (truncSafeStrong_spqrSendState_iff s).mp hs_s
        refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge b T (.inr (.inl ⟨s, hs_ak, harg⟩)), ?_⟩
        rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
      · have hargs := (truncSafeStrong_spqrRecvState_iff s).mp hs_s
        refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge b T (.inr (.inr ⟨s, hs_ak, harg⟩)), ?_⟩
        rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, TrWire.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
    · rintro b ⟨w, rfl, ⟨h1_ak, h1_s⟩, ⟨h2_ak, h2_s⟩, ⟨h3_ak, h3_s⟩⟩
      exact ⟨DY.Bytes.AttackerKnows.prove TrWire.trWireMsg.attackerKnowledge _ T
          ⟨w, rfl, h1_ak, h2_ak, h3_ak⟩,
        .trWireMsg w h1_s h2_s h3_s⟩
    · rintro b ⟨w, ⟨hw_ak, hw_s⟩, hmem⟩
      have hargs_s := (truncSafeStrong_trWireMsg_iff w).mp hw_s
      refine ⟨DY.Bytes.AttackerKnows.prove TrWire.trWireMsgArg.attackerKnowledge b T ⟨w, hw_ak, hmem⟩, ?_⟩
      rcases hmem with rfl | rfl | rfl
      exacts [hargs_s.1, hargs_s.2.1, hargs_s.2.2]
  · omega

theorem attackerKnows_imp_truncSafeStrong {T : ExecTrace}
    (hbase : ∀ b : DY.Bytes, T.BaseAttackerKnows b → TruncSafeStrong T b)
    {b : DY.Bytes} (hAK : b.AttackerKnows T) : TruncSafeStrong T b := by
  refine (DY.Bytes.AttackerKnows.is_least_fixpoint (AGTRStrong T) b T
    (agtrStrong_closed_under_attackerKnowledge T) (fun x hx => ?_) hAK).2
  simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hx
  exact ⟨DY.Bytes.AttackerKnows.prove_from_base x T hx, hbase x hx⟩

theorem truncSafeStrong_trHonestWireMsg {T : ExecTrace} {rk ct pqMsg : DY.Bytes} (ns pn : UInt32)
    (hrk : TruncSafeStrong T rk) (hct : TruncSafeStrong T ct) (hpq : TruncSafeStrong T pqMsg) :
    TruncSafeStrong T (trHonestWireMsg rk ns pn ct pqMsg) :=
  .trWireMsg
    { version := messageVersion, senderRatchetKey := rk, counter := ns,
      previousCounter := pn, ciphertext := ct, pqRatchet := pqMsg,
      encodingVariation := DY.TrWire.canonicalVariation }
    hrk hct hpq

theorem truncSafeStrong_chainKeyAt (T : ExecTrace) {ck0 : DY.Bytes} (h0 : TruncSafeStrong T ck0) :
    ∀ n : Nat, TruncSafeStrong T (chainKeyAt ck0 n)
  | 0 => h0
  | n + 1 => by
    rw [Symbolic.Swarm.COMPOSED.CompTermAlgebra.chainKeyAt_succ_eq_kdfCk_fst]
    exact truncSafeStrong_kdfExtract T _ _

/-! ## Trace invariant `TruncStrongInv` -/

structure TruncStrongInv (tr : ExecTrace) : Prop where
  baseSafe : ∀ b, tr.BaseAttackerKnows b → TruncSafeStrong tr b
  spqrSafe : ∀ me st idx, TRStoredAt tr me st idx → TruncSafeStrong tr st.spqr

theorem truncStrongInv_nil : TruncStrongInv Trace.nil :=
  { baseSafe := fun b h => False.elim (Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1 b ▸ h)
    spqrSafe := fun _ _ _ h => by
      unfold TRStoredAt at h; rw [Trace.at?_eq_some] at h
      exact False.elim (Symbolic.DYBridge.DY.Trace.nil_length_not_lt _ h.1) }

theorem TruncStrongInv.of_attackerKnows {tr : ExecTrace} (hc : TruncStrongInv tr) {b : DY.Bytes} (hk : b.AttackerKnows tr) :
    TruncSafeStrong tr b := attackerKnows_imp_truncSafeStrong hc.baseSafe hk

theorem TruncStrongInv.append_rnd {tr : ExecTrace} (hc : TruncStrongInv tr) (n : Nat) : TruncStrongInv (tr.append (RndE n)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_rnd tr n b).mp hb)).mono (Trace.append_le tr _),
   fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem TruncStrongInv.append_ev {tr : ExecTrace} (hc : TruncStrongInv tr) (ev : PQXDHEvent) : TruncStrongInv (tr.append (EvE ev)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_pqEv tr ev b).mp hb)).mono (Trace.append_le tr _),
   fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem TruncStrongInv.append_trEv {tr : ExecTrace} (hc : TruncStrongInv tr) (ev : TREvent) : TruncStrongInv (tr.append (TREvE ev)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_trEv tr ev b).mp hb)).mono (Trace.append_le tr _),
   fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem TruncStrongInv.append_cEv {tr : ExecTrace} (hc : TruncStrongInv tr) (ev : ComposedEvent) : TruncStrongInv (tr.append (CEvE ev)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_cEv tr ev b).mp hb)).mono (Trace.append_le tr _),
   fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem TruncStrongInv.append_st {tr : ExecTrace} (hc : TruncStrongInv tr) (me : Participant) (st : PQXDHState) :
    TruncStrongInv (tr.append (StE me st)) :=
  ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_pqSt tr me st b).mp hb)).mono (Trace.append_le tr _),
   fun me' st' idx hst => (hc.spqrSafe me' st' idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono (Trace.append_le tr _)⟩

theorem TruncStrongInv.append_net {tr : ExecTrace} (hc : TruncStrongInv tr) {msg : DY.Bytes}
    (hmsg : TruncSafeStrong (tr.append (NetE msg)) msg) : TruncStrongInv (tr.append (NetE msg)) := by
  have hle : tr ≤ tr.append (NetE msg) := Trace.append_le tr (NetE msg)
  refine ⟨fun b hb => ?_, fun me st idx hst => (hc.spqrSafe me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle⟩
  rcases (CompTrace.baseAttackerKnows_append_net tr msg b).mp hb with rfl | hb' <;> [exact hmsg; exact (hc.baseSafe b hb').mono hle]

theorem TruncStrongInv.append_net_of_safe {tr : ExecTrace} (hc : TruncStrongInv tr) {msg : DY.Bytes}
    (hmsg : TruncSafeStrong tr msg) : TruncStrongInv (tr.append (NetE msg)) :=
  hc.append_net (hmsg.mono (Trace.append_le tr (NetE msg)))

theorem TruncStrongInv.append_net_rnd {tr : ExecTrace} (hc : TruncStrongInv tr) (t n : Nat) :
    TruncStrongInv (tr.append (NetE (CompTrace.mkRand t n))) :=
  hc.append_net (truncSafeStrong_random _ { timestamp := t, size := n })

theorem TruncStrongInv.append_trSt {tr : ExecTrace} (hc : TruncStrongInv tr)
    {me : Participant} {st : TRState} (hspqr : TruncSafeStrong tr st.spqr) :
    TruncStrongInv (tr.append (TRStE me st)) := by
  have hle : tr ≤ tr.append (TRStE me st) := Trace.append_le tr (TRStE me st)
  refine ⟨fun b hb => (hc.baseSafe b ((CompTrace.baseAttackerKnows_append_trSt tr me st b).mp hb)).mono hle,
    fun me' st' idx hst => ?_⟩
  rcases CompInv.CompPresBob.trStoredAt_append_same hst with ⟨_, hst'⟩ | ⟨_, _, rfl⟩
  · exact (hc.spqrSafe me' st' idx hst').mono hle
  · exact hspqr.mono hle

theorem TruncStrongInv.logSkippedKeys_preserves (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32) (tr : ExecTrace),
      TruncStrongInv tr → TruncStrongInv ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k).run tr).2.val
  | 0, _, _, _, hc => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [Traceful.run_pure]; exact hc
  | k + 1, ck, n, tr, hc => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    exact TruncStrongInv.logSkippedKeys_preserves s pk rIdx src k (kdfCk ck).1 (n + 1) _ (hc.append_trEv _)

theorem TruncStrongInv.append_logMessageKeyAndStore {tr : ExecTrace} (hc : TruncStrongInv tr)
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : DY.Bytes)
    (n : UInt32) (rIdx prev : Nat) (st : TRState) (hspqr : TruncSafeStrong tr st.spqr) :
    TruncStrongInv ((DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx prev st).run tr).2.val := by
  rw [CompPresTRExp.run_logMessageKeyAndStore_snd]
  exact (hc.append_trEv _).append_trSt (hspqr.mono (Trace.append_le tr _))

theorem parseTrSignalMsg_pqRatchet_safeStrong {T : ExecTrace} {t : DY.Bytes} {msg : TRSignalMsg}
    (ht : TruncSafeStrong T t) (hparse : parseTrSignalMsg t = some msg) : TruncSafeStrong T msg.pqRatchet := by
  unfold parseTrSignalMsg at hparse
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at hparse
  rcases hparse with ⟨⟨wire, mac⟩, hsplit, x, hx, rfl⟩; dsimp only at hx ⊢
  rw [← Concat.concat_split t (t.length - Trunc.trunc8Length) wire mac hsplit] at ht
  have hwire : TruncSafeStrong T wire := ((truncSafeStrong_concat_iff wire mac).mp ht).1
  rw [TrWire.trWireMsg_of_fields? hx] at hwire; exact ((truncSafeStrong_trWireMsg_iff x).mp hwire).2.2

theorem macKdfStrong_receiveSignalMsg_at {tr : ExecTrace} (hc : TruncStrongInv tr) {α : Type}
    (msgIdx : Nat) {f : TRSignalMsg → Traceful α}
    (hf : ∀ msg, TruncSafeStrong tr msg.pqRatchet → TruncStrongInv ((f msg).run tr).2.val) :
    TruncStrongInv (((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at msgIdx tr hc fun raw _ hraw => ?_
  rcases hparse : parseTrSignalMsg raw with _ | msg
  · dsimp only; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hc
  dsimp only; rw [CompTrace.run_bind_assoc_snd]
  exact CompTrace.bind_guardP_at _ tr hc fun _ =>
    hf msg (parseTrSignalMsg_pqRatchet_safeStrong (hc.of_attackerKnows hraw) hparse)

theorem macKdfStrong_preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) (tr : ExecTrace) (hc : TruncStrongInv tr) :
    TruncStrongInv ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
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
      ns := 0, pn := 0, sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk,
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
  change TruncStrongInv (tr8.append (TRStE a stA))
  have hc3 : TruncStrongInv tr3 := ((hc.append_rnd 32).append_rnd 32).append_rnd 32
  have hc4 : TruncStrongInv tr4 := hc3.append_net_of_safe (.dhPk (truncSafeStrong_random _ _))
  have hc5 : TruncStrongInv tr5 := hc4.append_net_of_safe (truncSafeStrong_kemEncap_fst _ pqPk _)
  have hc8 : TruncStrongInv tr8 := ((hc5.append_ev _).append_trEv _).append_cEv _
  have hpqr : TruncSafeStrong tr8 hs.keys.pqr := by
    dsimp [hs, aliceOut, DY.Libsignal.PQXDH.aliceAgreement]; exact truncSafeStrong_kdfExtract tr8 _ _
  exact hc8.append_trSt (.spqrInit { authKey := hs.keys.pqr, params := spqrA2B } hpqr (truncSafeStrong_literal _ _))

theorem macKdfStrong_bobStart_commit {tr : ExecTrace} (hc : TruncStrongInv tr)
    (b a : Participant) (sB sS sQ : DY.Bytes) (o : Option DY.Bytes) (ikA ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (dhs spqr' seed pqSalt m : DY.Bytes) (c' : RecvChain) (hspqr : TruncSafeStrong tr spqr') :
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    TruncStrongInv (((do
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
  have hc₄ : TruncStrongInv tr₄ := (((hc.append_ev _).append_trEv _).append_trEv _).append_cEv _
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
  change TruncStrongInv (((skipAct >>= restAct).run tr₄).2.val)
  rw [CompInv.CompPresBob.run_logSkippedKeys_bind_snd]
  let tr₅ := (skipAct.run tr₄).2.val; have hle₄₅ : tr₄ ≤ tr₅ := (skipAct.run tr₄).2.property
  have hc₅ : TruncStrongInv tr₅ := TruncStrongInv.logSkippedKeys_preserves (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx skipped c.chainKey c.index tr₄ hc₄
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  have hc₆ : TruncStrongInv tr₆ := hc₅.append_trEv _
  have hle₀₆ : tr ≤ tr₆ := Trace.le_trans _ _ _ hle₀₄ (Trace.le_trans _ _ _ hle₄₅ (Trace.append_le tr₅ _))
  dsimp only [restAct]; rw [CompPresTRExp.run_logEvent_bind_snd]
  exact hc₆.append_logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
    msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' } (hspqr.mono hle₀₆)

theorem macKdfStrong_preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : TruncStrongInv tr) :
    TruncStrongInv ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hc
    fun sB sS sQ o ikA _ ek ct _ keys _ _ _ _ _ _ _ _ hbob => ?_
  refine macKdfStrong_receiveSignalMsg_at hc mh.msg fun msg hpq => ?_; dsimp only
  refine CompInv.CompPresBob.bind_ensureReceiverChain_bobInitSt
    a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey tr hc fun _ => ?_
  let dhs := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32
  let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
  let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
  let tr₁ := tr.append (RndE 32); have hc₁ : TruncStrongInv tr₁ := hc.append_rnd 32
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
  have hpqr₁ : TruncSafeStrong tr₁ keys.pqr := by rw [hkeys_eq]; exact truncSafeStrong_kdfExtract tr₁ _ _
  have hspqr₁ : TruncSafeStrong tr₁ spqr' :=
    truncSafeStrong_spqrRecv_state hSpqr (.spqrInit { authKey := keys.pqr, params := spqrB2A } hpqr₁ (truncSafeStrong_literal _ _)) (hpq.mono hle₀₁)
  let tr₂ := tr₁.append (NetE key); have hle₁₂ : tr₁ ≤ tr₂ := Trace.append_le tr₁ _
  have hc₂ : TruncStrongInv tr₂ := hc₁.append_net_of_safe (truncSafeStrong_spqrRecv_key hSpqr)
  have hspqr₂ : TruncSafeStrong tr₂ spqr' := hspqr₁.mono hle₁₂
  rw [CompPresTRExp.run_sendMessage_bind_snd]
  change TruncStrongInv (((Network.receiveMessage pqIdx >>= fun pqSalt =>
    DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed >>= fun m => _).run tr₂).2.val)
  refine CompTrace.bind_receiveMessage_at pqIdx tr₂ hc₂ fun pqSalt _ _ => ?_
  refine CompInv.CompPresBob.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr₂ hc₂ fun m _ => ?_
  cases o with
  | none =>
    dsimp only [Option.map]
    exact macKdfStrong_bobStart_commit hc₂ b a sB sS sQ none ikA ek ct keys msg dhs spqr' seed pqSalt m c' hspqr₂
  | some oSk =>
    dsimp only [Option.map]; rw [CompTrace.run_bind_snd]
    unfold DY.Libsignal.PQXDH.guardTrace; rw [Traceful.run_mk]; dsimp only
    by_cases hused : (!opkUsedB tr₂ b (DiffieHellman.dhPk oSk)) = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hused h]; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd]
      exact macKdfStrong_bobStart_commit (hc₂.append_ev _) b a sB sS sQ (some oSk) ikA ek ct keys msg dhs spqr' seed pqSalt m c'
        (hspqr₂.mono (Trace.append_le tr₂ _))
    · rw [ite_eq_right_iff.mpr fun h => absurd h hused]; dsimp only; exact hc₂

theorem macKdfStrong_preserves_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : TruncStrongInv tr) :
    TruncStrongInv ((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  obtain ⟨_, _, _, _, _, hdhs, _, _, _, _⟩ := hinv.trStOK me st stateIdx hst
  have hdhs_rand : ∃ t_s : Nat, st.dhs = randTerm t_s 32 := by
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩
    · exact ⟨t + 2, hdhs_eq⟩
    · exact ⟨t, hdhs_eq⟩
  obtain ⟨t_s, hdhs_eq⟩ := hdhs_rand
  have hspqr0 : TruncSafeStrong tr st.spqr := hc.spqrSafe me st stateIdx hst
  apply CompTrace.bind_guardP_at _ tr hc; intro _
  rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_sendMessage_bind_snd]
  let m := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32; let tr1 := tr.append (RndE 32)
  let coins := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr1.length coinsLen; let tr2 := tr1.append (RndE coinsLen)
  let key := (Spqr.spqrSend st.spqr coins).2.1; let tr3 := tr2.append (NetE key)
  have hc3 : TruncStrongInv tr3 := ((hc.append_rnd 32).append_rnd coinsLen).append_net_of_safe (truncSafeStrong_spqrSend_key tr2 st.spqr coins)
  have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 (Trace.append_le tr _) (Trace.append_le tr1 _)) (Trace.append_le tr2 _)
  apply CompTrace.bind_receiveMessage_at pqIdx tr3 hc3; intro pqSalt _ hpq_ak3
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    CompPresTRExp.run_logMessageKeyAndStore_bind_snd, CompPresTRExp.run_sendMessage_snd]
  let tr4 := tr3.append (TREvE (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m))
  have hc4 : TruncStrongInv tr4 := hc3.append_trEv _
  have hle04 : tr ≤ tr4 := Trace.le_trans tr tr3 tr4 hle03 (Trace.append_le tr3 _)
  let st' : TRState := { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 }
  have hspqr'_safe4 : TruncSafeStrong tr4 st'.spqr := truncSafeStrong_spqrSend_state (hspqr0.mono hle04) (truncSafeStrong_random tr4 _)
  have hc6 : TruncStrongInv ((DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) .sender (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st').run tr4).2.val :=
    hc4.append_logMessageKeyAndStore me (st.sessionInfo me) .sender
      (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st' hspqr'_safe4
  rw [CompPresTRExp.run_logMessageKeyAndStore_snd] at hc6
  let tr5 := tr4.append (TREvE (TREvent.MessageKey (st.sessionInfo me) .sender
    (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx))
  let tr6 := tr5.append (TRStE me st')
  let mk := trMsgKeys pqSalt (kdfCk st.cks).2
  let wire := DY.Libsignal.TripleRatchet.trHonestWireMsg (DiffieHellman.dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc mk.cipherKey mk.iv m) (Spqr.spqrSend st.spqr coins).2.2
  let mac := computeMac mk.macKey st.myIk st.peerIk wire
  let tr7 := tr6.append (NetE (Concat.concat wire mac))
  have hle36 : tr3 ≤ tr6 := Trace.le_trans tr3 tr4 tr6 (Trace.append_le tr3 _)
    (Trace.le_trans tr4 tr5 tr6 (Trace.append_le tr4 _) (Trace.append_le tr5 _))
  have hle37 : tr3 ≤ tr7 := Trace.le_trans tr3 tr6 tr7 hle36 (Trace.append_le tr6 _)
  have hle07 : tr ≤ tr7 := Trace.le_trans tr tr3 tr7 hle03 hle37
  have hdhs_safe7 : TruncSafeStrong tr7 st.dhs := by
    rw [hdhs_eq]; exact truncSafeStrong_random tr7 _
  have hwire_safe7 : TruncSafeStrong tr7 wire :=
    truncSafeStrong_trHonestWireMsg st.ns st.pn (.dhPk hdhs_safe7)
      (.symEnc (truncSafeStrong_random tr7 _)) (truncSafeStrong_spqrSend_msg tr7 st.spqr coins)
  have hmsg_ak7 : (Concat.concat wire mac).AttackerKnows tr7 :=
    DY.Bytes.AttackerKnows.prove_from_base (Concat.concat wire mac) tr7
      ((CompTrace.baseAttackerKnows_append_net tr6 (Concat.concat wire mac) (Concat.concat wire mac)).mpr (.inl rfl))
  exact hc6.append_net (.concat hwire_safe7 (.trunc8 (.inr ⟨pqSalt, (kdfCk st.cks).2,
    st.myIk, st.peerIk, st.dhs, st.ns, st.pn, m, (Spqr.spqrSend st.spqr coins).2.2,
    t_s, stateIdx, me, st, rfl, DY.Bytes.AttackerKnows_le pqSalt tr3 tr7 hle37 hpq_ak3,
    hmsg_ak7, hdhs_eq, CompTrace.at?_le_some hle07 hst, rfl, rfl, rfl⟩)))

theorem macKdfStrong_preserves_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : TruncStrongInv tr) :
    TruncStrongInv ((DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  have hspqr0 : TruncSafeStrong tr st.spqr := hc.spqrSafe me st stateIdx hst
  apply macKdfStrong_receiveSignalMsg_at hc msgIdx; intro msg hpq_safe
  apply CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc; intro ⟨ev⟩ _
  cases ev with
  | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
    dsimp only; apply CompTrace.bind_guardP_at _ tr hc; intro _
    apply CompPresTRExp.bind_guardTrace_at _ tr hc; intro _
    rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
    let tr1 := tr.append (NetE key); have hc1 : TruncStrongInv tr1 := hc.append_net_of_safe (truncSafeStrong_spqrRecv_key hspqr_recv)
    have hle01 : tr ≤ tr1 := Trace.append_le tr _
    apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1; intro pqSalt _ _
    apply CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1; intro m
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    let tr2 := tr1.append (TREvE (TREvent.SkippedKeyUsed s skippedKeyEventIdx))
    let tr3 := tr2.append (TREvE (TREvent.Received me st.peer pk n m))
    have hc3 : TruncStrongInv tr3 := (hc1.append_trEv _).append_trEv _
    have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 hle01 (Trace.append_le tr1 _)) (Trace.append_le tr2 _)
    exact hc3.append_logMessageKeyAndStore me s .receiver seed pqSalt n rIdx stateIdx { st with spqr := spqr' } ((truncSafeStrong_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle03)
  | _ => dsimp only; rw [Traceful.run_failure]; exact hc

theorem macKdfStrong_preserves_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : TruncStrongInv tr) :
    TruncStrongInv ((DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  have hspqr0 : TruncSafeStrong tr st.spqr := hc.spqrSafe me st stateIdx hst
  apply macKdfStrong_receiveSignalMsg_at hc msgIdx; intro msg hpq_safe
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor
  rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c
  · dsimp only; rcases hlow : x25519LowOrder msg.ratchetKey with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte, DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_bind_assoc_snd]
      apply CompTrace.bind_guardP_at _ tr hc; intro _
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_genRand_bind_snd, CompTrace.run_pure_bind_snd, CompTrace.run_pure_bind_snd]
      let tr1 := tr.append (RndE 32); have hc1 : TruncStrongInv tr1 := hc.append_rnd 32
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
      let tr2 := tr1.append (NetE key); have hc2 : TruncStrongInv tr2 := hc1.append_net_of_safe (truncSafeStrong_spqrRecv_key hspqr_recv)
      have hle02 : tr ≤ tr2 := Trace.le_trans tr tr1 tr2 hle01 (Trace.append_le tr1 _)
      apply CompTrace.bind_receiveMessage_at pqIdx tr2 hc2; intro pqSalt _ _
      apply CompPresTRExp.bind_verifyMacAndDecrypt_at st1 msg pqSalt seed tr2 hc2; intro m
      simp only [↓reduceIte]; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
        CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompTrace.run_bind_snd]
      let tr3 := tr2.append (TREvE (TREvent.DHRatchet me st1.peer msg.ratchetKey (DiffieHellman.dhPk st1.dhs)))
      let tr4 := tr3.append (TREvE (TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2)))
      have hc4 : TruncStrongInv tr4 := (hc2.append_trEv _).append_trEv _
      have hle04 : tr ≤ tr4 := Trace.le_trans tr tr2 tr4 hle02 (Trace.le_trans tr2 tr3 tr4 (Trace.append_le tr2 _) (Trace.append_le tr3 _))
      have hc5 := TruncStrongInv.logSkippedKeys_preserves (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
        (msg.counter.toNat - c_new.index.toNat) c_new.chainKey c_new.index tr4 hc4
      have hle45 := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
        c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4).2.property
      rcases hsk_res : (DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
          c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4 with ⟨_ | u, tr5_sub⟩
      · rw [hsk_res] at hc5; exact hc5
      · rw [hsk_res] at hc5 hle45; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
        let tr6 := tr5_sub.val.append (TREvE (TREvent.Received me st1.peer msg.ratchetKey msg.counter m))
        have hc6 : TruncStrongInv tr6 := hc5.append_trEv _
        have hle06 : tr ≤ tr6 := Trace.le_trans tr tr4 tr6 hle04 (Trace.le_trans tr4 tr5_sub.val tr6 hle45 (Trace.append_le tr5_sub.val _))
        exact hc6.append_logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt msg.counter
          c_new.rIdx stateIdx { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
          ((truncSafeStrong_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle06)
    · simp only [↓reduceIte]; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hc
  · dsimp only; rw [CompTrace.run_pure_bind_snd]
    rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
    let tr1 := tr.append (NetE key); have hc1 : TruncStrongInv tr1 := hc.append_net_of_safe (truncSafeStrong_spqrRecv_key hspqr_recv)
    have hle01 : tr ≤ tr1 := Trace.append_le tr _
    apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1; intro pqSalt _ _
    apply CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1; intro m
    simp only [Bool.false_eq_true, ↓reduceIte]; rw [CompTrace.run_bind_snd]
    have hc2 := TruncStrongInv.logSkippedKeys_preserves (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
      (msg.counter.toNat - c.index.toNat) c.chainKey c.index tr1 hc1
    have hle12 := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
      c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1).2.property
    rcases hsk_res : (DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
        c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1 with ⟨_ | u, tr2_sub⟩
    · rw [hsk_res] at hc2; exact hc2
    · rw [hsk_res] at hc2 hle12; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
      let tr3 := tr2_sub.val.append (TREvE (TREvent.Received me st.peer msg.ratchetKey msg.counter m))
      have hc3 : TruncStrongInv tr3 := hc2.append_trEv _
      have hle03 : tr ≤ tr3 := Trace.le_trans tr tr1 tr3 hle01 (Trace.le_trans tr1 tr2_sub.val tr3 hle12 (Trace.append_le tr2_sub.val _))
      exact hc3.append_logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter
        c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }
        ((truncSafeStrong_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle03)

theorem macKdfStrong_preserves_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : TruncStrongInv tr) :
    TruncStrongInv ((DY.Libsignal.TripleRatchet.exposeKey me stateIdx k).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  obtain ⟨_, keys, _, hkeys, _, hdhs, _, hrk, hcks, hrecv⟩ := hinv.trStOK me st stateIdx hst
  cases k with
  | rk =>
    dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    obtain ⟨r, p, s, hrk_eq⟩ := hrk
    exact (hc.append_trEv _).append_net_of_safe (by rw [hrk_eq]; exact truncSafeStrong_kdfExtract _ _ _)
  | dhs =>
    dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedDHs (st.sessionInfo me) st.dhs st.rIdx)
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩
    · rw [hdhs_eq] at hc1 ⊢; exact hc1.append_net_rnd (t + 2) 32
    · rw [hdhs_eq] at hc1 ⊢; exact hc1.append_net_rnd t 32
  | cks =>
    dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    obtain ⟨rkChain, pk, sk, n, _, hcks_eq⟩ := hcks
    exact (hc.append_trEv _).append_net_of_safe (by
      rw [hcks_eq]; exact truncSafeStrong_chainKeyAt _ (truncSafeStrong_kdfExtract _ _ _) n)
  | ckr pk =>
    dsimp only; rcases hfind : findRecvChain st.recv pk with _ | c; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; have hc_mem : c ∈ st.recv := CompPresTRExp.findRecvChain_mem hfind
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    let tr1 := tr.append (TREvE (TREvent.ExposedCKr (st.sessionInfo me) c.chainKey c.index c.rIdx))
    have hc1 : TruncStrongInv tr1 := hc.append_trEv _
    refine hc1.append_net_of_safe ?_
    obtain ⟨ikm, hikm⟩ := CompInv.CompPubInv.handshakeKeysAt_eq_pqxdhKdf hinv hkeys
    rcases hrecv c hc_mem with ⟨_, _, hck⟩ | ⟨n, _, _, hck⟩ | ⟨rkChain, pk', sk', n, _, hck⟩
    · rw [hck, hikm]; exact truncSafeStrong_kdfExtract tr1 _ _
    · rw [hck, hikm]; exact truncSafeStrong_chainKeyAt tr1 (truncSafeStrong_kdfExtract tr1 _ _) (n + 1)
    · rw [hck]; exact truncSafeStrong_chainKeyAt tr1 (truncSafeStrong_kdfExtract tr1 _ _) n

theorem macKdfStrong_preserves_exposeSkipped (skippedKeyEventIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : TruncStrongInv tr) :
    TruncStrongInv ((DY.Libsignal.TripleRatchet.exposeSkipped skippedKeyEventIdx).run tr).2.val := by
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
    have hc1 : TruncStrongInv tr1 := hc.append_trEv _
    have hseed_shape : ∃ c, seed = (kdfCk c).2 := by rcases hseed with ⟨m, rfl⟩ | ⟨_, _, _, m, _, rfl⟩ <;> exact ⟨_, rfl⟩
    obtain ⟨c, rfl⟩ := hseed_shape
    exact hc1.append_net_of_safe (truncSafeStrong_kdfExtract tr1 _ _)
  | _ => dsimp only; rw [Traceful.run_failure]; exact hc

theorem truncStrongInv_of_reachable {tr : ExecTrace} (hr : ReachableTraceStrong tr) : TruncStrongInv tr := by
  induction hr with
  | Base => exact truncStrongInv_nil
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
    · change DY.Bytes at inp; change TruncStrongInv ((Network.sendMessage inp).run _).2.val; rw [CompPresTRExp.run_sendMessage_snd]
      exact hc.append_net_of_safe (hc.of_attackerKnows hPre)
    · change Participant at inp; change TruncStrongInv ((registerIdentity inp).run _).2.val; unfold registerIdentity
      refine bind_guardOnTrace_at _ _ hc fun _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, hst_snd]
      exact ((((hc.append_rnd 32).append_ev _).append_net_of_safe
        (.dhPk (truncSafeStrong_random _ _))).append_net_of_safe (truncSafeStrong_vk _ _)).append_st inp _
    · rcases inp with ⟨p, skIdx⟩; change TruncStrongInv ((registerCorruptIdentity p skIdx).run _).2.val; unfold registerCorruptIdentity
      refine bind_guardOnTrace_at _ _ hc fun _ => bind_receiveMessage_at skIdx _ hc fun _ _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, hlog_snd]; exact (hc.append_ev _).append_ev _
    · rcases inp with ⟨b, idStateIdx⟩; change TruncStrongInv ((genSignedPrekey b idStateIdx).run _).2.val; unfold genSignedPrekey
      refine bind_getKey_at b idStateIdx .identity _ hc fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact (((((hc.append_rnd 32).append_rnd 64).append_ev _).append_st b _).append_net_of_safe
        (.dhPk (truncSafeStrong_random _ _))).append_net_of_safe (truncSafeStrong_sign _ _ _ _)
    · rcases inp with ⟨b, idStateIdx⟩; change TruncStrongInv ((genPQPrekey b idStateIdx).run _).2.val; unfold genPQPrekey
      refine bind_getKey_at b idStateIdx .identity _ hc fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact (((((hc.append_rnd 64).append_rnd 64).append_ev _).append_st b _).append_net_of_safe
        (.kemPk (truncSafeStrong_random _ _))).append_net_of_safe (truncSafeStrong_sign _ _ _ _)
    · change Participant at inp; change TruncStrongInv ((genOneTimePrekey inp).run _).2.val; unfold genOneTimePrekey
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd, hst_bind,
        CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact (((hc.append_rnd 32).append_ev _).append_st inp _).append_net_of_safe (.dhPk (truncSafeStrong_random _ _))
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩; exact macKdfStrong_preserves_aliceStart a b idStateIdx regIdxB bh _ hc
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩; exact macKdfStrong_preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩; exact macKdfStrong_preserves_messageEncrypt me stateIdx coinsLen pqIdx _ hinv hc
    · rcases inp with ⟨me, stateIdx⟩; change TruncStrongInv ((DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx).run _).2.val
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
      refine CompTrace.bind_getLocalState_tr_at me stateIdx _ hc fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, Traceful.run_failure]; exact hc.append_rnd 32
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩; exact macKdfStrong_preserves_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩; exact macKdfStrong_preserves_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, k⟩; exact macKdfStrong_preserves_exposeKey me stateIdx k _ hinv hc
    · rcases inp with ⟨me, stateIdx⟩; change TruncStrongInv ((DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx).run _).2.val
      unfold DY.Libsignal.TripleRatchet.exposeSpqr
      apply CompTrace.bind_getLocalState_tr_at me stateIdx _ hc; intro st hst
      rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
      exact (hc.append_trEv _).append_net_of_safe ((hc.spqrSafe me st stateIdx hst).mono (Trace.append_le _ _))
    · exact macKdfStrong_preserves_exposeSkipped inp _ hinv hc
    · rcases inp with ⟨p, stateIdx⟩; change TruncStrongInv ((compromiseIK p stateIdx).run _).2.val; unfold compromiseIK
      refine bind_getKey_at p stateIdx .identity _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _⟩ := hinv.stOK p { kind := .identity, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]; exact (hc.append_ev _).append_net_rnd t 32
    · rcases inp with ⟨b, stateIdx⟩; change TruncStrongInv ((compromiseSPK b stateIdx).run _).2.val; unfold compromiseSPK
      refine bind_getKey_at b stateIdx .signedPrekey _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .signedPrekey, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]; exact (hc.append_ev _).append_net_rnd t 32
    · rcases inp with ⟨b, stateIdx⟩; change TruncStrongInv ((compromisePQSPK b stateIdx).run _).2.val; unfold compromisePQSPK
      refine bind_getKey_at b stateIdx .pqPrekey _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .pqPrekey, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]; exact (hc.append_ev _).append_net_rnd t 64
    · rcases inp with ⟨b, stateIdx⟩; change TruncStrongInv ((compromiseOPK b stateIdx).run _).2.val; unfold compromiseOPK
      refine bind_getKey_at b stateIdx .oneTimePrekey _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _⟩ := hinv.stOK b { kind := .oneTimePrekey, sk := sk } stateIdx hst
      refine CompPresPQXDH.Preserves.bind_guardOnTrace _ (fun _ hc _ => ?_) _ hc
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]; exact (hc.append_ev _).append_net_rnd t 32
    · change TruncStrongInv ((DY.Libsignal.PQXDH.breakDH).run _).2.val; unfold DY.Libsignal.PQXDH.breakDH
      rw [hlog_snd]; exact hc.append_ev _
    · change TruncStrongInv ((DY.Libsignal.PQXDH.breakKEM).run _).2.val; unfold DY.Libsignal.PQXDH.breakKEM
      rw [hlog_snd]; exact hc.append_ev _
    · change Nat at inp; change TruncStrongInv ((invertDH inp).run _).2.val; unfold invertDH
      refine CompPresPQXDH.Preserves.bind_guardOnTrace DY.Libsignal.PQXDH.brokenDHB (fun tr hc _ => ?_) _ hc
      refine bind_receiveMessage_at inp tr hc fun pk _ hpk => ?_
      have hpk_safe : TruncSafeStrong tr (X25519.normalizeX25519Key pk) := truncSafeStrong_x25519Key (hc.of_attackerKnows hpk)
      rcases hdh : DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
      · dsimp only; rw [Traceful.run_failure]; exact hc
      dsimp only; rw [CompPresTRExp.run_sendMessage_snd]; rw [dhSkOf_eq_some hdh] at hpk_safe
      exact hc.append_net_of_safe ((truncSafeStrong_dhPk_iff sk).mp hpk_safe)
    · change Nat at inp; change TruncStrongInv ((invertKEM inp).run _).2.val; unfold invertKEM
      refine CompPresPQXDH.Preserves.bind_guardOnTrace DY.Libsignal.PQXDH.brokenKEMB (fun tr hc _ => ?_) _ hc
      refine bind_receiveMessage_at inp tr hc fun pk _ hpk => ?_
      have hpk_safe : TruncSafeStrong tr pk := hc.of_attackerKnows hpk
      rcases hkem : PQKem.invertKemPublicKey pk with _ | sk
      · dsimp only [liftM, monadLift, MonadLift.monadLift]; rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; exact hc
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [CompPresTRExp.run_sendMessage_snd]
      rw [kemPkInvert_eq_some hkem] at hpk_safe; exact hc.append_net_of_safe ((truncSafeStrong_kemPk_iff sk).mp hpk_safe)
    · omega

theorem truncSafeStrong_of_attackerKnows_reachable {T : ExecTrace} (hT : ReachableTraceStrong T)
    {b : DY.Bytes} (hAK : b.AttackerKnows T) : TruncSafeStrong T b :=
  (truncStrongInv_of_reachable hT).of_attackerKnows hAK

theorem truncInputValidTRStrong_of_attackerKnows_reachable {T : ExecTrace} (hT : ReachableTraceStrong T)
    {inp : DY.Bytes} (h : (Trunc.trunc8 inp).AttackerKnows T) : TruncInputValidTRStrong T inp :=
  (truncSafeStrong_trunc8_iff inp).mp (truncSafeStrong_of_attackerKnows_reachable hT h)

/-! ## Stored states vs. `availableStates` -/

private def NoTRStored (tr : ExecTrace) : Prop :=
  ∀ p st i, ¬ TRStateStoredAt p st i tr

private theorem noTRStored_nil : NoTRStored Trace.nil := fun _ _ _ h => by
  unfold TRStateStoredAt at h; rw [Trace.at?_eq_some] at h
  exact Symbolic.DYBridge.DY.Trace.nil_length_not_lt _ h.1

private theorem noTRStored_append_nonTRSt {T : Type} [ExecTraceTypes.Has T] {x : T}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) : Option TTRStEntry) = none)
    {tr : ExecTrace} (htr : NoTRStored tr) : NoTRStored (tr.append x) := by
  intro p st i h
  exact htr p st i (CompInv.CompPresBob.trStoredAt_append_other hnone h)

private theorem noTRStored_getKey (p : Participant) (stateIdx : Nat) (kind : KeyKind) :
    CompTrace.Preserves NoTRStored (getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p stateIdx) fun _ =>
    CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _

private theorem noTRStored_registerIdentity (p : Participant) :
    CompTrace.Preserves NoTRStored (registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ tr h => ?_
  rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
    CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl
    (noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl h))))

private theorem noTRStored_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    CompTrace.Preserves NoTRStored (genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine CompTrace.Preserves.bind (noTRStored_getKey b idStateIdx .identity) fun _ tr h => ?_
  rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
  exact noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl
    (noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl h)))))

private theorem noTRStored_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    CompTrace.Preserves NoTRStored (genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine CompTrace.Preserves.bind (noTRStored_getKey b idStateIdx .identity) fun _ tr h => ?_
  rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
  exact noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl
    (noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl h)))))

private theorem noTRStored_genOneTimePrekey (b : Participant) :
    CompTrace.Preserves NoTRStored (genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey; intro tr h
  rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
  exact noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl
    (noTRStored_append_nonTRSt rfl (noTRStored_append_nonTRSt rfl h)))

private theorem noTRStored_setupTrace (r : ProtocolSetup) : NoTRStored (setupTrace r) := by
  unfold setupTrace setupAct
  refine CompTrace.Preserves.bind (noTRStored_registerIdentity r.alice) (fun _ => ?_) Trace.nil noTRStored_nil
  refine CompTrace.Preserves.bind (noTRStored_registerIdentity r.bob) fun idB => ?_
  refine CompTrace.Preserves.bind (noTRStored_genSignedPrekey r.bob idB) fun _ => ?_
  refine CompTrace.Preserves.bind (noTRStored_genPQPrekey r.bob idB) fun _ => ?_
  cases r.withOpk
  · exact CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.bind (noTRStored_genOneTimePrekey r.bob) fun _ => CompTrace.Preserves.pure _

theorem le_runMoves_fst : ∀ (ms : List Move) (tr : ExecTrace), tr ≤ (runMoves ms tr).1
  | [], tr => Trace.le_refl tr
  | m :: ms, tr => by
    unfold runMoves
    exact Trace.le_trans tr (m.next tr) (runMoves ms (m.next tr)).1
      (m.act.run tr).2.property (le_runMoves_fst ms (m.next tr))

theorem mem_availableStates_of_trStateStoredAt (r₀ : ProtocolSetup) (ms : List Move)
    {me : Participant} {st : TRState} {stH : Nat}
    (hst : TRStateStoredAt me st stH (runTraceMoves r₀ ms)) :
    st ∈ availableStates r₀ (runTraceMoves r₀ ms) := by
  unfold TRStateStoredAt at hst
  have hlt : stH < (runTraceMoves r₀ ms).length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := TTRStEntry) (runTraceMoves r₀ ms) stH
    rw [hst] at this; exact this
  have hge : (setupTrace r₀).length ≤ stH := by
    by_contra hlt_setup
    have hinit : stH < (setupTrace r₀).length := Nat.lt_of_not_le hlt_setup
    have hle : setupTrace r₀ ≤ runTraceMoves r₀ ms := by
      unfold runTraceMoves setupTrace; unfold runMoves; exact le_runMoves_fst ms _
    have h_at : ((setupTrace r₀).at? stH : Option TTRStEntry) = some ⟨⟨me, st⟩⟩ := by
      rw [Trace.at?_eq_some] at hst ⊢
      exact ⟨hinit, by rw [Trace.at_le (setupTrace r₀) (runTraceMoves r₀ ms) stH hinit hle]; exact hst.2⟩
    exact noTRStored_setupTrace r₀ me st stH h_at
  unfold availableStates
  rw [List.mem_map]
  refine ⟨⟨me, st⟩, ?_, rfl⟩
  unfold storedStates DY.Libsignal.Composed.Refinement.newIndices DY.ExecTrace.getLocalStateAt
  rw [List.mem_filterMap]
  refine ⟨stH, List.mem_range'.mpr ⟨stH - (setupTrace r₀).length, by omega, by omega⟩, ?_⟩
  rw [hst]; rfl

theorem macKdfSafe_tr_trunc8_inv_strong (r₀ : ProtocolSetup) (ms : List Move) (inp₀ : DY.Bytes)
    (hreach : (runTraceMoves r₀ ms).Reachable DY.Libsignal.Composed.reachability)
    (hknows : (Trunc.trunc8 inp₀).AttackerKnows (runTraceMoves r₀ ms)) :
    inp₀.AttackerKnows (runTraceMoves r₀ ms) ∨
    ∃ (pqSalt seed myIk peerIk a : DY.Bytes) (ns pn : UInt32) (m pqMsg : DY.Bytes)
      (t_s : Nat) (st_s : TRState),
      inp₀ = hmac (trMsgKeys pqSalt seed).macKey
        (Concat.concat myIk (Concat.concat peerIk
          (trHonestWireMsg (dhPk a) ns pn
            (SymEnc.symEnc (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv m) pqMsg))) ∧
      pqSalt.AttackerKnows (runTraceMoves r₀ ms) ∧
      (Concat.concat
        (trHonestWireMsg (dhPk a) ns pn
          (SymEnc.symEnc (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv m) pqMsg)
        (Trunc.trunc8 inp₀)).AttackerKnows (runTraceMoves r₀ ms) ∧
      a = randTerm t_s 32 ∧
      st_s ∈ availableStates r₀ (runTraceMoves r₀ ms) ∧
      st_s.myIk = myIk ∧
      st_s.peerIk = peerIk ∧
      (kdfCk st_s.cks).2 = seed := by
  have hsafe := truncSafeStrong_of_attackerKnows_reachable hreach hknows
  rcases (truncSafeStrong_trunc8_iff inp₀).mp hsafe with
    hinp_ak | ⟨pqSalt, seed, myIk, peerIk, a, ns, pn, m, pqMsg, t_s, stH, me, st_s,
      hinp_eq, hpq_ak, ht'_ak, ha_eq, hst_at, hmyIk, hpeerIk, hseed⟩
  · exact Or.inl hinp_ak
  · exact Or.inr ⟨pqSalt, seed, myIk, peerIk, a, ns, pn, m, pqMsg, t_s, st_s,
      hinp_eq, hpq_ak, ht'_ak, ha_eq,
      mem_availableStates_of_trStateStoredAt r₀ ms hst_at, hmyIk, hpeerIk, hseed⟩

end Symbolic.Swarm.CREF.TR.G1
