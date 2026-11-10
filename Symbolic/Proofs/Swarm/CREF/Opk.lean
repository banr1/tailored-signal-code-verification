/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.Random
import DY.Actions.ProtocolEvent
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# One-Time Pre-Key Usage Preservation

Proves that Bob's one-time pre-key is unused on `setupTrace r` and that `opkUsedB` is preserved
by quiet (`NoSessionEffect`) moves and by any move sequence outside an OPK-consuming `Move.bobStart`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

open DY
open DY.Libsignal
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace

/-! ## `NoMatchingEvent` and `opkUsedB` -/

/-- No `PQXDHEvent` on `tr` satisfies `p`. -/
def NoMatchingEvent (p : PQXDHEvent → Bool) (tr : ExecTrace) : Prop :=
  ∀ j (e : PQXDHEntry), tr.at? j = some e → p e.ev = false

theorem someEventB_eq_false_iff (p : PQXDHEvent → Bool) (tr : ExecTrace) :
    (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) tr p = false ↔ NoMatchingEvent p tr := by
  unfold NoMatchingEvent; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [List.any_eq_false]
  constructor
  · intro h j e hj
    have hlt : j < tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := PQXDHEntry) tr j
      rw [hj] at this; exact this
    have hj' := h j (List.mem_range.mpr hlt)
    simp only [hj, Bool.not_eq_true] at hj'
    exact hj'
  · intro h i _
    rcases hi : (tr.at? i : Option PQXDHEntry) with _ | e
    · simp
    · simp [h i e hi]

theorem noMatchingEvent_append_nonEvent {p : PQXDHEvent → Bool}
    {T : Type} [ExecTraceTypes.Has T] {x : T}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option PQXDHEntry) = none)
    {tr : ExecTrace} (htr : NoMatchingEvent p tr) : NoMatchingEvent p (tr.append x) := by
  intro j e h
  rcases at?_append_cases h with ⟨_, h'⟩ | ⟨_, hp⟩
  · exact htr j e h'
  · rw [hnone] at hp; cases hp

theorem noMatchingEvent_append_event {p : PQXDHEvent → Bool}
    {tr : ExecTrace} (htr : NoMatchingEvent p tr)
    {ev : PQXDHEvent} (hev : p ev = false) :
    NoMatchingEvent p (tr.append (PQEvE ev)) := by
  intro j e h
  rcases at?_append_cases h with ⟨_, h'⟩ | ⟨_, hp⟩
  · exact htr j e h'
  · rw [proj_inj_eq] at hp
    rcases e with ⟨ev'⟩
    cases hp
    exact hev

abbrev isOpkUsedPred (b : Participant) (opkPk : DY.Bytes) : PQXDHEvent → Bool :=
  fun
    | .OPKUsed b' o => b' == b && o == opkPk
    | _ => false

theorem opkUsedB_eq_false_iff (tr : ExecTrace) (b : Participant) (opkPk : DY.Bytes) :
    opkUsedB tr b opkPk = false ↔ NoMatchingEvent (isOpkUsedPred b opkPk) tr := by
  have heq : opkUsedB tr b opkPk = (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) tr (isOpkUsedPred b opkPk) := by
    unfold opkUsedB
    congr 1
    funext x
    cases x <;> rfl
  rw [heq]
  exact someEventB_eq_false_iff (isOpkUsedPred b opkPk) tr

theorem noMatchingEvent_mono_false {p : PQXDHEvent → Bool} {tr₁ tr₂ : ExecTrace}
    (hle : tr₁ ≤ tr₂) (h : NoMatchingEvent p tr₂) : NoMatchingEvent p tr₁ := by
  intro j e hj
  have hj₂ := Trace.at?_le (EntryT := PQXDHEntry) tr₁ tr₂ j hle
  rw [hj] at hj₂
  exact h j e hj₂

theorem opkUsedB_mono {tr₁ tr₂ : ExecTrace} {b : Participant} {opkPk : DY.Bytes}
    (hle : tr₁ ≤ tr₂) (h : opkUsedB tr₁ b opkPk = true) :
    opkUsedB tr₂ b opkPk = true := by
  rcases h₂ : opkUsedB tr₂ b opkPk with _ | _
  · have hno₂ := (opkUsedB_eq_false_iff tr₂ b opkPk).mp h₂
    have hno₁ := noMatchingEvent_mono_false hle hno₂
    have h₁ := (opkUsedB_eq_false_iff tr₁ b opkPk).mpr hno₁
    rw [h] at h₁; cases h₁
  · rfl

/-! ## Per-primitive and per-move preservation of `NoMatchingEvent` -/

section NoMatchingPreserves

variable (b0 : Participant) (opk0 : DY.Bytes)

abbrev InvOpk := NoMatchingEvent (isOpkUsedPred b0 opk0)

private theorem invOpk_sendMessage (m : DY.Bytes) :
    Preserves (InvOpk b0 opk0) (Network.sendMessage m) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk]
  exact noMatchingEvent_append_nonEvent rfl h

private theorem invOpk_genRand (n : Nat) :
    Preserves (InvOpk b0 opk0) (Random.genRand n) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact noMatchingEvent_append_nonEvent rfl h

private theorem invOpk_logEvent_tr (ev : TREvent) :
    Preserves (InvOpk b0 opk0) (ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact noMatchingEvent_append_nonEvent rfl h

private theorem invOpk_logEvent_c (ev : ComposedEvent) :
    Preserves (InvOpk b0 opk0) (ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact noMatchingEvent_append_nonEvent rfl h

private theorem invOpk_logEvent_pq (ev : PQXDHEvent)
    (hev : isOpkUsedPred b0 opk0 ev = false) :
    Preserves (InvOpk b0 opk0) (ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact noMatchingEvent_append_event h hev

private theorem invOpk_storeLocalState_tr (me : Participant) (st : TRState) :
    Preserves (InvOpk b0 opk0) (PersistentLocalState.storeLocalState me st) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact noMatchingEvent_append_nonEvent rfl h

private theorem invOpk_storeLocalState_pq (me : Participant) (st : PQXDHState) :
    Preserves (InvOpk b0 opk0) (PersistentLocalState.storeLocalState me st) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact noMatchingEvent_append_nonEvent rfl h

private theorem invOpk_getKey (p : Participant) (stateIdx : Nat) (kind : KeyKind) :
    Preserves (InvOpk b0 opk0) (getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p stateIdx) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

theorem preserves_noMatchingEvent_registerIdentity (p : Participant) :
    Preserves (InvOpk b0 opk0) (registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (invOpk_genRand b0 opk0 32) fun _ => ?_
  refine Preserves.bind (invOpk_logEvent_pq b0 opk0 _ rfl) fun _ => ?_
  refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
  refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
  exact invOpk_storeLocalState_pq b0 opk0 p _

theorem preserves_noMatchingEvent_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves (InvOpk b0 opk0) (genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine Preserves.bind (invOpk_getKey b0 opk0 b idStateIdx .identity) fun _ => ?_
  refine Preserves.bind (invOpk_genRand b0 opk0 32) fun _ => ?_
  refine Preserves.bind (invOpk_genRand b0 opk0 64) fun _ => ?_
  refine Preserves.bind (invOpk_logEvent_pq b0 opk0 _ rfl) fun _ => ?_
  refine Preserves.bind (invOpk_storeLocalState_pq b0 opk0 b _) fun _ => ?_
  refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
  refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
  exact Preserves.pure _

theorem preserves_noMatchingEvent_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves (InvOpk b0 opk0) (genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine Preserves.bind (invOpk_getKey b0 opk0 b idStateIdx .identity) fun _ => ?_
  refine Preserves.bind (invOpk_genRand b0 opk0 64) fun _ => ?_
  refine Preserves.bind (invOpk_genRand b0 opk0 64) fun _ => ?_
  refine Preserves.bind (invOpk_logEvent_pq b0 opk0 _ rfl) fun _ => ?_
  refine Preserves.bind (invOpk_storeLocalState_pq b0 opk0 b _) fun _ => ?_
  refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
  refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
  exact Preserves.pure _

theorem preserves_noMatchingEvent_genOneTimePrekey (b : Participant) :
    Preserves (InvOpk b0 opk0) (genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine Preserves.bind (invOpk_genRand b0 opk0 32) fun _ => ?_
  refine Preserves.bind (invOpk_logEvent_pq b0 opk0 _ rfl) fun _ => ?_
  refine Preserves.bind (invOpk_storeLocalState_pq b0 opk0 b _) fun _ => ?_
  refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
  exact Preserves.pure _

theorem preserves_noMatchingEvent_setupAct (a b : Participant) (withOpk : Bool) :
    Preserves (InvOpk b0 opk0) (setupAct a b withOpk) := by
  unfold setupAct
  refine Preserves.bind (preserves_noMatchingEvent_registerIdentity b0 opk0 a) fun _ => ?_
  refine Preserves.bind (preserves_noMatchingEvent_registerIdentity b0 opk0 b) fun idB => ?_
  refine Preserves.bind (preserves_noMatchingEvent_genSignedPrekey b0 opk0 b idB) fun _ => ?_
  refine Preserves.bind (preserves_noMatchingEvent_genPQPrekey b0 opk0 b idB) fun _ => ?_
  cases withOpk
  · exact Preserves.pure _
  · exact Preserves.bind (preserves_noMatchingEvent_genOneTimePrekey b0 opk0 b) fun _ =>
      Preserves.pure _

theorem preserves_noMatchingEvent_aliceStart
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles) :
    Preserves (InvOpk b0 opk0) (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr htr
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr htr
    (noMatchingEvent_append_nonEvent rfl htr) ?_
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have h1 : InvOpk b0 opk0 ((tr.append (RndE 32)).append (RndE 32)) :=
    noMatchingEvent_append_nonEvent rfl (noMatchingEvent_append_nonEvent rfl htr)
  refine (show Preserves (InvOpk b0 opk0) _ by
    refine Preserves.bind (invOpk_genRand b0 opk0 32) fun _ => ?_
    refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
    refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
    refine Preserves.bind Preserves.traceLength fun _ => ?_
    refine Preserves.bind (invOpk_logEvent_pq b0 opk0 _ rfl) fun _ => ?_
    refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
    refine Preserves.bind (invOpk_logEvent_c b0 opk0 _) fun _ => ?_
    exact invOpk_storeLocalState_tr b0 opk0 a _) _ h1

theorem preserves_noMatchingEvent_dhRatchetStep
    (st : TRState) (peerRatchetKey : DY.Bytes) :
    Preserves (InvOpk b0 opk0) (DY.Libsignal.TripleRatchet.dhRatchetStep st peerRatchetKey) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine Preserves.bind (Preserves.guardP _) fun _ => ?_
  refine Preserves.bind (invOpk_genRand b0 opk0 32) fun _ => ?_
  exact Preserves.pure _

theorem preserves_noMatchingEvent_ensureReceiverChain
    (st : TRState) (peerRatchetKey : DY.Bytes) :
    Preserves (InvOpk b0 opk0) (DY.Libsignal.TripleRatchet.ensureReceiverChain st peerRatchetKey) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact Preserves.pure _
  · refine Preserves.bind (preserves_noMatchingEvent_dhRatchetStep b0 opk0 st peerRatchetKey)
      fun ⟨_, _⟩ => ?_
    exact Preserves.pure _
  · exact Preserves.failure

theorem preserves_noMatchingEvent_logSkippedKeys
    (sinfo : SessionInfo) (rk : DY.Bytes) (rIdx srcIdx : Nat) :
    ∀ (n : Nat) (ck : DY.Bytes) (idx : UInt32),
      Preserves (InvOpk b0 opk0)
        (DY.Libsignal.TripleRatchet.logSkippedKeys sinfo rk rIdx srcIdx ck idx n)
  | 0, _, _ => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    exact Preserves.pure ()
  | n + 1, ck, idx => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
    exact preserves_noMatchingEvent_logSkippedKeys sinfo rk rIdx srcIdx n (DY.Libsignal.TripleRatchet.kdfCk ck).1 (idx + 1)

theorem preserves_noMatchingEvent_logMessageKeyAndStore
    (me : Participant) (sinfo : SessionInfo) (dir : KeyDir) (seed pqSalt : DY.Bytes)
    (ctr : UInt32) (rIdx parIdx : Nat) (st : TRState) :
    Preserves (InvOpk b0 opk0)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me sinfo dir seed pqSalt ctr
        rIdx parIdx st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
  exact invOpk_storeLocalState_tr b0 opk0 me st

theorem preserves_noMatchingEvent_messageEncrypt
    (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    Preserves (InvOpk b0 opk0)
      (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun _ => ?_
  refine Preserves.bind (Preserves.guardP _) fun _ => ?_
  refine Preserves.bind (invOpk_genRand b0 opk0 32) fun _ => ?_
  refine Preserves.bind (invOpk_genRand b0 opk0 coinsLen) fun _ => ?_
  refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage pqIdx) fun _ => ?_
  refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
  refine Preserves.bind
    (preserves_noMatchingEvent_logMessageKeyAndStore b0 opk0 me _ .sender _ _ _ _ _ _)
    fun _ => ?_
  exact invOpk_sendMessage b0 opk0 _

theorem preserves_noMatchingEvent_messageEncryptAbort
    (me : Participant) (stateIdx : Nat) :
    Preserves (InvOpk b0 opk0)
      (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  refine Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun _ => ?_
  refine Preserves.bind (invOpk_genRand b0 opk0 32) fun _ => ?_
  exact Preserves.failure

theorem preserves_noMatchingEvent_messageDecrypt
    (me : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves (InvOpk b0 opk0)
      (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun st0 => ?_
  refine Preserves.bind (Preserves.receiveSignalMsg msgIdx) fun msg => ?_
  refine Preserves.bind (preserves_noMatchingEvent_ensureReceiverChain b0 opk0 st0 msg.ratchetKey)
    fun ⟨st, c, ratcheted⟩ => ?_
  dsimp only
  split
  · split
    · refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
      refine Preserves.bind (Preserves.receiveMessage pqIdx) fun pqSalt => ?_
      refine Preserves.bind (Preserves.verifyMacAndDecrypt st msg pqSalt _) fun _ => ?_
      split
      · refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
        refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
        refine Preserves.bind (preserves_noMatchingEvent_logSkippedKeys b0 opk0 _ _ _ _ _ _ _)
          fun _ => ?_
        refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
        exact preserves_noMatchingEvent_logMessageKeyAndStore b0 opk0 me _ .receiver _ _ _ _ _ _
      · refine Preserves.bind (preserves_noMatchingEvent_logSkippedKeys b0 opk0 _ _ _ _ _ _ _)
          fun _ => ?_
        refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
        exact preserves_noMatchingEvent_logMessageKeyAndStore b0 opk0 me _ .receiver _ _ _ _ _ _
    · exact Preserves.failure
  · exact Preserves.failure

theorem preserves_noMatchingEvent_messageDecryptSkipped
    (me : Participant) (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves (InvOpk b0 opk0)
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun st => ?_
  refine Preserves.bind (Preserves.receiveSignalMsg msgIdx) fun msg => ?_
  refine Preserves.bind (Preserves.getEntry skIdx) fun ⟨ev⟩ => ?_
  cases ev with
  | SkippedKeyStored _ _ _ _ _ _ =>
    dsimp only
    refine Preserves.bind (Preserves.guardP _) fun _ => ?_
    refine Preserves.bind (Preserves.guardTrace _) fun _ => ?_
    split
    · refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
      refine Preserves.bind (Preserves.receiveMessage pqIdx) fun pqSalt => ?_
      refine Preserves.bind (Preserves.verifyMacAndDecrypt st msg pqSalt _) fun _ => ?_
      refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
      refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
      exact preserves_noMatchingEvent_logMessageKeyAndStore b0 opk0 me _ .receiver _ _ _ _ _ _
    · exact Preserves.failure
  | _ => exact Preserves.failure

theorem preserves_noMatchingEvent_exposeKey
    (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    Preserves (InvOpk b0 opk0) (DY.Libsignal.TripleRatchet.exposeKey me stateIdx k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun st => ?_
  cases k with
  | ckr idx =>
    dsimp only
    split
    · exact Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ =>
        invOpk_sendMessage b0 opk0 _
    · exact Preserves.failure
  | _ =>
    exact Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ =>
      invOpk_sendMessage b0 opk0 _

theorem preserves_noMatchingEvent_exposeSpqr
    (me : Participant) (stateIdx : Nat) :
    Preserves (InvOpk b0 opk0) (DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  refine Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun _ => ?_
  refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ =>
    invOpk_sendMessage b0 opk0 _

theorem preserves_noMatchingEvent_exposeSkipped (evIdx : Nat) :
    Preserves (InvOpk b0 opk0) (DY.Libsignal.TripleRatchet.exposeSkipped evIdx) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine Preserves.bind (Preserves.getEntry evIdx) fun ⟨ev⟩ => ?_
  cases ev with
  | SkippedKeyStored _ _ _ _ _ _ =>
    dsimp only
    refine Preserves.bind (Preserves.guardTrace _) fun _ => ?_
    refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ =>
      invOpk_sendMessage b0 opk0 _
  | _ => exact Preserves.failure

theorem preserves_noMatchingEvent_compromiseIK (p : Participant) (stateIdx : Nat) :
    Preserves (InvOpk b0 opk0) (compromiseIK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  refine Preserves.bind (invOpk_getKey b0 opk0 p stateIdx .identity) fun _ => ?_
  refine Preserves.bind (invOpk_logEvent_pq b0 opk0 _ rfl) fun _ => ?_
  exact invOpk_sendMessage b0 opk0 _

theorem preserves_noMatchingEvent_compromiseSPK (b : Participant) (stateIdx : Nat) :
    Preserves (InvOpk b0 opk0) (compromiseSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  refine Preserves.bind (invOpk_getKey b0 opk0 b stateIdx .signedPrekey) fun _ => ?_
  refine Preserves.bind (invOpk_logEvent_pq b0 opk0 _ rfl) fun _ => ?_
  exact invOpk_sendMessage b0 opk0 _

theorem preserves_noMatchingEvent_compromisePQSPK (b : Participant) (stateIdx : Nat) :
    Preserves (InvOpk b0 opk0) (compromisePQSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  refine Preserves.bind (invOpk_getKey b0 opk0 b stateIdx .pqPrekey) fun _ => ?_
  refine Preserves.bind (invOpk_logEvent_pq b0 opk0 _ rfl) fun _ => ?_
  exact invOpk_sendMessage b0 opk0 _

theorem preserves_noMatchingEvent_compromiseOPK (b : Participant) (stateIdx : Nat) :
    Preserves (InvOpk b0 opk0) (compromiseOPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  refine Preserves.bind (invOpk_getKey b0 opk0 b stateIdx .oneTimePrekey) fun _ => ?_
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (invOpk_logEvent_pq b0 opk0 _ rfl) fun _ => ?_
  exact invOpk_sendMessage b0 opk0 _

theorem preserves_noMatchingEvent_move_of_not_bobStart
    (m : Move)
    (hnot : ∀ b a kh regIdxA mh pqIdx spqrMsgIdx shown,
      m ≠ .bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown) :
    Preserves (InvOpk b0 opk0) (Move.act m) := by
  cases m with
  | setup a b withOpk => exact preserves_noMatchingEvent_setupAct b0 opk0 a b withOpk
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact Preserves.bind (preserves_noMatchingEvent_aliceStart b0 opk0 a b idStateIdx regIdxB h)
      fun _ => Preserves.pure _
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
    exact False.elim (hnot b a kh regIdxA mh pqIdx spqrMsgIdx shown rfl)
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact Preserves.bind (preserves_noMatchingEvent_messageEncrypt b0 opk0 me stateIdx coinsLen pqIdx)
      fun _ => Preserves.pure _
  | encryptAbort me stateIdx =>
    exact Preserves.bind (preserves_noMatchingEvent_messageEncryptAbort b0 opk0 me stateIdx)
      fun _ => Preserves.pure _
  | encryptFail me stateIdx coinsLen =>
    unfold Move.act
    refine Preserves.bind Preserves.traceLength fun n => ?_
    exact Preserves.bind (preserves_noMatchingEvent_messageEncrypt b0 opk0 me stateIdx coinsLen (n + 3))
      fun _ => Preserves.pure _
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact Preserves.bind (preserves_noMatchingEvent_messageDecrypt b0 opk0 me stateIdx msgIdx pqIdx spqrMsgIdx)
      fun _ => Preserves.pure _
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx _ =>
    exact Preserves.bind (preserves_noMatchingEvent_messageDecryptSkipped b0 opk0 me stateIdx msgIdx skIdx pqIdx spqrMsgIdx)
      fun _ => Preserves.pure _
  | reject _ => exact Preserves.pure _
  | compromiseIK p stateIdx =>
    exact Preserves.bind (preserves_noMatchingEvent_compromiseIK b0 opk0 p stateIdx)
      fun _ => Preserves.pure _
  | compromiseSPK b stateIdx =>
    exact Preserves.bind (preserves_noMatchingEvent_compromiseSPK b0 opk0 b stateIdx)
      fun _ => Preserves.pure _
  | compromisePQSPK b stateIdx =>
    exact Preserves.bind (preserves_noMatchingEvent_compromisePQSPK b0 opk0 b stateIdx)
      fun _ => Preserves.pure _
  | compromiseOPK b stateIdx =>
    exact Preserves.bind (preserves_noMatchingEvent_compromiseOPK b0 opk0 b stateIdx)
      fun _ => Preserves.pure _
  | exposeKey me stateIdx k =>
    exact Preserves.bind (preserves_noMatchingEvent_exposeKey b0 opk0 me stateIdx k)
      fun _ => Preserves.pure _
  | exposeSpqr me stateIdx =>
    exact Preserves.bind (preserves_noMatchingEvent_exposeSpqr b0 opk0 me stateIdx)
      fun _ => Preserves.pure _
  | exposeSkipped evIdx =>
    exact Preserves.bind (preserves_noMatchingEvent_exposeSkipped b0 opk0 evIdx)
      fun _ => Preserves.pure _
  | attackerSend msg =>
    exact Preserves.bind (invOpk_sendMessage b0 opk0 msg)
      fun _ => Preserves.pure _
  | brkDH =>
    exact invOpk_logEvent_pq b0 opk0 .BrokenDH rfl
  | brkKEM =>
    exact invOpk_logEvent_pq b0 opk0 .BrokenKEM rfl

theorem preserves_noMatchingEvent_bobStart_of_opk_isNone
    (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32)
    (hnone : kh.opk = none) :
    Preserves (InvOpk b0 opk0) (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr htr
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr htr ?_
  intro ikB spkSk pqsk opkSk ikA vkA ek ct honest keys _ _ _ hopk _ _ _ _ _
  have hopkNone : opkSk = none := by
    rcases hopk with ⟨_, rfl⟩ | ⟨idx, _, hsome, _⟩
    · rfl
    · rw [hnone] at hsome; cases hsome
  subst hopkNone
  refine (show Preserves (InvOpk b0 opk0) _ by
    dsimp only [Option.map]
    refine Preserves.bind (Preserves.receiveSignalMsg mh.msg) fun msg => ?_
    refine Preserves.bind (preserves_noMatchingEvent_ensureReceiverChain b0 opk0 _ msg.ratchetKey)
      fun ⟨st, c, ratcheted⟩ => ?_
    dsimp only
    split
    · split
      · refine Preserves.bind (invOpk_sendMessage b0 opk0 _) fun _ => ?_
        refine Preserves.bind (Preserves.receiveMessage pqIdx) fun pqSalt => ?_
        refine Preserves.bind (Preserves.verifyMacAndDecrypt st msg pqSalt _) fun _ => ?_
        refine Preserves.bind Preserves.traceLength fun _ => ?_
        refine Preserves.bind (invOpk_logEvent_pq b0 opk0 _ rfl) fun _ => ?_
        split
        · refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
          refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
          refine Preserves.bind (invOpk_logEvent_c b0 opk0 _) fun _ => ?_
          refine Preserves.bind Preserves.traceLength fun _ => ?_
          refine Preserves.bind (preserves_noMatchingEvent_logSkippedKeys b0 opk0 _ _ _ _ _ _ _)
            fun _ => ?_
          refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
          exact preserves_noMatchingEvent_logMessageKeyAndStore b0 opk0 b _ .receiver _ _ _ _ _ _
        · refine Preserves.bind (invOpk_logEvent_c b0 opk0 _) fun _ => ?_
          refine Preserves.bind Preserves.traceLength fun _ => ?_
          refine Preserves.bind (preserves_noMatchingEvent_logSkippedKeys b0 opk0 _ _ _ _ _ _ _)
            fun _ => ?_
          refine Preserves.bind (invOpk_logEvent_tr b0 opk0 _) fun _ => ?_
          exact preserves_noMatchingEvent_logMessageKeyAndStore b0 opk0 b _ .receiver _ _ _ _ _ _
      · exact Preserves.failure
    · exact Preserves.failure) tr htr

theorem preserves_noMatchingEvent_move_bobStart_of_opk_isNone
    (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (shown : Nat)
    (hnone : kh.opk = none) :
    Preserves (InvOpk b0 opk0) (Move.act (.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown)) := by
  exact Preserves.bind (preserves_noMatchingEvent_bobStart_of_opk_isNone b0 opk0 b a kh regIdxA mh pqIdx spqrMsgIdx hnone)
    fun _ => Preserves.pure _

theorem preserves_noMatchingEvent_bobStart_or_terms4
    (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (shown : Nat)
    (tr : ExecTrace) (htr : InvOpk b0 opk0 tr) :
    InvOpk b0 opk0 ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next tr) ∨
      ∃ ek ct raw opkPk,
        received tr [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr).toList = [ek, ct, raw, opkPk] := by
  rcases hopk : kh.opk with _ | opkIdx
  · exact Or.inl (preserves_noMatchingEvent_move_bobStart_of_opk_isNone b0 opk0 b a kh regIdxA mh pqIdx spqrMsgIdx shown hopk tr htr)
  · unfold Move.next Move.act; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
    rw [run_bind_assoc_snd]
    refine bind_bobHandshake_at (Inv := fun t => InvOpk b0 opk0 t ∨
        ∃ ek ct raw opkPk,
          received tr [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr).toList = [ek, ct, raw, opkPk])
      b a kh regIdxA mh.ek mh.ct tr (Or.inl htr) ?_
    intro ikB spkSk pqsk opkSk ikA vkA ek ct honest keys _ _ _ hopkSt _ hek hct _ _
    rcases hopkSt with ⟨hnone, _⟩ | ⟨idx, o, hsome, rfl, hstO⟩
    · rw [hopk] at hnone; cases hnone
    · unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
      rw [run_bind_assoc_snd, run_bind_assoc_snd]
      refine bind_receiveMessage_at
        (Inv := fun t => InvOpk b0 opk0 t ∨
          ∃ ek ct raw opkPk,
            received tr [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr).toList = [ek, ct, raw, opkPk])
        mh.msg tr (Or.inl htr) fun raw hraw _ => ?_
      refine Or.inr ⟨ek, ct, raw, DY.DiffieHellman.dhPk o, ?_⟩
      have h1 : tr.getMessageSentAt mh.ek = some ek := by
        simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]; rw [hek]
      have h2 : tr.getMessageSentAt mh.ct = some ct := by
        simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]; rw [hct]
      have h3 : tr.getMessageSentAt mh.msg = some raw := by
        simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]; rw [hraw]
      have h4 : bobOpkPk b kh tr = some (DY.DiffieHellman.dhPk o) := by
        unfold bobOpkPk DY.Libsignal.PQXDH.getKey
        rcases kh with ⟨_, _, _, oi⟩
        dsimp only at hsome ⊢
        subst hsome
        dsimp only [Option.bind]
        rw [run_bind_fst, getLocalState_pq_fst, getLocalState_pq_snd, hstO]
        simp [_root_.guard, run_bind_fst, Traceful.run_pure]
      simp [received, h1, h2, h3, h4]

end NoMatchingPreserves

theorem opkUsedB_next_of_not_bobStart (tr : ExecTrace) (b0 : Participant) (opk0 : DY.Bytes)
    (m : Move)
    (hnot : ∀ b a kh regIdxA mh pqIdx spqrMsgIdx shown,
      m ≠ .bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown) :
    opkUsedB (m.next tr) b0 opk0 = opkUsedB tr b0 opk0 := by
  rcases h : opkUsedB tr b0 opk0 with _ | _
  · exact (opkUsedB_eq_false_iff (m.next tr) b0 opk0).mpr
      (preserves_noMatchingEvent_move_of_not_bobStart b0 opk0 m hnot tr
        ((opkUsedB_eq_false_iff tr b0 opk0).mp h))
  · exact opkUsedB_mono ((Move.act m).run tr).2.property h

theorem opkUsedB_setupTrace (r : ProtocolSetup) (b0 : Participant) (opk0 : DY.Bytes) :
    opkUsedB (setupTrace r) b0 opk0 = false := by
  change opkUsedB (r.setupMove.next Trace.nil) b0 opk0 = false
  rw [opkUsedB_next_of_not_bobStart Trace.nil b0 opk0 r.setupMove
    (fun _ _ _ _ _ _ _ _ h => nomatch h)]
  unfold opkUsedB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  simp [Symbolic.DYBridge.DY.Trace.length_eq_1]

/-! ## Explanation-block preservation of `opkUsedB` -/

theorem opkUsedB_of_noSessionEffect {tr : ExecTrace} {m : Move} (h : NoSessionEffect tr m)
    (b0 : Participant) (opk0 : DY.Bytes) :
    opkUsedB (m.next tr) b0 opk0 = opkUsedB tr b0 opk0 := by
  have hle : tr ≤ m.next tr := ((Move.act m).run tr).2.property
  rcases h0 : opkUsedB tr b0 opk0 with _ | _
  · refine (opkUsedB_eq_false_iff _ b0 opk0).2 fun j e hj => ?_
    have hno := (opkUsedB_eq_false_iff _ b0 opk0).1 h0
    by_cases hlt : j < tr.length
    · have hj' : j < (m.next tr).length := Nat.lt_of_lt_of_le hlt (Trace.length_le _ _ hle)
      have heq : ((m.next tr).at? j : Option PQXDHEntry) = tr.at? j := by
        simp only [Trace.at?, hlt, hj', ↓reduceDIte, Trace.at_le tr (m.next tr) j hlt hle]
      rw [heq] at hj
      exact hno j e hj
    · have hj' : j < (m.next tr).length := by
        unfold Trace.at? at hj; split at hj <;> [assumption; cases hj]
      have hmem : j ∈ newIndices tr (m.next tr) := by
        simp only [newIndices, List.mem_range'_1]; omega
      exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_pred_eq_false (h j hmem).2.1 hj
  · exact opkUsedB_mono hle h0

theorem not_opkNamed_true_of_opkNamed_false {r : ProtocolSetup} {b : HwBytes}
    (h : OpkNamed r b false) : ¬ OpkNamed r b true := by
  rcases h with ⟨p₁, hp₁, hnone⟩
  rintro ⟨p₂, hp₂, hsome, _⟩
  cases hp₁.symm.trans hp₂
  rw [hnone] at hsome; cases hsome

theorem not_opkNamed_true_of_parsePreKeyWire_none {r : ProtocolSetup} {b : HwBytes}
    (h : parsePreKeyWire b = none) : ¬ OpkNamed r b true := by
  rintro ⟨p, hp, _⟩
  rw [h] at hp; cases hp

theorem not_opkNamed_true_of_preKeyId_ne {r : ProtocolSetup} {b : HwBytes}
    {pf : PreKeyFields}
    (hp : parsePreKeyWire b = some pf) (hne : pf.preKeyId ≠ some r.opkId) :
    ¬ OpkNamed r b true := by
  rintro ⟨p, hp', hsome, _⟩
  cases hp.symm.trans hp'
  exact hne hsome

theorem not_opkNamed_true_of_preKeyId_isNone {r : ProtocolSetup} {b : HwBytes}
    {pf : PreKeyFields}
    (hp : parsePreKeyWire b = some pf) (hnone : pf.preKeyId = none) :
    ¬ OpkNamed r b true :=
  not_opkNamed_true_of_preKeyId_ne hp (by rw [hnone]; simp)

theorem opkUsedB_next_eq_of_forall₂ {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {b0 : Participant} {opk0 : DY.Bytes} {tr : ExecTrace} {m : Move}
    {blk : List MachineEvent}
    (hs : m.isSetup = false) (ha : m.LogsSessionCompletion tr)
    (hm : List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis tr))
    (hcond : (∀ e ∈ blk, eventKind e ≠ .accept) ∨
      (∀ b, MachineEvent.recv b ∈ blk → ¬ OpkNamed r b true)) :
    opkUsedB (m.next tr) b0 opk0 = opkUsedB tr b0 opk0 := by
  by_cases hbob : ∃ b a kh regIdxA mh pqIdx spqrMsgIdx shown,
      m = .bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown
  · rcases hbob with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx, shown, rfl⟩
    rcases hcond with hnoacc | hnoopk
    · refine opkUsedB_of_noSessionEffect
        (noSessionEffect_of_no_accept (m := .bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown)
          trivial ha ?_) b0 opk0
      intro v hv hvk
      obtain ⟨e, he, hev⟩ := xpl_forall₂_mem_right hm v hv
      exact hnoacc e he ((xpl_kind_of_matches hev).symm.trans hvk)
    · by_cases hv0 : (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).vis tr = []
      · exact opkUsedB_of_noSessionEffect (noSessionEffect_of_vis_nil hs ha hv0) b0 opk0
      · rcases shown with _ | n
        · exfalso
          apply hv0
          rw [xpl_vis_eq, exposures_nil_of_not_leakKind hs (by rintro ⟨⟩), List.append_nil]
          rfl
        · rcases h0 : opkUsedB tr b0 opk0 with _ | _
          · refine (opkUsedB_eq_false_iff _ b0 opk0).mpr ?_
            rcases preserves_noMatchingEvent_bobStart_or_terms4 b0 opk0 b a kh regIdxA mh pqIdx
                spqrMsgIdx (n + 1) tr ((opkUsedB_eq_false_iff tr b0 opk0).mp h0) with
              hinv | ⟨ek, ct, raw, opkPk, h4⟩
            · exact hinv
            · exfalso
              have hvis : ∃ rest,
                  (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx (n + 1)).vis tr =
                    ⟨.recv, [ek, ct, raw, opkPk], .preKeyRecv, none⟩ :: rest := by
                rw [xpl_vis_eq, exposures_nil_of_not_leakKind hs (by rintro ⟨⟩), List.append_nil]
                dsimp only [xpl_ownVis, bobVis]
                rw [h4]
                exact ⟨_, rfl⟩
              obtain ⟨rest, hvis⟩ := hvis
              rw [hvis] at hm
              cases blk with
              | nil => cases hm
              | cons e₀ tail =>
                cases hm with
                | cons he₀ _ =>
                  obtain ⟨hk, hlay⟩ := he₀
                  cases e₀ with
                  | recv bytes =>
                    dsimp only [eventBytes] at hlay
                    exact hnoopk bytes (List.mem_cons_self) hlay.2
                  | pt _ => cases hk
                  | rng _ => cases hk
                  | send _ => cases hk
                  | accept _ => cases hk
                  | leak _ => cases hk
          · exact opkUsedB_mono ((Move.act _).run tr).2.property h0
  · refine opkUsedB_next_of_not_bobStart tr b0 opk0 m
      fun b a kh regIdxA mh pqIdx spqrMsgIdx shown hm' =>
        hbob ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx, shown, hm'⟩

theorem opkUsedB_runMoves_eq_of_forall₂ {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} (b0 : Participant) (opk0 : DY.Bytes) :
    ∀ (δ : List Move) (tr : ExecTrace) (blk : List MachineEvent),
      MovesFrom (fun tr m => m.isSetup = false ∧ m.LogsSessionCompletion tr) tr δ →
      List.Forall₂ (EventMatchesEntry interpretation r S g) blk (runMoves δ tr).2 →
      ((∀ e ∈ blk, eventKind e ≠ .accept) ∨
        (∀ b, MachineEvent.recv b ∈ blk → ¬ OpkNamed r b true)) →
      opkUsedB (runMoves δ tr).1 b0 opk0 = opkUsedB tr b0 opk0
  | [], tr, _, _, _, _ => rfl
  | m :: δ, tr, blk, ⟨⟨hs, ha⟩, hδ⟩, hm, hcond => by
    have hcons : (runMoves (m :: δ) tr).2 = m.vis tr ++ (runMoves δ (m.next tr)).2 := rfl
    rw [hcons] at hm
    have hlen : (m.vis tr).length ≤ blk.length := by
      rw [xpl_forall₂_length hm, List.length_append]; omega
    have hsplit : blk = blk.take (m.vis tr).length ++ blk.drop (m.vis tr).length :=
      (List.take_append_drop _ _).symm
    rw [hsplit] at hm
    obtain ⟨hm₁, hm₂⟩ := xpl_forall₂_append_split (by simp; omega) hm
    have hcond₁ : (∀ e ∈ blk.take (m.vis tr).length, eventKind e ≠ .accept) ∨
        (∀ b, MachineEvent.recv b ∈ blk.take (m.vis tr).length → ¬ OpkNamed r b true) :=
      hcond.elim (fun h => Or.inl fun e he => h e (List.mem_of_mem_take he))
        (fun h => Or.inr fun b hb => h b (List.mem_of_mem_take hb))
    have hcond₂ : (∀ e ∈ blk.drop (m.vis tr).length, eventKind e ≠ .accept) ∨
        (∀ b, MachineEvent.recv b ∈ blk.drop (m.vis tr).length → ¬ OpkNamed r b true) :=
      hcond.elim (fun h => Or.inl fun e he => h e (List.mem_of_mem_drop he))
        (fun h => Or.inr fun b hb => h b (List.mem_of_mem_drop hb))
    have hfst : (runMoves (m :: δ) tr).1 = (runMoves δ (m.next tr)).1 := rfl
    rw [hfst,
      opkUsedB_runMoves_eq_of_forall₂ b0 opk0 δ (m.next tr) _ hδ hm₂ hcond₂,
      opkUsedB_next_eq_of_forall₂ hs ha hm₁ hcond₁]

theorem opkUsedB_xplBlock_eq {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ δ : List Move} {acc blk : List MachineEvent}
    (b0 : Participant) (opk0 : DY.Bytes)
    (hB : XplBlock interpretation r S who g ms₀ δ acc blk)
    (hcond : (∀ e ∈ blk, eventKind e ≠ .accept) ∨
      (∀ b, MachineEvent.recv b ∈ blk → ¬ OpkNamed r b true)) :
    opkUsedB (runTraceMoves r (ms₀ ++ δ)) b0 opk0 = opkUsedB (runTraceMoves r ms₀) b0 opk0 := by
  have hs := hB.run.2.1
  have hanc := hB.run.2.2.1.2.1
  have hanc' := xpl_movesAnchored_append_right ms₀ δ (setupTrace r) hanc
  rw [← xpl_runTrace_eq] at hanc'
  rw [runTrace_append]
  exact opkUsedB_runMoves_eq_of_forall₂ b0 opk0 δ (runTraceMoves r ms₀) blk
    (xpl_movesFrom_of δ _ (fun m hm => hs m (List.mem_append_right _ hm)) hanc')
    hB.matched hcond

/-! ## Quiet moves (`NoSessionEffect`) leave `opkUsedB` unchanged -/

private theorem opk_at?_of_le_lt {EntryT α : Type} [TraceEntryHas EntryT α] {tr tr' : Trace α}
    (hle : tr ≤ tr') {j : Nat} (hj : j < tr.length) :
    (tr'.at? j : Option EntryT) = tr.at? j := by
  have hj' : j < tr'.length := Nat.lt_of_lt_of_le hj (Trace.length_le tr tr' hle)
  simp only [Trace.at?, hj, hj', dite_true, Trace.at_le tr tr' j hj hle]

/-- A move with `NoSessionEffect` leaves `opkUsedB` unchanged. -/
theorem rpk_opkUsedB_quiet {tr : ExecTrace} {m : Move} (h : NoSessionEffect tr m)
    (b0 : Participant) (opk0 : DY.Bytes) :
    DY.Libsignal.PQXDH.opkUsedB (m.next tr) b0 opk0 =
      DY.Libsignal.PQXDH.opkUsedB tr b0 opk0 := by
  have hle : tr ≤ m.next tr := ((Move.act m).run tr).2.property
  rcases h0 : DY.Libsignal.PQXDH.opkUsedB tr b0 opk0 with _ | _
  · refine (opkUsedB_eq_false_iff _ b0 opk0).2 fun j e hj => ?_
    have hno := (opkUsedB_eq_false_iff _ b0 opk0).1 h0
    by_cases hlt : j < tr.length
    · rw [opk_at?_of_le_lt hle hlt] at hj
      exact hno j e hj
    · have hjl : j < (m.next tr).length := by
        have := Trace.at?_eq_some_implies_length_le
          (EntryT := Symbolic.Swarm.COMPOSED.CompTrace.PQXDHEntry) (m.next tr) j
        rw [hj] at this; exact this
      have hmem : j ∈ newIndices tr (m.next tr) := by
        simp only [newIndices, List.mem_range'_1]; omega
      exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_pred_eq_false (h j hmem).2.1 hj
  · exact opkUsedB_mono hle h0

theorem rpk_opkUsedB_movesFrom_quiet (b0 : Participant) (opk0 : DY.Bytes) :
    ∀ (tr : ExecTrace) (δ : List Move), MovesFrom (fun tr m => NoSessionEffect tr m) tr δ →
      DY.Libsignal.PQXDH.opkUsedB (runMoves δ tr).1 b0 opk0 =
        DY.Libsignal.PQXDH.opkUsedB tr b0 opk0
  | _, [], _ => by simp [runMoves]
  | tr, m :: δ, ⟨h, hδ⟩ => by
    simp only [runMoves]
    rw [rpk_opkUsedB_movesFrom_quiet b0 opk0 (m.next tr) δ hδ, rpk_opkUsedB_quiet h]

end Symbolic.Swarm.CREF
