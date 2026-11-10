/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.UA.ClassicalBridge
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Specifications.Security.AsmSecure
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# CLI-Level Excuse Coverage on Break-Free Traces

Characterizes which model compromise excuses and queries remain active on CLI-explained traces
without quantum break or inversion events (`BreakFree evs`). Every `Explains` witness of a
`BreakFree` CLI trace satisfies `NoBreak` (`noBreak_explains`), eliminating all `BrokenDH`,
`BrokenKEM`, and dishonest `IdentityRegistered` disjuncts from the PQXDH and Triple Ratchet
compromise predicates and making `HNDLQuery` follow from `ForwardSecrecyQuery`
(`asmSecure_iff_without_hndl`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.CliCoverage

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent)
open Symbolic.Proofs.Swarm.UA.ClassicalBridge (BreakFree breakFree_of_cons breakFree_append)
open Symbolic.Swarm.COMPOSED (CompTrace.Preserves CompTrace.Preserves.bind
  CompTrace.Preserves.failure CompTrace.Preserves.getEntry CompTrace.Preserves.getLocalState_pq
  CompTrace.Preserves.getLocalState_tr CompTrace.Preserves.requireTracePredicate CompTrace.Preserves.guardP
  CompTrace.Preserves.guardTrace CompTrace.Preserves.pure CompTrace.Preserves.receiveMessage
  CompTrace.Preserves.receiveSignalMsg CompTrace.Preserves.traceLength
  CompTrace.Preserves.verifyMacAndDecrypt CompTrace.bind_aliceHandshake_at
  CompTrace.bind_bobHandshake_at)
open Symbolic.Swarm.COMPOSED.CompTrace (CEvE NetE PQEvE PQStE PQXDHEntry RndE TREvE TRStE
  eventLogged_append_other_iff eventLogged_append_same_iff)
open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.PQKem DY.Signature DY.X25519
open DY.Libsignal DY.Libsignal.TripleRatchet DY.Libsignal.PQXDH
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement

/-! ## `NoBreak` Invariant -/

/-- True on quantum-break (`BrokenDH`, `BrokenKEM`) and dishonest `IdentityRegistered` events. -/
def isBreak : PQXDHEvent → Bool
  | .BrokenDH | .BrokenKEM => true
  | .IdentityRegistered _ _ _ false => true
  | _ => false

/-- No `BrokenDH`, `BrokenKEM`, or dishonest `IdentityRegistered` event is logged in `tr`. -/
def NoBreak (tr : ExecTrace) : Prop :=
  ∀ ev : PQXDHEvent, tr.EventLogged ev → isBreak ev = false

theorem noBreak_nil : NoBreak (Trace.nil : ExecTrace) := by
  rintro _ ⟨_, h⟩
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
    Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h

theorem noBreak_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace}
    (hok : NoBreak tr) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHEntry) = none) :
    NoBreak (tr.append e) :=
  fun ev h => hok ev ((eventLogged_append_other_iff hnone).1 h)

theorem noBreak_append_pqEv {tr : ExecTrace} (hok : NoBreak tr) (ev₀ : PQXDHEvent)
    (hev : isBreak ev₀ = false) : NoBreak (tr.append (PQEvE ev₀)) := by
  intro ev h
  rcases eventLogged_append_same_iff.1 h with h | rfl
  · exact hok ev h
  · exact hev

/-! ## Primitive `Preserves NoBreak` combinators -/

theorem NoBreak.preserves_storeLocalState_pq (me : Participant) (st : PQXDHState) :
    CompTrace.Preserves NoBreak (PersistentLocalState.storeLocalState me st) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact noBreak_append_other hok (PQStE me st) rfl

theorem NoBreak.preserves_logEvent_pq (ev : PQXDHEvent) (hev : isBreak ev = false) :
    CompTrace.Preserves NoBreak (ProtocolEvent.logEvent ev) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
    DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact noBreak_append_pqEv hok ev hev

theorem NoBreak.preserves_sendMessage (msg : Bytes) :
    CompTrace.Preserves NoBreak (Network.sendMessage msg) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact noBreak_append_other hok (NetE msg) rfl

theorem NoBreak.preserves_genRand (n : Nat) :
    CompTrace.Preserves NoBreak (Random.genRand n) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
    DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact noBreak_append_other hok (RndE n) rfl

theorem NoBreak.preserves_storeLocalState_tr (me : Participant) (st : TRState) :
    CompTrace.Preserves NoBreak (PersistentLocalState.storeLocalState me st) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact noBreak_append_other hok (TRStE me st) rfl

theorem NoBreak.preserves_logEvent_tr (ev : TREvent) :
    CompTrace.Preserves NoBreak (ProtocolEvent.logEvent ev) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
    DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact noBreak_append_other hok (TREvE ev) rfl

theorem NoBreak.preserves_logEvent_c (ev : ComposedEvent) :
    CompTrace.Preserves NoBreak (ProtocolEvent.logEvent ev) := by
  intro _ hok
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
    DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact noBreak_append_other hok (CEvE ev) rfl

/-! ## The non-break transitions preserve `NoBreak` -/

theorem NoBreak.preserves_getKey (p : Participant) (stateIdx : Nat) (kind : KeyKind) :
    CompTrace.Preserves NoBreak (DY.Libsignal.PQXDH.getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p stateIdx) fun _ => ?_
  exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _

theorem NoBreak.preserves_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : Bytes) (counter : UInt32)
    (rIdx childStateIdx : Nat) (st : TRState) :
    CompTrace.Preserves NoBreak
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt counter rIdx childStateIdx st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
  exact NoBreak.preserves_storeLocalState_tr me st

theorem NoBreak.preserves_logSkippedKeys (s : SessionInfo) (ratchetKey : Bytes)
    (rIdx sourceStateIdx : Nat) :
    ∀ (count : Nat) (ck : Bytes) (idx : UInt32),
      CompTrace.Preserves NoBreak
        (DY.Libsignal.TripleRatchet.logSkippedKeys s ratchetKey rIdx sourceStateIdx ck idx count)
  | 0, _, _ => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    exact CompTrace.Preserves.pure ()
  | count + 1, ck, idx => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
    exact NoBreak.preserves_logSkippedKeys s ratchetKey rIdx sourceStateIdx count (DY.Libsignal.TripleRatchet.kdfCk ck).1 (idx + 1)

theorem NoBreak.preserves_dhRatchetStep (st : TRState) (peerRatchetKey : Bytes) :
    CompTrace.Preserves NoBreak (DY.Libsignal.TripleRatchet.dhRatchetStep st peerRatchetKey) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_genRand 32) fun _ => ?_
  exact CompTrace.Preserves.pure _

theorem NoBreak.preserves_ensureReceiverChain (st : TRState) (peerRatchetKey : Bytes) :
    CompTrace.Preserves NoBreak (DY.Libsignal.TripleRatchet.ensureReceiverChain st peerRatchetKey) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact CompTrace.Preserves.pure _
  · refine CompTrace.Preserves.bind (NoBreak.preserves_dhRatchetStep st peerRatchetKey) fun ⟨_, _⟩ => ?_
    exact CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.failure

theorem NoBreak.preserves_registerIdentity (p : Participant) :
    CompTrace.Preserves NoBreak (registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_pq _ (by rfl)) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
  exact NoBreak.preserves_storeLocalState_pq p _

theorem NoBreak.preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    CompTrace.Preserves NoBreak (genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine CompTrace.Preserves.bind (NoBreak.preserves_getKey b idStateIdx .identity) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_pq _ (by rfl)) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_storeLocalState_pq b _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.pure _

theorem NoBreak.preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    CompTrace.Preserves NoBreak (genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine CompTrace.Preserves.bind (NoBreak.preserves_getKey b idStateIdx .identity) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_pq _ (by rfl)) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_storeLocalState_pq b _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.pure _

theorem NoBreak.preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) :
    CompTrace.Preserves NoBreak (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr hok
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hok
    (noBreak_append_other hok (RndE 32) rfl) ?_
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hok2 : NoBreak ((tr.append (RndE 32)).append (RndE 32)) :=
    noBreak_append_other (noBreak_append_other hok (RndE 32) rfl) (RndE 32) rfl
  refine (show CompTrace.Preserves NoBreak _ by
    refine CompTrace.Preserves.bind (NoBreak.preserves_genRand 32) fun _ => ?_
    refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
    refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
    refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
    refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_pq _ (by rfl)) fun _ => ?_
    refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
    refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_c _) fun _ => ?_
    exact NoBreak.preserves_storeLocalState_tr a _) _ hok2

theorem NoBreak.preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    CompTrace.Preserves NoBreak (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr hok
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hok ?_
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  refine (show CompTrace.Preserves NoBreak _ by
    refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveSignalMsg mh.msg) fun _ => ?_
    refine CompTrace.Preserves.bind (NoBreak.preserves_ensureReceiverChain _ _) fun ⟨_, _, _⟩ => ?_
    dsimp only
    split
    · split
      · refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
        refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
        refine CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
        split
        · refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
          refine CompTrace.Preserves.bind
            (NoBreak.preserves_logEvent_pq _ (by rfl)) fun _ => ?_
          refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
          refine CompTrace.Preserves.bind
            (NoBreak.preserves_logEvent_pq _ (by rfl)) fun _ => ?_
          split
          · refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
            refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
            refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_c _) fun _ => ?_
            refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
            refine CompTrace.Preserves.bind (NoBreak.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
            refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
            exact NoBreak.preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
          · refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_c _) fun _ => ?_
            refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
            refine CompTrace.Preserves.bind (NoBreak.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
            refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
            exact NoBreak.preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
        · refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
          refine CompTrace.Preserves.bind
            (NoBreak.preserves_logEvent_pq _ (by rfl)) fun _ => ?_
          split
          · refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
            refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
            refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_c _) fun _ => ?_
            refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
            refine CompTrace.Preserves.bind (NoBreak.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
            refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
            exact NoBreak.preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
          · refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_c _) fun _ => ?_
            refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
            refine CompTrace.Preserves.bind (NoBreak.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
            refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
            exact NoBreak.preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
      · exact CompTrace.Preserves.failure
    · exact CompTrace.Preserves.failure) _ hok

theorem NoBreak.preserves_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) :
    CompTrace.Preserves NoBreak
      (DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_genRand coinsLen) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_logMessageKeyAndStore me _ .sender _ _ _ _ _ _) fun _ => ?_
  exact NoBreak.preserves_sendMessage _

theorem NoBreak.preserves_messageEncryptAbort (me : Participant) (stH : Nat) :
    CompTrace.Preserves NoBreak
      (DY.Libsignal.TripleRatchet.messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_genRand 32) fun _ => ?_
  exact CompTrace.Preserves.failure

theorem NoBreak.preserves_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    CompTrace.Preserves NoBreak
      (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveSignalMsg msgH) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_ensureReceiverChain _ _) fun ⟨_, _, _⟩ => ?_
  dsimp only
  split
  · split
    · refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
      refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
      refine CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
      split
      · refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
        refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
        refine CompTrace.Preserves.bind (NoBreak.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
        refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
        exact NoBreak.preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
      · refine CompTrace.Preserves.bind (NoBreak.preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
        refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
        exact NoBreak.preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact CompTrace.Preserves.failure
  · exact CompTrace.Preserves.failure

theorem NoBreak.preserves_messageDecryptSkipped (me : Participant)
    (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    CompTrace.Preserves NoBreak
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveSignalMsg msgH) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getEntry evH) fun ⟨ev⟩ => ?_
  cases ev with
  | SkippedKeyStored _ _ _ _ _ _ =>
    dsimp only
    refine CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => ?_
    refine CompTrace.Preserves.bind (CompTrace.Preserves.guardTrace _) fun _ => ?_
    split
    · refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
      refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
      refine CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
      refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
      refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
      exact NoBreak.preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact CompTrace.Preserves.failure
  | _ => exact CompTrace.Preserves.failure

theorem NoBreak.preserves_exposeKey (me : Participant) (stH : Nat) (k : KeyComponent) :
    CompTrace.Preserves NoBreak
      (DY.Libsignal.TripleRatchet.exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  cases k with
  | ckr pk =>
    dsimp only
    split
    · exact CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ =>
        NoBreak.preserves_sendMessage _
    · exact CompTrace.Preserves.failure
  | _ =>
    exact CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ =>
      NoBreak.preserves_sendMessage _

theorem NoBreak.preserves_exposeSpqr (me : Participant) (stH : Nat) :
    CompTrace.Preserves NoBreak
      (DY.Libsignal.TripleRatchet.exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
  exact NoBreak.preserves_sendMessage _

theorem NoBreak.preserves_exposeSkipped (evH : Nat) :
    CompTrace.Preserves NoBreak
      (DY.Libsignal.TripleRatchet.exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getEntry evH) fun ⟨ev⟩ => ?_
  cases ev with
  | SkippedKeyStored _ _ _ _ _ _ =>
    dsimp only
    refine CompTrace.Preserves.bind (CompTrace.Preserves.guardTrace _) fun _ => ?_
    refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_tr _) fun _ => ?_
    exact NoBreak.preserves_sendMessage _
  | _ => exact CompTrace.Preserves.failure

theorem NoBreak.preserves_compromiseSPK (b : Participant) (stateIdx : Nat) :
    CompTrace.Preserves NoBreak (compromiseSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  refine CompTrace.Preserves.bind (NoBreak.preserves_getKey b stateIdx .signedPrekey) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_pq _ (by rfl)) fun _ => ?_
  exact NoBreak.preserves_sendMessage _

theorem NoBreak.preserves_compromisePQSPK (b : Participant) (stateIdx : Nat) :
    CompTrace.Preserves NoBreak (compromisePQSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  refine CompTrace.Preserves.bind (NoBreak.preserves_getKey b stateIdx .pqPrekey) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_pq _ (by rfl)) fun _ => ?_
  exact NoBreak.preserves_sendMessage _

theorem NoBreak.preserves_compromiseOPK (b : Participant) (stateIdx : Nat) :
    CompTrace.Preserves NoBreak (compromiseOPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  refine CompTrace.Preserves.bind (NoBreak.preserves_getKey b stateIdx .oneTimePrekey) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.guardTrace _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_pq _ (by rfl)) fun _ => ?_
  exact NoBreak.preserves_sendMessage _

theorem NoBreak.preserves_genOneTimePrekey (b : Participant) :
    CompTrace.Preserves NoBreak (genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine CompTrace.Preserves.bind (NoBreak.preserves_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_pq _ (by rfl)) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_storeLocalState_pq b _) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.pure _

theorem NoBreak.preserves_compromiseIK (p : Participant) (stateIdx : Nat) :
    CompTrace.Preserves NoBreak (compromiseIK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  refine CompTrace.Preserves.bind (NoBreak.preserves_getKey p stateIdx .identity) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_logEvent_pq _ (by rfl)) fun _ => ?_
  exact NoBreak.preserves_sendMessage _

/-! ## Unconstrained `Step` vs CLI-Allowed Steps -/

theorem not_noBreak_runTrace_breakDH (r : ProtocolSetup) : ¬ NoBreak (runTrace r [.breakDH]) := by
  intro h
  have htr : runTrace r [.breakDH] = (setupTrace r).append (PQEvE .BrokenDH) := by
    dsimp only [runTrace, runSteps, Step.next, Step.toInput, stepIn]
    rw [← (DY.ReachabilityConfig.HasStep.pf_step
      (config1 := PQXDH.breakDH.reachability) (config2 := reachability) ())]
    dsimp only [PQXDH.breakDH.reachability, PQXDH.breakDH]
    rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk]
    dsimp only
    rw [DY.Traceful.run_pure]
  have hlog : (runTrace r [.breakDH]).EventLogged PQXDHEvent.BrokenDH := by
    rw [htr]
    exact eventLogged_append_same_iff.2 (Or.inr rfl)
  exact Bool.noConfusion (h PQXDHEvent.BrokenDH hlog)

theorem not_noBreak_runTrace_breakKEM (r : ProtocolSetup) : ¬ NoBreak (runTrace r [.breakKEM]) := by
  intro h
  have htr : runTrace r [.breakKEM] = (setupTrace r).append (PQEvE .BrokenKEM) := by
    dsimp only [runTrace, runSteps, Step.next, Step.toInput, stepIn]
    rw [← (DY.ReachabilityConfig.HasStep.pf_step
      (config1 := PQXDH.breakKEM.reachability) (config2 := reachability) ())]
    dsimp only [PQXDH.breakKEM.reachability, PQXDH.breakKEM]
    rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk]
    dsimp only
    rw [DY.Traceful.run_pure]
  have hlog : (runTrace r [.breakKEM]).EventLogged PQXDHEvent.BrokenKEM := by
    rw [htr]
    exact eventLogged_append_same_iff.2 (Or.inr rfl)
  exact Bool.noConfusion (h PQXDHEvent.BrokenKEM hlog)

/-- Post-setup steps permitted by `MatchesEvents` on `BreakFree` CLI events: invisible, party, or
leak steps (excluding `.setup` and break/inversion/corrupt-identity steps). -/
def Step.CliAllowed (s : Step) : Prop :=
  s.cls = .invisible ∨ s.cls = .party ∨ s.IsLeak

theorem NoBreak.preserves_setupAct (a b : Participant) (withOpk : Bool) :
    CompTrace.Preserves NoBreak (Refinement.setupAct a b withOpk) := by
  unfold Refinement.setupAct
  refine CompTrace.Preserves.bind (NoBreak.preserves_registerIdentity a) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_registerIdentity b) fun hB => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_genSignedPrekey b hB) fun _ => ?_
  refine CompTrace.Preserves.bind (NoBreak.preserves_genPQPrekey b hB) fun _ => ?_
  cases withOpk
  · exact CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.bind (NoBreak.preserves_genOneTimePrekey b) fun _ =>
      CompTrace.Preserves.pure _

theorem noBreak_setupTrace (r : ProtocolSetup) : NoBreak (setupTrace r) :=
  NoBreak.preserves_setupAct r.alice r.bob r.withOpk Trace.nil noBreak_nil

theorem Step.preserves_noBreak (s : Step) (hs : s.cls = .setup ∨ Step.CliAllowed s) :
    CompTrace.Preserves NoBreak (reachability.step s.toInput).2 := by
  cases s with
  | network msg => exact NoBreak.preserves_sendMessage msg
  | registerIdentity p => exact NoBreak.preserves_registerIdentity p
  | genSignedPrekey b idStateIdx => exact NoBreak.preserves_genSignedPrekey b idStateIdx
  | genPQPrekey b idStateIdx => exact NoBreak.preserves_genPQPrekey b idStateIdx
  | genOneTimePrekey b => exact NoBreak.preserves_genOneTimePrekey b
  | aliceStart a b idStateIdx regIdxB h =>
    exact NoBreak.preserves_aliceStart a b idStateIdx regIdxB h
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx =>
    exact NoBreak.preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx
  | messageEncrypt me stateIdx coinsLen pqIdx =>
    exact NoBreak.preserves_messageEncrypt me stateIdx coinsLen pqIdx
  | messageEncryptAbort me stateIdx =>
    exact NoBreak.preserves_messageEncryptAbort me stateIdx
  | messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx =>
    exact NoBreak.preserves_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx
  | messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx =>
    exact NoBreak.preserves_messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx
  | exposeKey me stateIdx k => exact NoBreak.preserves_exposeKey me stateIdx k
  | exposeSpqr me stateIdx => exact NoBreak.preserves_exposeSpqr me stateIdx
  | exposeSkipped skIdx => exact NoBreak.preserves_exposeSkipped skIdx
  | compromiseIK p stateIdx => exact NoBreak.preserves_compromiseIK p stateIdx
  | compromiseSPK b stateIdx => exact NoBreak.preserves_compromiseSPK b stateIdx
  | compromisePQSPK b stateIdx => exact NoBreak.preserves_compromisePQSPK b stateIdx
  | compromiseOPK b stateIdx => exact NoBreak.preserves_compromiseOPK b stateIdx
  | registerCorruptIdentity _ _ | breakDH | breakKEM | invertDH _ | invertKEM _ =>
    simp [Step.CliAllowed, Step.cls, Step.IsLeak] at hs

theorem NoBreak.next {tr : ExecTrace} {s : Step} (hs : s.cls = .setup ∨ Step.CliAllowed s)
    (h : NoBreak tr) : NoBreak (s.next tr) :=
  Step.preserves_noBreak s hs tr h

/-! ## `NoBreak` holds on every CLI-explained run -/

theorem noBreak_runSteps : ∀ (ss : List Step) {tr : ExecTrace},
    (∀ s ∈ ss, s.cls = .setup ∨ Step.CliAllowed s) → NoBreak tr → NoBreak (runSteps ss tr)
  | [], _, _, h => h
  | s :: ss, _, hss, h =>
    noBreak_runSteps ss (fun x hx => hss x (List.mem_cons_of_mem s hx))
      (NoBreak.next (hss s List.mem_cons_self) h)

theorem noBreak_runTrace_of_allowed (r : ProtocolSetup) {ss : List Step}
    (hss : ∀ s ∈ ss, Step.CliAllowed s) : NoBreak (runTrace r ss) :=
  noBreak_runSteps ss (fun s hs => Or.inr (hss s hs)) (noBreak_setupTrace r)

theorem MatchesEventsAt.cliAllowed {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option DY.Libsignal.Composed.Refinement.BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hm : DY.Libsignal.Composed.Refinement.MatchesEventsAt interp r S g initIds tr ss evs vis)
    (hbf : BreakFree evs) :
    ∀ s ∈ ss, Step.CliAllowed s := by
  revert hbf
  induction hm with
  | nil hpre =>
    intro _ x hx
    exact Or.inl (hpre x hx)
  | run1 hpre hrun _ ih =>
    intro hbf x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact Or.inl (hpre x hx)
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inr (Or.inl hrun.1)
      · exact ih (breakFree_of_cons hbf) x hx
  | run0 hpre _ _ ih =>
    intro hbf x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact Or.inl (hpre x hx)
    · exact ih (breakFree_of_cons hbf) x hx
  | env hpre henv _ ih =>
    intro hbf
    cases ‹DY.Libsignal.HwEvents.EnvEvent› with
    | leak p k =>
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact Or.inl (hpre x hx)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inr (Or.inr henv.2.1)
        · exact ih (breakFree_of_cons hbf) x hx
    | breakDH | breakKEM | invertDH _ _ | invertKEM _ _ =>
      exact (hbf _ (List.mem_cons_self ..) trivial).elim
    | registerCorrupt _ _ => exact False.elim henv

theorem MatchesEvents.cliAllowed {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hm : MatchesEvents interp r S g tr ss evs vis) (hbf : BreakFree evs) :
    ∀ s ∈ ss, Step.CliAllowed s :=
  MatchesEventsAt.cliAllowed hm hbf

theorem noBreak_matchesEvents {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (htr : NoBreak tr) (hm : MatchesEvents interp r S g tr ss evs vis) (hbf : BreakFree evs) :
    NoBreak (runSteps ss tr) :=
  noBreak_runSteps ss (fun x hx => Or.inr (MatchesEvents.cliAllowed hm hbf x hx)) htr

/-- Every `Explains` witness of `BreakFree` CLI events satisfies `NoBreak`. -/
theorem noBreak_explains {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}
    (hex : Explains interp r S g ss vis evs) (hbf : BreakFree evs) : NoBreak (runTrace r ss) :=
  noBreak_runTrace_of_allowed r (MatchesEvents.cliAllowed hex.2.2.2 hbf)

/-! ## Which events never fire -/

theorem NoBreak.not_logged {tr : ExecTrace} (h : NoBreak tr) {ev : PQXDHEvent}
    (hb : isBreak ev = true) : ¬ tr.EventLogged ev := fun hl => by
  rw [h ev hl] at hb
  exact Bool.false_ne_true hb

theorem NoBreak.not_brokenDH {tr : ExecTrace} (h : NoBreak tr) :
    ¬ tr.EventLogged PQXDHEvent.BrokenDH :=
  h.not_logged rfl

theorem NoBreak.not_brokenDH_at {tr : ExecTrace} (h : NoBreak tr) (j : Nat) :
    ¬ tr.EventLoggedAt PQXDHEvent.BrokenDH j :=
  fun hj => h.not_brokenDH ⟨j, hj⟩

theorem NoBreak.not_brokenKEM {tr : ExecTrace} (h : NoBreak tr) :
    ¬ tr.EventLogged PQXDHEvent.BrokenKEM :=
  h.not_logged rfl

theorem NoBreak.not_corruptIdentity {tr : ExecTrace} (h : NoBreak tr) (p : Participant)
    (ikPk vk : Bytes) : ¬ tr.EventLogged (PQXDHEvent.IdentityRegistered p ikPk vk false) :=
  h.not_logged rfl

/-- A model trace logging `ev` with `isBreak ev = true` cannot equal `runTrace r ss` for any
`Explains` witness of `BreakFree` CLI events. -/
theorem ne_runTrace_of_break {tr : ExecTrace} {ev : PQXDHEvent} (hb : isBreak ev = true)
    (hl : tr.EventLogged ev) {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}
    (hex : Explains interp r S g ss vis evs) (hbf : BreakFree evs) : tr ≠ runTrace r ss := by
  rintro rfl
  exact (noBreak_explains hex hbf).not_logged hb hl

theorem not_explains_of_break {ev : PQXDHEvent} (hb : isBreak ev = true)
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}
    (hl : (runTrace r ss).EventLogged ev) (hbf : BreakFree evs) :
    ¬ Explains interp r S g ss vis evs :=
  fun hex => (noBreak_explains hex hbf).not_logged hb hl

/-! ## Compromise Predicates and Premises on `NoBreak` Traces -/

theorem NoBreak.thm7Excuse_iff {tr : ExecTrace} (h : NoBreak tr) {b : Participant}
    {ikB spk pqpk : Bytes} {i : Nat} :
    AliceHandshakeWasCompromised b ikB spk pqpk i tr ↔
      ∃ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j ∧
        (j < i ∨ (tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
          tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk))) := by
  constructor
  · rintro (⟨j, hj, hlt | ⟨hspk, hpq | hkem⟩⟩ | ⟨j, hj, _⟩)
    · exact ⟨j, hj, Or.inl hlt⟩
    · exact ⟨j, hj, Or.inr ⟨hspk, hpq⟩⟩
    · exact absurd hkem h.not_brokenKEM
    · exact absurd hj (h.not_brokenDH_at j)
  · rintro ⟨j, hj, hlt | ⟨hspk, hpq⟩⟩
    · exact Or.inl ⟨j, hj, Or.inl hlt⟩
    · exact Or.inl ⟨j, hj, Or.inr ⟨hspk, Or.inl hpq⟩⟩

theorem NoBreak.thm9Excuse_iff {tr : ExecTrace} (h : NoBreak tr) {b a : Participant}
    {ikB ikA spk pqpk : Bytes} {opk : Option Bytes} {i : Nat} :
    BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr ↔
      LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr ∨
      LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr ∨
      (tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
        tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
        OPKAbsentOrCompromised b opk i tr ∧
        tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)) := by
  constructor
  · rintro ((h0 | h1 | ⟨j, hj, _⟩) | ⟨hIK, hSPK, hOPK, hPQ | hKEM⟩ | ⟨hDH, _⟩)
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact absurd hj (h.not_brokenDH_at j)
    · exact Or.inr (Or.inr ⟨hIK, hSPK, hOPK, hPQ⟩)
    · exact absurd hKEM h.not_brokenKEM
    · exact absurd hDH h.not_brokenDH
  · rintro (h0 | h1 | ⟨hIK, hSPK, hOPK, hPQ⟩)
    · exact Or.inl (Or.inl h0)
    · exact Or.inl (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inl ⟨hIK, hSPK, hOPK, Or.inl hPQ⟩)

theorem NoBreak.thm8Excuse_iff {tr : ExecTrace} (h : NoBreak tr) {b a : Participant}
    {ikA spk : Bytes} {i : Nat} :
    HandshakeAuthWasCompromised b a ikA spk i tr ↔
      LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr ∨
      LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr := by
  constructor
  · rintro (h0 | h1 | ⟨j, hj, _⟩)
    · exact Or.inl h0
    · exact Or.inr h1
    · exact absurd hj (h.not_brokenDH_at j)
  · rintro (h0 | h1)
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)

theorem NoBreak.compromised_iff {tr : ExecTrace} (h : NoBreak tr)
    (k : Bytes) :
    Cheval.CompromisedKey tr k ↔
      (∃ s i, tr.EventLogged (TREvent.ExposedRK s k i)) ∨
      (∃ s i, tr.EventLogged (TREvent.ExposedDHs s k i)) ∨
      (∃ s ns i, tr.EventLogged (TREvent.ExposedCKs s k ns i)) ∨
      (∃ s nr i, tr.EventLogged (TREvent.ExposedCKr s k nr i)) ∨
      (∃ s n i, tr.EventLogged (TREvent.ExposedMK s k n i)) ∨
      Cheval.HandshakeRootCompromised tr k := by
  constructor
  · rintro (h1 | h2 | h3 | h4 | h5 | h6 | ⟨_, hb⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))
    · exact absurd hb h.not_brokenDH
  · rintro (h1 | h2 | h3 | h4 | h5 | h6)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))

theorem NoBreak.hndlPremise_iff {tr : ExecTrace} (h : NoBreak tr) {a b : Participant}
    {ikA ikB spk pqpk : Bytes} {i : Nat} :
    HNDLPremise a b ikA ikB spk pqpk i tr ↔
      ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
      ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
      ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) := by
  constructor
  · rintro ⟨_, _, hrest⟩
    exact hrest
  · rintro hrest
    exact ⟨fun j hj => absurd hj (h.not_brokenDH_at j), h.not_brokenKEM, hrest⟩

theorem NoBreak.fsPremise_of_hndlPremise {tr : ExecTrace} (h : NoBreak tr) {a b : Participant}
    {ikA ikB spk pqpk : Bytes} {i : Nat} (hp : HNDLPremise a b ikA ikB spk pqpk i tr) :
    FSPremise a b ikA ikB spk pqpk i tr := by
  obtain ⟨_, _, hIKA, hIKB, hSPK, hPQ⟩ := hp
  exact ⟨fun j hj => absurd ⟨j, hj⟩ hIKA, fun j hj => absurd ⟨j, hj⟩ hIKB, hSPK, hPQ,
    h.not_brokenDH, h.not_brokenKEM⟩

theorem NoBreak.hndlQuery_of_forwardSecrecyQuery {tr : ExecTrace} (h : NoBreak tr)
    {Knows : Bytes → Prop} (hfs : ForwardSecrecyQuery tr Knows) : HNDLQuery tr Knows :=
  fun a b ikA ikB spk pqpk opk keys i hcomp hp =>
    hfs a b ikA ikB spk pqpk opk keys i hcomp (h.fsPremise_of_hndlPremise hp)

/-! ## Consequences for `Explains`, `AllSecurityQueriesHoldOnHwTrace`, and `CollisionAfterExplainedPrefix` -/

section
variable {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
  {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}

theorem thm7Excuse_runTrace_iff (hex : Explains interp r S g ss vis evs)
    (hbf : BreakFree evs)
    {b : Participant} {ikB spk pqpk : Bytes} {i : Nat} :
    AliceHandshakeWasCompromised b ikB spk pqpk i (runTrace r ss) ↔
      ∃ j, (runTrace r ss).EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j ∧
        (j < i ∨ ((runTrace r ss).EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
          (runTrace r ss).EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk))) :=
  (noBreak_explains hex hbf).thm7Excuse_iff

theorem thm9Excuse_runTrace_iff (hex : Explains interp r S g ss vis evs)
    (hbf : BreakFree evs)
    {b a : Participant} {ikB ikA spk pqpk : Bytes} {opk : Option Bytes} {i : Nat} :
    BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i (runTrace r ss) ↔
      LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i (runTrace r ss) ∨
      LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i (runTrace r ss) ∨
      ((runTrace r ss).EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
        (runTrace r ss).EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
        OPKAbsentOrCompromised b opk i (runTrace r ss) ∧
        (runTrace r ss).EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)) :=
  (noBreak_explains hex hbf).thm9Excuse_iff

theorem thm8Excuse_runTrace_iff (hex : Explains interp r S g ss vis evs)
    (hbf : BreakFree evs)
    {b a : Participant} {ikA spk : Bytes} {i : Nat} :
    HandshakeAuthWasCompromised b a ikA spk i (runTrace r ss) ↔
      LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i (runTrace r ss) ∨
      LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i (runTrace r ss) :=
  (noBreak_explains hex hbf).thm8Excuse_iff

theorem compromised_runTrace_iff (hex : Explains interp r S g ss vis evs)
    (hbf : BreakFree evs)
    (k : Bytes) :
    Cheval.CompromisedKey (runTrace r ss) k ↔
      (∃ s i, (runTrace r ss).EventLogged (TREvent.ExposedRK s k i)) ∨
      (∃ s i, (runTrace r ss).EventLogged (TREvent.ExposedDHs s k i)) ∨
      (∃ s ns i, (runTrace r ss).EventLogged (TREvent.ExposedCKs s k ns i)) ∨
      (∃ s nr i, (runTrace r ss).EventLogged (TREvent.ExposedCKr s k nr i)) ∨
      (∃ s n i, (runTrace r ss).EventLogged (TREvent.ExposedMK s k n i)) ∨
      Cheval.HandshakeRootCompromised (runTrace r ss) k :=
  (noBreak_explains hex hbf).compromised_iff k

theorem hndlPremise_runTrace_iff (hex : Explains interp r S g ss vis evs)
    (hbf : BreakFree evs)
    {a b : Participant} {ikA ikB spk pqpk : Bytes} {i : Nat} :
    HNDLPremise a b ikA ikB spk pqpk i (runTrace r ss) ↔
      ¬ (runTrace r ss).EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
      ¬ (runTrace r ss).EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
      ¬ (runTrace r ss).EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      ¬ (runTrace r ss).EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) :=
  (noBreak_explains hex hbf).hndlPremise_iff

theorem fsPremise_of_hndlPremise_runTrace (hex : Explains interp r S g ss vis evs)
    (hbf : BreakFree evs)
    {a b : Participant} {ikA ikB spk pqpk : Bytes} {i : Nat}
    (hp : HNDLPremise a b ikA ikB spk pqpk i (runTrace r ss)) :
    FSPremise a b ikA ikB spk pqpk i (runTrace r ss) :=
  (noBreak_explains hex hbf).fsPremise_of_hndlPremise hp

theorem hndlQuery_of_forwardSecrecyQuery_runTrace (hex : Explains interp r S g ss vis evs)
    (hbf : BreakFree evs)
    {Knows : Bytes → Prop}
    (hfs : ForwardSecrecyQuery (runTrace r ss) Knows) : HNDLQuery (runTrace r ss) Knows :=
  (noBreak_explains hex hbf).hndlQuery_of_forwardSecrecyQuery hfs

/-- On `BreakFree` CLI traces, the first nine queries of `AllSecurityQueriesHoldOnHwTrace` already
imply `HNDLQuery`. -/
theorem asmSecure_iff_without_hndl (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (evs : List CliEvent) (hbf : BreakFree evs) :
    AllSecurityQueriesHoldOnHwTrace interp r S evs ↔
      ∀ g ss vis, Explains interp r S g ss vis evs →
        let tr := runTrace r ss
        let Knows := HwAttackerKnows r vis
        Cheval.FSQuery tr Knows ∧
        Cheval.PCSQuery tr Knows ∧
        AliceInitiatorSecrecyQuery tr Knows ∧
        BobResponderSecrecyQuery tr Knows ∧
        AuthenticationQuery tr ∧
        PeerAuthenticationQuery tr ∧
        ForwardSecrecyQuery tr Knows ∧
        KCIQuery tr ∧
        SessionIndependenceQuery tr Knows := by
  constructor
  · intro h g ss vis hex
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := h g ss vis hex
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · intro h g ss vis hex
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h g ss vis hex
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9,
      hndlQuery_of_forwardSecrecyQuery_runTrace hex hbf h7⟩

/-- Every `CollisionAfterExplainedPrefix` witness on `BreakFree` CLI events has an explained prefix
whose model trace satisfies `NoBreak`. -/
theorem exists_noBreak_prefix_of_collisionAtCli {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {evs : List CliEvent} (hcol : Cli.CollisionAfterExplainedPrefix interp r S evs)
    (hbf : BreakFree evs) :
    ∃ evs₁ ev evs₂ g ss vis,
      evs = evs₁ ++ .run ev :: evs₂ ∧
      Explains interp r S g ss vis evs₁ ∧
      NoBreak (runTrace r ss) := by
  obtain ⟨evs₁, ev, evs₂, g, ss, vis, heq, hex, _⟩ := hcol
  have hbf₁ : BreakFree evs₁ := (breakFree_append.mp (heq ▸ hbf)).1
  exact ⟨evs₁, ev, evs₂, g, ss, vis, heq, hex, noBreak_explains hex hbf₁⟩

end

end Symbolic.Proofs.Tests.Model.ExplanationTightness.CliCoverage
