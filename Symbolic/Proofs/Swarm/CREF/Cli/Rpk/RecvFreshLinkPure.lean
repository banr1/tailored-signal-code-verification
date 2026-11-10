/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Mathlib.Tactic.ToDual
public import Symbolic.Specifications.Model.Instance
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompTrDHS
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvFreshLinkPureA
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Skipped-Key Usage Bounds on Reachable Composed Traces

Proves that every `TREvent.SkippedKeyUsed` event on a reachable composed trace
refers to a strictly earlier trace index (`skippedKeyUsedB tr k = false` for `tr.length ≤ k`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR

cref_open
open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir KeyComponent setRecvChain recvChainFor
  createChain)
open DY.Libsignal.PQXDH (PQXDHEvent BundleHandles BobKeyHandles PreKeyMsgHandles serializedIk
  guardTrace)
open DY.Libsignal.TripleRatchet (TREvent TRState TRSignalMsg receiveSignalMsg verifyMacAndDecrypt
  ensureReceiverChain dhRatchetStep logSkippedKeys logMessageKeyAndStore messageEncrypt
  messageDecrypt messageDecryptSkipped exposeKey exposeSpqr exposeSkipped skippedKeyUsedB
  traceLength guardTrace)
open Symbolic.Swarm.CREF.TR.RecvDec
  (StEntry TREntry at?_append_of_lt at?_eq_none_of_le at?_append_non_entry
   logSkippedKeysTr logSkippedKeysTr_length at?_trEntry_logSkippedKeysTr_lt
   at?_trEntry_logSkippedKeysTr_add decTailTr decSkippedTr decRatchetPreTr trDhRatchetState)

section SkippedUsedLt

private theorem rf_proj_inj {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [DY.TraceEntryHas.inj_proj_eq]
private theorem rf_at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) :=
  at?_append_of_lt tr e hi
private theorem rf_at?_append_cases {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    {tr : ExecTrace} {e : E1} {x : E2} {i : Nat}
    (h : ((tr.append e).at? i : Option E2) = some x) :
    (i < tr.length ∧ (tr.at? i : Option E2) = some x) ∨
    (i = tr.length ∧
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = some x) := by
  have hlt : i < (tr.append e).length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := E2) (tr.append e) i; rw [h] at this; exact this
  have hlen : (tr.append e).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rcases (show i < tr.length ∨ i = tr.length by omega) with hi | rfl
  · rw [rf_at?_append_of_lt tr e hi] at h; exact .inl ⟨hi, h⟩
  · simp only [Trace.at?, hlt, ↓reduceDIte] at h
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte] at h; exact .inr ⟨rfl, h⟩
private theorem rf_eventLoggedAt_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    {ev : TREvent} {i : Nat} (h : (tr.append e).EventLoggedAt ev i) : tr.EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  rcases rf_at?_append_cases h with ⟨_, h⟩ | ⟨_, hp⟩
  · exact h
  · rw [hnone] at hp; cases hp
private theorem rf_eventLoggedAt_append_tr {tr : ExecTrace} {ev₀ ev : TREvent} {i : Nat}
    (h : (tr.append (⟨ev₀⟩ : TREntry)).EventLoggedAt ev i) :
    (i < tr.length ∧ tr.EventLoggedAt ev i) ∨ (i = tr.length ∧ ev₀ = ev) := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  rcases rf_at?_append_cases h with ⟨hi, h⟩ | ⟨heq_i, hp⟩
  · exact .inl ⟨hi, h⟩
  · rw [rf_proj_inj] at hp; injection hp with hp; injection hp with hp; exact .inr ⟨heq_i, hp⟩
private def RFPreserves (Inv : ExecTrace → Prop) {α : Type} (x : Traceful α) : Prop :=
  ∀ tr, Inv tr → Inv (x.run tr).2.val
private theorem RFPreserves.of_id {Inv : ExecTrace → Prop} {α : Type} {x : Traceful α}
    (hx : ∀ tr, (x.run tr).2.val = tr) : RFPreserves Inv x := by intro tr h; rw [hx]; exact h
private theorem RFPreserves.pure {Inv : ExecTrace → Prop} {α : Type} (a : α) :
    RFPreserves Inv (pure a : Traceful α) := RFPreserves.of_id fun _ => by simp only [Traceful.run_pure]
private theorem RFPreserves.failure {Inv : ExecTrace → Prop} {α : Type} :
    RFPreserves Inv (failure : Traceful α) := RFPreserves.of_id fun _ => by simp only [Traceful.run_failure]
private theorem RFPreserves.monadLiftErr {Inv : ExecTrace → Prop} {α : Type} (x : DY.Err α) :
    RFPreserves Inv (monadLift x : Traceful α) :=
  RFPreserves.of_id fun _ => by cases x <;> simp only [liftM, monadLift, MonadLift.monadLift, Traceful.run_mk]
private theorem RFPreserves.getEntry {Inv : ExecTrace → Prop} {E : Type} [ExecTraceTypes.Has E] (i : Nat) :
    RFPreserves Inv (DY.getEntry i : Traceful E) :=
  RFPreserves.of_id fun _ => by simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
private theorem RFPreserves.traceLength {Inv : ExecTrace → Prop} :
    RFPreserves Inv traceLength :=
  RFPreserves.of_id fun _ => by unfold DY.Libsignal.TripleRatchet.traceLength; simp only [Traceful.run_mk]
private theorem RFPreserves.guardP {Inv : ExecTrace → Prop} (p : Prop) [Decidable p] :
    RFPreserves Inv (_root_.guard p : Traceful Unit) := by
  unfold _root_.guard; split
  · exact RFPreserves.pure _
  · exact RFPreserves.failure
private theorem RFPreserves.guardTrace {Inv : ExecTrace → Prop} (p : ExecTrace → Bool) :
    RFPreserves Inv (guardTrace p) :=
  RFPreserves.of_id fun _ => by unfold DY.Libsignal.TripleRatchet.guardTrace; simp only [Traceful.run_mk]
private theorem RFPreserves.requireTracePredicate {Inv : ExecTrace → Prop} (p : ExecTrace → Bool) :
    RFPreserves Inv (DY.Libsignal.PQXDH.guardTrace p) :=
  RFPreserves.of_id fun _ => by
    unfold DY.Libsignal.PQXDH.guardTrace; simp only [Traceful.run_mk]
private theorem RFPreserves.bind {Inv : ExecTrace → Prop} {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : RFPreserves Inv x) (hf : ∀ a, RFPreserves Inv (f a)) : RFPreserves Inv (x >>= f) := by
  intro tr hInv; rw [Traceful.run_bind]
  rcases h : x.run tr with ⟨o, trMid, _⟩
  have hMid : Inv trMid := by have := hx tr hInv; rw [h] at this; exact this
  cases o with
  | none => exact hMid
  | some a => exact hf a trMid hMid
private theorem RFPreserves.receiveMessage {Inv : ExecTrace → Prop} (msgH : Nat) :
    RFPreserves Inv (Network.receiveMessage msgH) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact RFPreserves.bind (RFPreserves.getEntry _) fun _ => RFPreserves.pure _
private theorem RFPreserves.getLocalState {Inv : ExecTrace → Prop} (me : Participant) (stH : Nat) :
    RFPreserves Inv (PersistentLocalState.getLocalState me stH : Traceful TRState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine RFPreserves.bind (RFPreserves.bind (RFPreserves.getEntry _) fun _ => RFPreserves.pure _) fun _ => ?_
  exact RFPreserves.bind (RFPreserves.guardP _) fun _ => RFPreserves.pure _
private theorem RFPreserves.receiveSignalMsg {Inv : ExecTrace → Prop} (msgH : Nat) :
    RFPreserves Inv (DY.Libsignal.TripleRatchet.receiveSignalMsg msgH) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine RFPreserves.bind (RFPreserves.receiveMessage _) fun _ => ?_
  split
  · exact RFPreserves.bind (RFPreserves.guardP _) fun _ => RFPreserves.pure _
  · exact RFPreserves.failure
private theorem RFPreserves.verifyMacAndDecrypt {Inv : ExecTrace → Prop}
    (st : TRState) (msg : TRSignalMsg) (pqSalt seed : DY.Bytes) :
    RFPreserves Inv (DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  exact RFPreserves.bind (RFPreserves.guardP _) fun _ => RFPreserves.monadLiftErr _
private theorem RFPreserves.and {P Q : ExecTrace → Prop} {α : Type} {x : Traceful α}
    (hP : RFPreserves P x) (hQ : RFPreserves Q x) : RFPreserves (fun tr => P tr ∧ Q tr) x :=
  fun tr ⟨hp, hq⟩ => ⟨hP tr hp, hQ tr hq⟩
private theorem RFPreserves.lt_length (k : Nat) {α : Type} (x : Traceful α) :
    RFPreserves (fun t => k < t.length) x :=
  fun tr hk => Nat.lt_of_lt_of_le hk (Trace.length_le _ _ (x.run tr).2.property)
private theorem RFPreserves.bind_getEntry_lt {Inv : ExecTrace → Prop} {α : Type}
    (evH : Nat) {f : TREntry → Traceful α}
    (hf : ∀ e, RFPreserves (fun tr => Inv tr ∧ evH < tr.length) (f e)) :
    RFPreserves Inv ((DY.getEntry evH : Traceful TREntry) >>= f) := by
  intro tr hInv
  have hrun : (DY.getEntry evH : Traceful TREntry).run tr = (tr.at? evH, ⟨tr, Trace.le_refl tr⟩) := by
    simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  rw [Traceful.run_bind, hrun]
  rcases he : (tr.at? evH : Option TREntry) with _ | e
  · exact hInv
  · dsimp only
    have hlt : evH < tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := TREntry) tr evH
      rw [he] at this; exact this
    exact (hf e tr ⟨hInv, hlt⟩).1
def TRSkippedUsedLt (tr : ExecTrace) : Prop :=
  ∀ s k i, tr.EventLoggedAt (TREvent.SkippedKeyUsed s k) i → k < tr.length
private theorem TRSkippedUsedLt.append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (h : TRSkippedUsedLt tr) : TRSkippedUsedLt (tr.append e) := by
  intro s k i hi; have hk := h s k i (rf_eventLoggedAt_append_other hnone hi)
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
private theorem TRSkippedUsedLt.inertOnNonTR :
    Symbolic.Swarm.COMPOSED.CompRatchet.TrDHS.InertOnNonTR TRSkippedUsedLt where
  append_net _ _ h := h.append_other rfl
  append_rnd _ _ h := h.append_other rfl
  append_pqxEv _ _ h := h.append_other rfl
  append_cEv _ _ h := h.append_other rfl
  append_pqxSt _ _ _ h := h.append_other rfl
private theorem RFPreserves.su_logEvent (ev : TREvent) (hne : ∀ s h, ev ≠ .SkippedKeyUsed s h) :
    RFPreserves TRSkippedUsedLt (DY.ProtocolEvent.logEvent ev) := by
  intro tr h s k i hi
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure] at hi ⊢
  rcases rf_eventLoggedAt_append_tr hi with ⟨_, hi⟩ | ⟨_, heq⟩
  · have hk := h s k i hi
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  · exact absurd heq (hne s k)
private theorem TRSkippedUsedLt.append_used {tr : ExecTrace} {s₀ : SessionInfo} {evH : Nat}
    (h : TRSkippedUsedLt tr) (hlt : evH < tr.length) :
    TRSkippedUsedLt (tr.append (⟨.SkippedKeyUsed s₀ evH⟩ : TREntry)) := by
  intro s k i hi; rcases rf_eventLoggedAt_append_tr hi with ⟨_, hi⟩ | ⟨_, heq⟩
  · have hk := h s k i hi
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  · injection heq with _ hk_eq; subst hk_eq
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
private theorem RFPreserves.su_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat),
      RFPreserves TRSkippedUsedLt (logSkippedKeys s pk rIdx sourceStateIdx ck n k)
  | _, _, 0 => RFPreserves.pure _
  | ck, n, k + 1 => by
    unfold logSkippedKeys
    exact RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
      RFPreserves.su_logSkippedKeys s pk rIdx sourceStateIdx _ _ k
private theorem RFPreserves.su_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx parentStateIdx : Nat)
    (st : TRState) :
    RFPreserves TRSkippedUsedLt
      (logMessageKeyAndStore me s dir seed pqSalt n rIdx parentStateIdx st) := by
  unfold logMessageKeyAndStore
  refine RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
    fun _ h => by
      simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
        Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
      exact TRSkippedUsedLt.append_other rfl h
private theorem RFPreserves.su_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    RFPreserves TRSkippedUsedLt (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; split
  · exact RFPreserves.pure _
  · exact RFPreserves.bind (RFPreserves.bind (RFPreserves.guardP _) fun _ =>
      RFPreserves.bind (TRSkippedUsedLt.inertOnNonTR.preserves_genRand _) fun _ =>
      RFPreserves.pure _) fun _ => RFPreserves.pure _
  · exact RFPreserves.failure

private theorem RFPreserves.su_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) :
    RFPreserves TRSkippedUsedLt (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr₀ hInv₀
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TRSkippedUsedLt.inertOnNonTR.bind_aliceHandshake a b idStateIdx regIdxB bh tr₀ hInv₀ fun o => ?_
  have hTail : RFPreserves TRSkippedUsedLt (do
      let dhsA ← Random.genRand 32
      let (rkA, cksA) := createChain o.keys.rk o.spk dhsA
      let stA : TRState := {
        peer := b, myIk := serializedIk o.ikA, peerIk := serializedIk o.ikB,
        rk := rkA, dhs := dhsA, cks := cksA, ns := 0, pn := 0,
        sid := Concat.concat (DY.DiffieHellman.dhPk dhsA) o.keys.rk, initiator := true, rIdx := 1,
        recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
        spqr := Spqr.spqrInit o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B }
      let _ ← Network.sendMessage o.ek
      let _ ← Network.sendMessage o.ct
      let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
      DY.ProtocolEvent.logEvent (PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys)
      DY.ProtocolEvent.logEvent (TREvent.InitSession a b (DY.DiffieHellman.dhPk dhsA) o.spk)
      DY.ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (stA.sessionInfo a) doneIdx)
      PersistentLocalState.storeLocalState a stA) :=
    RFPreserves.bind (TRSkippedUsedLt.inertOnNonTR.preserves_genRand _) fun _ =>
    RFPreserves.bind (TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _) fun _ =>
    RFPreserves.bind (TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _) fun _ =>
    RFPreserves.bind RFPreserves.traceLength fun _ =>
    RFPreserves.bind (TRSkippedUsedLt.inertOnNonTR.preserves_logPQX _) fun _ =>
    RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ hc; cases hc)) fun _ =>
    RFPreserves.bind (fun _ h => by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
      exact TRSkippedUsedLt.inertOnNonTR.append_cEv _ _ h) fun _ =>
    fun _ h => by
      simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
        Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
      exact TRSkippedUsedLt.append_other rfl h
  exact hTail _ ((hInv₀.append_other rfl).append_other rfl)

private theorem RFPreserves.su_bobStart (b a : Participant)
    (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    RFPreserves TRSkippedUsedLt
      (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr₀ hInv₀
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine Symbolic.Swarm.COMPOSED.CompRatchet.TrDHS.InertOnNonTR.bind_bobHandshake
    b a kh regIdxA mh.ek mh.ct tr₀ hInv₀ fun o => ?_
  revert tr₀ hInv₀
  refine RFPreserves.bind (RFPreserves.receiveSignalMsg _) fun msg =>
    RFPreserves.bind (RFPreserves.su_ensureReceiverChain _ _) fun ⟨st, c, ratcheted⟩ => ?_
  dsimp only; split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      refine RFPreserves.bind (TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _) fun _ =>
        RFPreserves.bind (RFPreserves.receiveMessage _) fun pqSalt =>
        RFPreserves.bind (RFPreserves.verifyMacAndDecrypt _ _ _ _) fun pt => ?_
      have hTail (opkOpt : Option DY.Bytes) :
          RFPreserves TRSkippedUsedLt (do
            let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
            DY.ProtocolEvent.logEvent (PQXDHEvent.BobDone b a o.ikB o.ikA o.spk o.pqpk opkOpt o.ek o.ct o.keys)
            if ratcheted then
              DY.ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DY.DiffieHellman.dhPk st.dhs))
              DY.ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
            DY.ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
            let skipped := msg.counter.toNat - c.index.toNat
            let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
            logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
            DY.ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter pt)
            logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
              msg.counter c.rIdx childIdx
              { st with recv := setRecvChain st.recv c', spqr := spqr' }) := by
        refine RFPreserves.bind RFPreserves.traceLength fun doneIdx =>
          RFPreserves.bind (TRSkippedUsedLt.inertOnNonTR.preserves_logPQX _) fun _ => ?_
        have hAfterRat : RFPreserves TRSkippedUsedLt (do
            DY.ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
            let skipped := msg.counter.toNat - c.index.toNat
            let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
            logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
            DY.ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter pt)
            logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
              msg.counter c.rIdx childIdx
              { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
          RFPreserves.bind (fun _ h => by
            simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
              Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
            exact TRSkippedUsedLt.inertOnNonTR.append_cEv _ _ h) fun _ =>
          RFPreserves.bind RFPreserves.traceLength fun _ =>
          RFPreserves.bind (RFPreserves.su_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
          RFPreserves.su_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
        cases ratcheted
        · exact hAfterRat
        · exact RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
            RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
            hAfterRat
      cases o.opk with
      | none => exact hTail none
      | some opk =>
        dsimp only
        exact RFPreserves.bind (RFPreserves.requireTracePredicate _) fun _ =>
          RFPreserves.bind (TRSkippedUsedLt.inertOnNonTR.preserves_logPQX _) fun _ =>
          hTail (some opk)
    · exact RFPreserves.failure
  · exact RFPreserves.failure

private theorem RFPreserves.su_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) :
    RFPreserves TRSkippedUsedLt (messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine RFPreserves.bind (RFPreserves.getLocalState _ _) fun _ =>
    RFPreserves.bind (RFPreserves.guardP _) fun _ =>
    RFPreserves.bind (TRSkippedUsedLt.inertOnNonTR.preserves_genRand _) fun _ =>
    RFPreserves.bind (TRSkippedUsedLt.inertOnNonTR.preserves_genRand _) fun _ =>
    RFPreserves.bind (TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _) fun _ =>
    RFPreserves.bind (RFPreserves.receiveMessage _) fun _ =>
    RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
    RFPreserves.bind (RFPreserves.su_logMessageKeyAndStore _ _ _ _ _ _ _ _ _) fun _ =>
    TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _

private theorem RFPreserves.su_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    RFPreserves TRSkippedUsedLt (messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine RFPreserves.bind (RFPreserves.getLocalState _ _) fun _ =>
    RFPreserves.bind (RFPreserves.receiveSignalMsg _) fun _ =>
    RFPreserves.bind (RFPreserves.su_ensureReceiverChain _ _) fun ⟨st, c, ratcheted⟩ => ?_
  dsimp only; split
  · split
    · refine RFPreserves.bind (TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _) fun _ =>
        RFPreserves.bind (RFPreserves.receiveMessage _) fun _ =>
        RFPreserves.bind (RFPreserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
      split
      · refine RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
          RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
          RFPreserves.bind (RFPreserves.su_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
          RFPreserves.su_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
      · refine RFPreserves.bind (RFPreserves.su_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
          RFPreserves.su_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
    · exact RFPreserves.failure
  · exact RFPreserves.failure

private theorem RFPreserves.su_messageDecryptSkipped (me : Participant)
    (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    RFPreserves TRSkippedUsedLt (messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine RFPreserves.bind (RFPreserves.getLocalState _ _) fun st =>
    RFPreserves.bind (RFPreserves.receiveSignalMsg _) fun msg =>
    RFPreserves.bind_getEntry_lt evH fun ⟨ev⟩ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
    dsimp only
    refine RFPreserves.bind
      (RFPreserves.and (RFPreserves.guardP _) (RFPreserves.lt_length evH _)) fun _ =>
      RFPreserves.bind
        (RFPreserves.and (RFPreserves.guardTrace _) (RFPreserves.lt_length evH _)) fun _ => ?_
    split
    · refine RFPreserves.bind
        (RFPreserves.and (TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _)
          (RFPreserves.lt_length evH _)) fun _ =>
        RFPreserves.bind
          (RFPreserves.and (RFPreserves.receiveMessage _) (RFPreserves.lt_length evH _)) fun _ =>
        RFPreserves.bind
          (RFPreserves.and (RFPreserves.verifyMacAndDecrypt _ _ _ _)
            (RFPreserves.lt_length evH _)) fun _ =>
        RFPreserves.bind
          (fun t ⟨hInv, hlt⟩ => by
            simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
              Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
            exact ⟨hInv.append_used hlt, by
              simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega⟩) fun _ =>
        RFPreserves.bind
          (RFPreserves.and (RFPreserves.su_logEvent _ (by intro _ _ h; cases h))
            (RFPreserves.lt_length evH _)) fun _ =>
        RFPreserves.and (RFPreserves.su_logMessageKeyAndStore _ _ _ _ _ _ _ _ _)
          (RFPreserves.lt_length evH _)
    · exact RFPreserves.and RFPreserves.failure (RFPreserves.lt_length evH _)
  | _ => exact RFPreserves.and RFPreserves.failure (RFPreserves.lt_length evH _)

private theorem RFPreserves.su_exposeKey (me : Participant) (stH : Nat) (k : KeyComponent) :
    RFPreserves TRSkippedUsedLt (exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine RFPreserves.bind (RFPreserves.getLocalState _ _) fun _ => ?_
  split
  · exact RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
      TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _
  · exact RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
      TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _
  · exact RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
      TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _
  · split
    · exact RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
         TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _
    · exact RFPreserves.failure

private theorem RFPreserves.su_exposeSpqr (me : Participant) (stH : Nat) :
    RFPreserves TRSkippedUsedLt (exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  exact RFPreserves.bind (RFPreserves.getLocalState _ _) fun _ =>
    RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
    TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _

private theorem RFPreserves.su_exposeSkipped (evH : Nat) :
    RFPreserves TRSkippedUsedLt (exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine RFPreserves.bind (RFPreserves.getEntry _) fun _ => ?_
  split
  · refine RFPreserves.bind (RFPreserves.guardTrace _) fun _ =>
      RFPreserves.bind (RFPreserves.su_logEvent _ (by intro _ _ h; cases h)) fun _ =>
      TRSkippedUsedLt.inertOnNonTR.preserves_sendMessage _
  · exact RFPreserves.failure

theorem trSkippedUsedLt_reachable {tr : ExecTrace} (h : tr.Reachable reachability) :
    TRSkippedUsedLt tr :=
  TRSkippedUsedLt.inertOnNonTR.reachable_induction
    (fun _ _ _ hi => by
      simp [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?,
        Symbolic.DYBridge.DY.Trace.length_eq_1] at hi)
    RFPreserves.su_aliceStart
    RFPreserves.su_bobStart
    RFPreserves.su_messageEncrypt
    RFPreserves.su_messageDecrypt
    RFPreserves.su_messageDecryptSkipped
    RFPreserves.su_exposeKey
    RFPreserves.su_exposeSpqr
    RFPreserves.su_exposeSkipped
    h

/-- On any reachable composed trace `tr`, `skippedKeyUsedB tr k = false` for all `k` with `tr.length ≤ k`. -/
theorem skippedKeyUsedB_of_ge_length_tr {tr : ExecTrace} (hreach : tr.Reachable reachability)
    {k : Nat} (hle : tr.length ≤ k) : skippedKeyUsedB tr k = false := by
  have hsu := trSkippedUsedLt_reachable hreach
  rcases hb : skippedKeyUsedB tr k with _ | _
  · rfl
  · exfalso; unfold skippedKeyUsedB at hb
    obtain ⟨ev, i, hev, hq⟩ := exists_eventLoggedAt_of_someEventOnTraceB_tr hb
    cases ev with
    | SkippedKeyUsed s k' =>
      simp only [beq_iff_eq] at hq; subst hq; have hlt := hsu s k' i hev; omega
    | _ => simp at hq

end SkippedUsedLt

end Symbolic.Swarm.CREF.CliPure.TR
