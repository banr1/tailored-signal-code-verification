/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.QuietTransferPure
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvRecv
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import DY.Actions.Network
import DY.Actions.PersistentGlobalState
import DY.Actions.PersistentLocalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Trace.Basic
import DY.Trace.Manipulation
import DY.Trace.Monad
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.Monad

/-!
# Promoted Prekey Receive Trace Frame

Defines the trace-extension predicate `promRcvFrame` for a promoted prekey receive step of `p`
and proves `RoleSnapshots` preservation (`prom_roleSnapshots_of_oneMove_recv`) and single-move
frame establishment (`prom_rcv_next_move`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.RecvPrekeyProm

cref_open
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.COMPOSED
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir)
open DY.Libsignal.TripleRatchet (TRState TREvent
  dhRatchetStep ensureReceiverChain logSkippedKeys logMessageKeyAndStore
  receiveSignalMsg verifyMacAndDecrypt traceLength guardTrace)

theorem prom_roleSnapshots_of_oneMove_recv {r : ProtocolSetup} {p : Participant}
    {blk : List MachineEvent} {tr : ExecTrace} {δ : List Move}
    (hone : OneMove (RecvStep p blk) tr δ)
    (h0 : RoleSnapshots r tr) :
    RoleSnapshots r (runMoves δ tr).1 :=
  roleSnapshots_of_oneMove (fun _ _ hm h => roleSnapshots_of_recvMove hm.2.1 h) hone h0

def promRcvEv (p : Participant) (tr₀ : ExecTrace) : TREvent → Prop
  | .SkippedKeyUsed s k =>
    s.me = p ∧ ∃ pk n seed rIdx srcIdx,
      (tr₀.at? k : Option CompTrace.TREntry) =
        some ⟨.SkippedKeyStored s pk n seed rIdx srcIdx⟩
  | .MessageKey s _ _ _ _ _ _ => s.me = p
  | .SkippedKeyStored s _ _ _ _ _ => s.me = p
  | _ => True

def promRcvFrame (p : Participant) (tr₀ tr : ExecTrace) : Prop :=
  tr₀ ≤ tr ∧ ∀ i, tr₀.length ≤ i →
    (∀ e : CompTrace.TRStEntry, (tr.at? i : Option CompTrace.TRStEntry) = some e →
      e.st.participant = p) ∧
    (∀ e : CompTrace.TREntry, (tr.at? i : Option CompTrace.TREntry) = some e →
      promRcvEv p tr₀ e.ev) ∧
    Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.NonSessionPQAt tr i

theorem promRcvFrame_refl (p : Participant) (tr : ExecTrace) : promRcvFrame p tr tr := by
  refine ⟨DY.Trace.le_refl tr, fun _ hi => ⟨fun _ he => ?_, fun _ he => ?_, ?_⟩⟩
  · rw [Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.at?_none_of_ge hi] at he; cases he
  · rw [Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.at?_none_of_ge hi] at he; cases he
  · exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_of_eq_none (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.at?_none_of_ge hi)

theorem promRcvFrame_of_quietExt (p : Participant) {tr₀ tr : ExecTrace}
    (hq : Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QuietExt tr₀ tr) : promRcvFrame p tr₀ tr := by
  refine ⟨hq.1, fun i hi => ?_⟩
  by_cases hlt : i < tr.length
  · obtain ⟨hst, hpq, htr, _⟩ := hq.2 i hi hlt
    exact ⟨fun _ he => (by rw [hst] at he; cases he),
      fun _ he => (by rw [htr] at he; cases he), hpq⟩
  · have hge : tr.length ≤ i := by omega
    exact ⟨fun _ he => (by rw [Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.at?_none_of_ge hge] at he; cases he),
      fun _ he => (by rw [Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.at?_none_of_ge hge] at he; cases he),
      Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_of_eq_none (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.at?_none_of_ge hge)⟩

theorem promRcvFrame_append {E : Type} [DY.ExecTraceTypes.Has E] {p : Participant}
    {tr₀ tr : ExecTrace} {x : E}
    (hst : ∀ e : CompTrace.TRStEntry,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
        Option CompTrace.TRStEntry) = some e → e.st.participant = p)
    (hev : ∀ e : CompTrace.TREntry,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
        Option CompTrace.TREntry) = some e → promRcvEv p tr₀ e.ev)
    (hpq : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QPqE) = none)
    (h : promRcvFrame p tr₀ tr) : promRcvFrame p tr₀ (tr.append x) := by
  refine ⟨DY.Trace.le_trans _ _ _ h.1 (DY.Trace.append_le tr x), fun i hi =>
    ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_⟩⟩
  · rcases CompTrace.at?_append_cases he with ⟨_, he'⟩ | ⟨_, hp⟩
    · exact (h.2 i hi).1 e he'
    · exact hst e hp
  · rcases CompTrace.at?_append_cases he with ⟨_, he'⟩ | ⟨_, hp⟩
    · exact (h.2 i hi).2.1 e he'
    · exact hev e hp
  · rcases CompTrace.at?_append_cases he with ⟨_, he'⟩ | ⟨_, hp⟩
    · exact (h.2 i hi).2.2 e he'
    · rw [hpq] at hp; cases hp

theorem promRcvFrame_append_other {E : Type} [DY.ExecTraceTypes.Has E] {p : Participant}
    {tr₀ tr : ExecTrace} {x : E}
    (h1 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option CompTrace.TRStEntry) = none)
    (h2 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option CompTrace.TREntry) = none)
    (h3 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QPqE) = none)
    (h : promRcvFrame p tr₀ tr) : promRcvFrame p tr₀ (tr.append x) :=
  promRcvFrame_append (fun _ hp => by rw [h1] at hp; cases hp)
    (fun _ hp => by rw [h2] at hp; cases hp) h3 h

private structure promRcvFx (Inv : ExecTrace → Prop) (p : Participant) (tr₀ : ExecTrace) : Prop where
  send : ∀ m : DY.Bytes, CompTrace.Preserves Inv (DY.Network.sendMessage m)
  rand : ∀ k : Nat, CompTrace.Preserves Inv (DY.Random.genRand k)
  tr : ∀ ev : TREvent, promRcvEv p tr₀ ev → CompTrace.Preserves Inv (DY.ProtocolEvent.logEvent ev)
  store : ∀ st : TRState, CompTrace.Preserves Inv (DY.PersistentLocalState.storeLocalState p st)

private theorem promRcvFrameFx (p : Participant) (tr₀ : ExecTrace) :
    promRcvFx (promRcvFrame p tr₀) p tr₀ where
  send _ := by
    intro _ h
    rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      DY.Traceful.run_mk]
    exact promRcvFrame_append_other rfl rfl rfl h
  rand _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact promRcvFrame_append_other rfl rfl rfl h
  tr _ hev := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact promRcvFrame_append (fun _ hp => by cases hp)
      (fun _ hp => by rw [CompTrace.proj_inj_eq] at hp; cases hp; exact hev) rfl h
  store _ := by
    intro _ h
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact promRcvFrame_append
      (fun _ hp => by rw [CompTrace.proj_inj_eq] at hp; cases hp; rfl) (fun _ hp => by cases hp) rfl h

private theorem prom_rcv_logSkippedKeys {Inv : ExecTrace → Prop} {p : Participant} {tr₀ : ExecTrace}
    (fx : promRcvFx Inv p tr₀) (s : SessionInfo) (hs : s.me = p) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (idx : UInt32) (k : Nat),
      CompTrace.Preserves Inv (logSkippedKeys s pk rIdx src ck idx k)
  | _, _, 0 => CompTrace.Preserves.pure ()
  | ck, idx, k + 1 => by
    unfold logSkippedKeys
    exact CompTrace.Preserves.bind (fx.tr _ (by exact hs)) fun _ =>
      prom_rcv_logSkippedKeys fx s hs pk rIdx src _ _ k

private theorem prom_rcv_logMKStore {Inv : ExecTrace → Prop} {p : Participant} {tr₀ : ExecTrace}
    (fx : promRcvFx Inv p tr₀) (s : SessionInfo) (hs : s.me = p) (dir : KeyDir)
    (seed pqSalt : DY.Bytes) (k : UInt32) (rIdx par : Nat) (st : TRState) :
    CompTrace.Preserves Inv (logMessageKeyAndStore p s dir seed pqSalt k rIdx par st) := by
  unfold logMessageKeyAndStore
  exact CompTrace.Preserves.bind (fx.tr _ (by exact hs)) fun _ => fx.store st

private theorem prom_rcv_dhRatchetStep {Inv : ExecTrace → Prop} {p : Participant} {tr₀ : ExecTrace}
    (fx : promRcvFx Inv p tr₀) (st : TRState) (pk : DY.Bytes) :
    CompTrace.Preserves Inv (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ =>
    CompTrace.Preserves.bind (fx.rand 32) fun _ => CompTrace.Preserves.pure _

private theorem prom_rcv_ensureReceiverChain {Inv : ExecTrace → Prop} {p : Participant}
    {tr₀ : ExecTrace} (fx : promRcvFx Inv p tr₀) (st₀ : TRState) (pk : DY.Bytes) :
    CompTrace.Preserves Inv (ensureReceiverChain st₀ pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.bind (prom_rcv_dhRatchetStep fx st₀ pk) fun _ =>
      CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.failure

private theorem prom_rcv_messageDecrypt {Inv : ExecTrace → Prop} {p : Participant} {tr₀ : ExecTrace}
    (fx : promRcvFx Inv p tr₀) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    CompTrace.Preserves Inv
      (DY.Libsignal.TripleRatchet.messageDecrypt p stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr p stateIdx) fun st =>
    CompTrace.Preserves.bind (CompTrace.Preserves.receiveSignalMsg msgIdx) fun msg =>
    CompTrace.Preserves.bind (prom_rcv_ensureReceiverChain fx st msg.ratchetKey) fun r => ?_
  rcases r with ⟨st', _, _⟩
  dsimp only
  split
  · next seed _ _ =>
    split
    · next _ key _ =>
      refine CompTrace.Preserves.bind (fx.send key) fun _ =>
        CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun pqSalt =>
        CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt st' msg pqSalt seed)
          fun _ => ?_
      try dsimp only
      split
      · exact CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
          CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
          CompTrace.Preserves.bind (prom_rcv_logSkippedKeys fx (st'.sessionInfo p) rfl _ _ _ _ _ _) fun _ =>
          CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
          prom_rcv_logMKStore fx (st'.sessionInfo p) rfl _ _ _ _ _ _ _
      · exact CompTrace.Preserves.bind (prom_rcv_logSkippedKeys fx (st'.sessionInfo p) rfl _ _ _ _ _ _) fun _ =>
          CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
          prom_rcv_logMKStore fx (st'.sessionInfo p) rfl _ _ _ _ _ _ _
    · exact CompTrace.Preserves.failure
  · exact CompTrace.Preserves.failure

private theorem prom_rcv_getEntry_tr_at {Inv : ExecTrace → Prop} {α : Type}
    (skIdx : Nat) {f : CompTrace.TREntry → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ e : CompTrace.TREntry,
      (tr.at? skIdx : Option CompTrace.TREntry) = some e → Inv ((f e).run tr).2.val) :
    Inv (((DY.getEntry skIdx >>= f).run tr).2.val) := by
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [CompTrace.run_bind_snd, Traceful.run_mk]
  dsimp only
  rcases he : (tr.at? skIdx : Option CompTrace.TREntry) with _ | e
  · exact hInv
  · exact hf e he

private theorem prom_rcv_messageDecryptSkipped {p : Participant} (stateIdx msgIdx skIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr₀ : ExecTrace) :
    promRcvFrame p tr₀
      ((DY.Libsignal.TripleRatchet.messageDecryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run
        tr₀).2.val := by
  have hInv : promRcvFrame p tr₀ tr₀ := promRcvFrame_refl p tr₀
  have fx : promRcvFx (promRcvFrame p tr₀) p tr₀ := promRcvFrameFx p tr₀
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine CompTrace.bind_getLocalState_tr_at p stateIdx tr₀ hInv fun st _ => ?_
  rw [CompTrace.run_bind_snd]
  have hrcv_snd : ((receiveSignalMsg msgIdx).run tr₀).2.val = tr₀ :=
    CompTrace.Preserves.receiveSignalMsg (Inv := fun t => t = tr₀) msgIdx tr₀ rfl
  rcases hmsg : ((receiveSignalMsg msgIdx).run tr₀).1 with _ | msg
  · rw [hrcv_snd]; exact hInv
  · rw [hrcv_snd]
    refine prom_rcv_getEntry_tr_at skIdx tr₀ hInv fun e he => ?_
    rcases e with ⟨ev⟩
    cases ev with
    | SkippedKeyStored s pk n seed rIdx srcIdx =>
      dsimp only
      refine CompTrace.bind_guardP_at _ tr₀ hInv fun hguard => ?_
      obtain ⟨rfl, _, _⟩ := hguard
      have hsk_ev : promRcvEv p tr₀ (.SkippedKeyUsed (st.sessionInfo p) skIdx) :=
        ⟨rfl, pk, n, seed, rIdx, srcIdx, he⟩
      refine (CompTrace.Preserves.bind (CompTrace.Preserves.guardTrace _) fun _ => ?_) tr₀ hInv
      split
      · next _ key _ =>
        exact CompTrace.Preserves.bind (fx.send key) fun _ =>
          CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun pqSalt =>
          CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt st msg pqSalt seed)
            fun _ =>
          CompTrace.Preserves.bind (fx.tr _ hsk_ev) fun _ =>
          CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
          prom_rcv_logMKStore fx (st.sessionInfo p) rfl _ _ _ _ _ _ _
      · exact CompTrace.Preserves.failure
    | _ => dsimp only; rw [DY.Traceful.run_failure]; exact hInv

theorem prom_rcv_next_move {p : Participant} {tr₀ : ExecTrace} {m : Move}
    (hact : ActorIn p m) (hrk : RecvKind m ∨ NoSessionEffect tr₀ m) :
    promRcvFrame p tr₀ (m.next tr₀) := by
  rcases hrk with hrk | hno
  · cases m with
    | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
      have hme : me = p := by
        rcases hact with h | h <;> simp only [moveActor, Option.some.injEq, reduceCtorEq] at h
        exact h
      subst me
      dsimp only [Move.next, Move.act]
      rw [b5_run_bind_pure_val]
      exact prom_rcv_messageDecrypt (promRcvFrameFx p tr₀) stateIdx msgIdx pqIdx spqrMsgIdx tr₀
        (promRcvFrame_refl p tr₀)
    | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx _ =>
      have hme : me = p := by
        rcases hact with h | h <;> simp only [moveActor, Option.some.injEq, reduceCtorEq] at h
        exact h
      subst me
      dsimp only [Move.next, Move.act]
      rw [b5_run_bind_pure_val]
      exact prom_rcv_messageDecryptSkipped stateIdx msgIdx skIdx pqIdx spqrMsgIdx tr₀
    | reject _ =>
      dsimp only [Move.next, Move.act]
      rw [DY.Traceful.run_pure]
      exact promRcvFrame_refl p tr₀
    | _ => cases hrk
  · exact promRcvFrame_of_quietExt p (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quietExt_of_noSessionEffect hno)

end Symbolic.Swarm.CREF.CliPure.RecvPrekeyProm
