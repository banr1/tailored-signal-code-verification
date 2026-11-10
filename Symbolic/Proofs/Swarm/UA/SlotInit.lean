/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.EquationalTheory.Literal
import DY.EquationalTheory.DiffieHellman
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRecordInj
import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPureC
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L02GoodExit0Cut
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L04BridgeBQuietFail
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L07SlotInitCli
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.PendingPreKey
import Symbolic.Proofs.Swarm.UA.SlotInitTransfer
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDefs -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic

/-!
# Alice `init` Slot Invariant Preservation

Proves `slot_init_ua : UASlotInitSpec`, advancing `PqTurnSim1A` and `UAInv` across Alice's
`session_initiate` CLI call by combining the exit-`1` rejection lift with the exit-`0`
`.aliceStart` explanation and universal `AliceRecordPendingInSession` alignment.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.SlotInit

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Traceful ExecTraceTypes)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
open _root_.DY.Libsignal.PQXDH (PQXDHEvent BundleHandles)
open _root_.DY.Libsignal.TripleRatchet (TREvent TRState x25519LowOrder)
open CryptoVerification.E2E (PEParams initiateTapeLen)
open CryptoVerification.SignalSession (Inputs bundleDir PublicBundle)
open Symbolic.Swarm.CREF (compSemOf SemReady RoleStE initiateFullDrawLengths entropyBytes
  CBadSigmaFrame cBadSigmaFrame_updateFreshAt IniOkBin at?_of_setupTrace
  setupTrace_at?_4 setupTrace_at?_6 setupTrace_at?_25
  runTrace_getMessageSentAt_25 received_setupHandles received_setupHandles_some
  compat_of_sigma_eq_lt bundleCore_of_honestBundle attackerKnows_x25519Variant_opkPub
  x25519LowOrder_x25519Variant_opkPub gamma_x25519Variant_opkPub slice_9_33_eq_ecKey
  next_aliceStart_on_runTrace ini_forall₂_initiate_rng_34
  aliceStartTrOfOut aliceStart_next_cases bundleMatches_honest rng_vis_aliceStart_35
  kemEncapCtBytes bks_stored_of_getLocalState iniAliceStartTr getMessageSentAt_of_netMsgAt
  TR.gamma_kemEncap_fst TR.gamma_dhPk TR.setupTrace_eq TR.setupTrace_reachable
  TR.FreshSigma.VisStampsLt TR.FreshSigma.TraceEntriesLt
  TR.FreshSigma.updateFreshAt TR.FreshSigma.updateFreshAt_self
  TR.FreshSigma.traceEntriesLt_of_reachable)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry aliceOut)
open Symbolic.Swarm.CREF.CliPure (IniPure.iniP_alice_st_idx_eq_4
  IniPure.AliceInitiatedV1PostPure IniPure.aliceInitiatedV1_bytes_pure)
open Symbolic.Swarm.CREF.Cli (interpOfParams externContractsHoldCli_interpOfParams
  Slots.initiateDrawsOfCoins Slots.initiateDrawsOfCoins_lengths Slots.initiateDrawsOfCoins_nonempty
  Slots.initiateDrawsOfCoins_flatten Slots.initiateDrawsOfCoins_length Slots.recordCanonical_Q_inj)
open Symbolic.Swarm.Coinsplit.Lift (CliLiveAtCli)
open Symbolic.Proofs.Swarm.UA.Defs (runOk flatEntry flatExit failedSend flatEvent flatEvents
  callsOf SchedFits AlicePendingKeysOn AliceRecordPendingInSession UAInv UASlotPost UASlotInitSpec)
open Symbolic.Proofs.Swarm.UA.Base (runSteps_append callsOf_append callsOf_run_call
  flatEvents_append flatEvents_run_call failedSend_runEventOf callStarts_flatEvents_length
  collisionAtCli_append runRejected_none explains_snoc_rejected modelRunWF_of_append
  activeBundleIds_snoc_init_ok)
open Symbolic.Proofs.Swarm.UA.PendingPreKey (handshakeSessionValid_reachable modelRunWF_reachable
  aliceStart_ok_eq_iniAliceStartTr alicePendingKeysOn_iniAliceStartTr
  alicePendingKeysOn_of_matchesEvents aliceRecordPendingInSession_of_no_record
  aliceRecordPendingInSession_of_not_pending)
open Symbolic.Proofs.Swarm.UA.SlotInitTransfer (step_le_next runSteps_le step_next_reachable
  runSteps_reachable stepsWF_append_iff stepsStateFaithful_append_noLoad matchesEvents_snoc_run1
  matchesEvents_snoc_run_inv gamma_randTerm_eq matchesEvents_visStampsLt ghostWF_transfer
  matchesEvents_transfer not_readCollisionCli_snoc_noDecrypt)

/-! ## `stepToMove` Bridge and `AliceOnlyInitiator` -/

private def StepHasMove (s : Step) : Prop :=
  s.cls = .invisible ∨ s.cls = .party ∨ s.IsLeak

private def stepToMove : Step → Move
  | .network msg => .attackerSend msg
  | .aliceStart a b i r h => .aliceStart a b i r h 35
  | .bobStart b a kh r mh pq sp => .bobStart b a kh r mh pq sp 3
  | .messageEncrypt me si cl pq => .encrypt me si cl pq none
  | .messageEncryptAbort me si => .encryptAbort me si
  | .messageDecrypt me si mi pq sp => .decrypt me si mi pq sp false
  | .messageDecryptSkipped me si mi sk pq sp => .decryptSkipped me si mi sk pq sp false
  | .exposeKey me si k => .exposeKey me si k
  | .exposeSpqr me si => .exposeSpqr me si
  | .exposeSkipped sk => .exposeSkipped sk
  | .compromiseIK p si => .compromiseIK p si
  | .compromiseSPK b si => .compromiseSPK b si
  | .compromisePQSPK b si => .compromisePQSPK b si
  | .compromiseOPK b si => .compromiseOPK b si
  | _ => .reject []

private theorem stepToMove_isSetup_false (s : Step) : (stepToMove s).isSetup = false := by
  cases s <;> rfl

private theorem bind_pure_unit_snd {α : Type} (x : Traceful α) (tr : ExecTrace) :
    ((x >>= fun _ => pure ()).run tr).2.val = (x.run tr).2.val := by
  rw [_root_.DY.Traceful.run_bind]
  rcases x.run tr with ⟨_ | _, _⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem stepIn_next (c : _root_.DY.ReachabilityConfig)
    [i : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (i.pf_step x).symm

private theorem stepToMove_next {s : Step} (hs : StepHasMove s) (tr : ExecTrace) :
    (stepToMove s).next tr = s.next tr := by
  cases s <;>
    (try (rcases hs with h | h | h <;> cases h)) <;>
    (dsimp only [stepToMove, Move.next, Move.act, Step.next, Step.toInput];
     symm;
     refine (stepIn_next _ _ tr).trans ?_;
     exact (bind_pure_unit_snd _ tr).symm)


private theorem runSteps_eq_runMoves_map :
    ∀ {ss : List Step}, (∀ s ∈ ss, StepHasMove s) → ∀ (tr : ExecTrace),
      runSteps ss tr = (runMoves (ss.map stepToMove) tr).1
  | [], _, _ => rfl
  | s :: ss, h, tr => by
    rw [List.map_cons, runMoves_cons_fst, stepToMove_next (h s (.head _)) tr, runSteps]
    exact runSteps_eq_runMoves_map (fun s' hs' => h s' (.tail _ hs')) (s.next tr)

private theorem runTrace_eq_runTraceMoves (r : ProtocolSetup) {ss : List Step}
    (h : ∀ s ∈ ss, StepHasMove s) :
    runTrace r ss = runTraceMoves r (ss.map stepToMove) := by
  unfold runTrace runTraceMoves
  rw [runMoves_cons_fst]
  have hsetup : r.setupMove.next _root_.DY.Trace.nil = setupTrace r := rfl
  rw [hsetup]
  exact runSteps_eq_runMoves_map h (setupTrace r)

private theorem matchesEvents_stepHasMove {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
    {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsClassicalAt interp r S g initIds tr ss evs vis) :
    ∀ s ∈ ss, StepHasMove s := by
  induction hme with
  | nil hinv => exact fun s hs => Or.inl (hinv s hs)
  | run1 hpre hrm _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inl (hpre x hx)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr (Or.inl hrm.1)
      · exact ih x hx
  | run0 hpre _ _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inl (hpre x hx)
    · exact ih x hx
  | @env _ _ _ _ _ ev _ _ _ hpre hem _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inl (hpre x hx)
    · rcases List.mem_cons.mp hx with rfl | hx
      · cases ev with
        | leak _ _ => exact Or.inr (Or.inr hem.2.1)
        | breakDH | breakKEM | invertDH _ | invertKEM _ | registerCorrupt _ _ => cases hem
      · exact ih x hx

private def AliceOnlyInitiator (alice : Participant) (tr : ExecTrace) : Prop :=
  ∀ (st : TRState) (i : Nat), (tr.at? i : Option RoleStE) = some ⟨⟨alice, st⟩⟩ →
    st.initiator = true

private theorem aliceOnlyInitiator_of_noNewSt {alice : Participant} {tr tr' : ExecTrace}
    (hle : tr ≤ tr')
    (hno : ∀ i, tr.length ≤ i → i < tr'.length → (tr'.at? i : Option RoleStE) = none)
    (h : AliceOnlyInitiator alice tr) :
    AliceOnlyInitiator alice tr' := by
  intro st i hat
  by_cases hi : i < tr.length
  · rw [Symbolic.Swarm.CREF.XplSteps.xat?_le_eq hle hi] at hat
    exact h st i hat
  · by_cases hi' : i < tr'.length
    · rw [hno i (Nat.le_of_not_lt hi) hi'] at hat
      cases hat
    · simp only [_root_.DY.Trace.at?, show ¬ i < tr'.length by omega, dite_false] at hat
      cases hat

private theorem aliceOnlyInitiator_of_xquiet {alice : Participant} {α : Type} {x : Traceful α}
    (hq : Symbolic.Swarm.CREF.XplSteps.XQuiet x) {tr : ExecTrace}
    (h : AliceOnlyInitiator alice tr) :
    AliceOnlyInitiator alice (x.run tr).2.val :=
  aliceOnlyInitiator_of_noNewSt (Symbolic.Swarm.CREF.XplSteps.xrun_le x tr)
    (fun i hi _ => (hq tr i hi).1) h

private theorem aliceOnlyInitiator_append_non_st {E : Type} [ExecTraceTypes.Has E]
    {alice : Participant} {tr : ExecTrace} (e : E)
    (hnone : (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option RoleStE) = none)
    (h : AliceOnlyInitiator alice tr) :
    AliceOnlyInitiator alice (tr.append e) := by
  refine aliceOnlyInitiator_of_noNewSt (_root_.DY.Trace.append_le tr e) (fun i hi hlt => ?_) h
  have heq : i = tr.length := by
    have hlen : (tr.append e).length = tr.length + 1 := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    omega
  subst heq
  exact Symbolic.Swarm.CREF.TR.at?_append_eq_of_proj tr e rfl _ hnone

private theorem aliceOnlyInitiator_append_st {alice p : Participant} {st₀ : TRState}
    {tr : ExecTrace} (hp : p = alice → st₀.initiator = true)
    (h : AliceOnlyInitiator alice tr) :
    AliceOnlyInitiator alice (tr.append (⟨⟨p, st₀⟩⟩ : RoleStE)) := by
  intro st i hat
  rcases Symbolic.Swarm.COMPOSED.CompTrace.trStateStoredAt_append_same hat with
    ⟨_, hat₀⟩ | ⟨_, rfl, rfl⟩
  · exact h st i hat₀
  · exact hp rfl

private theorem bobStart_alice_next_eq {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {ms : List Move}
    (hms : ∀ m ∈ ms, m.isSetup = false)
    (a : Participant) (kh : _root_.DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : _root_.DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    let tr := runTraceMoves r ms
    (Step.bobStart r.alice a kh regIdxA mh pqIdx spqrMsgIdx).next tr = tr := by
  intro tr
  rw [← stepToMove_next (Or.inr (Or.inl rfl))]
  dsimp only [stepToMove, Move.next, Move.act]
  rw [bind_pure_unit_snd]
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.bobStart_eq_inline]
  exact Symbolic.Swarm.COMPOSED.CompTrace.bind_bobHandshake_at
    (Inv := fun tr' => tr' = tr) r.alice a kh regIdxA mh.ek mh.ct tr rfl
    fun _ spkSk _ _ _ _ _ _ _ _ _ hstSpk _ _ _ _ _ _ _ => by
      have hidx : kh.spk = 4 := IniPure.iniP_alice_st_idx_eq_4 hne hms hstSpk
      rw [hidx] at hstSpk
      have h4 := at?_of_setupTrace (ms := ms) (setupTrace_at?_4 r hne)
      have heq := hstSpk.symm.trans h4
      cases heq

private def AliceTraceful (alice : Participant) {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, AliceOnlyInitiator alice tr →
    AliceOnlyInitiator alice (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a

private theorem AliceTraceful.of_xquiet {alice : Participant} {α : Type} {x : Traceful α}
    (hq : Symbolic.Swarm.CREF.XplSteps.XQuiet x) :
    AliceTraceful alice (fun _ => True) x :=
  fun _ h => ⟨aliceOnlyInitiator_of_xquiet hq h, fun _ _ => trivial⟩

private theorem AliceTraceful.pure {alice : Participant} {α : Type} {Q : α → Prop} {a : α}
    (ha : Q a) : AliceTraceful alice Q (Pure.pure a) := by
  intro _ h
  simp only [_root_.DY.Traceful.run_pure, Option.some.injEq]
  exact ⟨h, fun _ hb => hb ▸ ha⟩

private theorem AliceTraceful.failure {alice : Participant} {α : Type} {Q : α → Prop} :
    AliceTraceful alice Q (failure : Traceful α) := by
  intro _ h
  simp only [_root_.DY.Traceful.run_failure]
  exact ⟨h, fun _ ha => by cases ha⟩

private theorem AliceTraceful.bind {alice : Participant} {α β : Type}
    {P : α → Prop} {Q : β → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : AliceTraceful alice P x) (hf : ∀ a, P a → AliceTraceful alice Q (f a)) :
    AliceTraceful alice Q (x >>= f) := by
  intro tr h; obtain ⟨h₁, hP⟩ := hx tr h; rw [_root_.DY.Traceful.run_bind]
  rcases hrun : (x.run tr) with ⟨_ | a, sub⟩
  · exact ⟨by simpa [hrun] using h₁, fun _ hb => by cases hb⟩
  · exact hf a (hP a (by simp [hrun])) sub.val (by simpa [hrun] using h₁)

private theorem AliceTraceful.bind_true {alice : Participant} {α β : Type}
    {Q : β → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : AliceTraceful alice (fun _ => True) x) (hf : ∀ a, AliceTraceful alice Q (f a)) :
    AliceTraceful alice Q (x >>= f) :=
  AliceTraceful.bind hx fun a _ => hf a

private theorem AliceTraceful.run_snd {alice : Participant} {α : Type} {Q : α → Prop}
    {x : Traceful α} (hx : AliceTraceful alice Q x) {tr : ExecTrace}
    (h : AliceOnlyInitiator alice tr) : AliceOnlyInitiator alice (x.run tr).2.val :=
  (hx tr h).1

private theorem AliceTraceful.getLocalState (alice me : Participant) (idx : Nat) :
    AliceTraceful alice (fun st : TRState => me = alice → st.initiator = true)
      (_root_.DY.PersistentLocalState.getLocalState me idx) := by
  intro tr h
  refine ⟨by rw [Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState me idx tr]; exact h, fun st hst hme => ?_⟩
  subst hme; exact h st idx (bks_stored_of_getLocalState hst)

private theorem AliceTraceful.storeLocalState {alice : Participant} (me : Participant)
    {st : TRState} (hst : me = alice → st.initiator = true) :
    AliceTraceful alice (fun _ => True) (_root_.DY.PersistentLocalState.storeLocalState me st) := by
  intro _ h
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_mk]
  exact ⟨aliceOnlyInitiator_append_st hst h, fun _ _ => trivial⟩

private theorem AliceTraceful.logEvent_tr (alice : Participant) (ev : TREvent) :
    AliceTraceful alice (fun _ => True) (_root_.DY.ProtocolEvent.logEvent ev) := by
  intro _ h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_bind,
    _root_.DY.Traceful.run_mk, _root_.DY.Traceful.run_pure]
  exact ⟨aliceOnlyInitiator_append_non_st (⟨ev⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent) rfl h, fun _ _ => trivial⟩

private theorem AliceTraceful.logEvent_pq (alice : Participant) (ev : PQXDHEvent) :
    AliceTraceful alice (fun _ => True) (_root_.DY.ProtocolEvent.logEvent ev) := by
  intro _ h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_bind,
    _root_.DY.Traceful.run_mk, _root_.DY.Traceful.run_pure]
  exact ⟨aliceOnlyInitiator_append_non_st (⟨ev⟩ : _root_.DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl h, fun _ _ => trivial⟩

private theorem AliceTraceful.logEvent_c (alice : Participant) (ev : ComposedEvent) :
    AliceTraceful alice (fun _ => True) (_root_.DY.ProtocolEvent.logEvent ev) := by
  intro _ h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_bind,
    _root_.DY.Traceful.run_mk, _root_.DY.Traceful.run_pure]
  exact ⟨aliceOnlyInitiator_append_non_st (⟨ev⟩ : _root_.DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl h, fun _ _ => trivial⟩

private theorem AliceTraceful.logSkippedKeys (alice : Participant)
    (s : _root_.DY.Libsignal.TripleRatchet.SessionInfo) (pk : _root_.DY.Bytes)
    (rIdx src : Nat) (ck : _root_.DY.Bytes) (n : UInt32) (k : Nat) :
    AliceTraceful alice (fun _ => True)
      (_root_.DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  intro tr h; refine ⟨?_, fun _ _ => trivial⟩
  rw [(Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeys_run s pk rIdx src ck n k tr).2]
  induction k generalizing ck n tr with
  | zero => exact h
  | succ k ih =>
    exact ih _ _ _ (aliceOnlyInitiator_append_non_st (⟨_⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent) rfl h)

private theorem AliceTraceful.logMessageKeyAndStore {alice : Participant} (me : Participant)
    {s : _root_.DY.Libsignal.TripleRatchet.SessionInfo}
    {dir : _root_.DY.Libsignal.TripleRatchet.KeyDir} {seed pqSalt : _root_.DY.Bytes}
    {n : UInt32} {rIdx par : Nat} {st : TRState} (hst : me = alice → st.initiator = true) :
    AliceTraceful alice (fun _ => True)
      (_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact AliceTraceful.bind_true (AliceTraceful.logEvent_tr alice _) fun _ =>
    AliceTraceful.storeLocalState me hst

private theorem AliceTraceful.dhRatchetStep (alice : Participant) (st : TRState) (pk : _root_.DY.Bytes) :
    AliceTraceful alice (fun x => x.1.initiator = st.initiator)
      (_root_.DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine AliceTraceful.bind (AliceTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix (Symbolic.Swarm.CREF.XplSteps.xfix_guard _))) fun _ _ => ?_
  exact AliceTraceful.bind (AliceTraceful.of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_genRand 32)) fun _ _ => AliceTraceful.pure rfl

private theorem AliceTraceful.ensureReceiverChain (alice : Participant) (st : TRState) (pk : _root_.DY.Bytes) :
    AliceTraceful alice (fun x => x.1.initiator = st.initiator)
      (_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · exact AliceTraceful.pure rfl
  · exact AliceTraceful.bind (AliceTraceful.dhRatchetStep alice st pk) fun ⟨_, _⟩ hx => AliceTraceful.pure hx
  · exact AliceTraceful.failure

private theorem aliceOnlyInitiator_step {r : ProtocolSetup} (hne : r.alice ≠ r.bob)
    {ss₀ : List Step} (hss₀ : ∀ x ∈ ss₀, StepHasMove x)
    {s : Step} (hs : StepHasMove s)
    (h : AliceOnlyInitiator r.alice (runTrace r ss₀)) :
    AliceOnlyInitiator r.alice (s.next (runTrace r ss₀)) := by
  let tr := runTrace r ss₀
  have htr_eq : tr = runTraceMoves r (ss₀.map stepToMove) := runTrace_eq_runTraceMoves r hss₀
  have hms_setup : ∀ m ∈ ss₀.map stepToMove, m.isSetup = false := by
    intro m hm; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hm; exact stepToMove_isSetup_false x
  let xq {α : Type} {x : Traceful α} := @AliceTraceful.of_xquiet r.alice α x
  let xf {α : Type} {x : Traceful α} := @Symbolic.Swarm.CREF.XplSteps.xquiet_of_fix α x
  let bt {α β : Type} {Q : β → Prop} {x : Traceful α} {f : α → Traceful β} :=
    @AliceTraceful.bind_true r.alice α β Q x f
  let lpq := AliceTraceful.logEvent_pq r.alice
  let ltr := AliceTraceful.logEvent_tr r.alice
  let lc := AliceTraceful.logEvent_c r.alice
  cases s with
  | network msg =>
    rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    exact aliceOnlyInitiator_of_xquiet (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage msg) h
  | aliceStart a b idStateIdx regIdxB bh =>
    rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    refine AliceTraceful.run_snd (Q := fun _ => True) ?_ h; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.aliceStart_eq_inline]
    exact bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_aliceHandshake _ _ _ _ _)) fun _ =>
      bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_genRand 32)) fun _ =>
      bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)) fun _ =>
      bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)) fun _ =>
      bt (xq (xf Symbolic.Swarm.CREF.XplSteps.xfix_traceLength)) fun _ =>
      bt (lpq _) fun _ => bt (ltr _) fun _ => bt (lc _) fun _ =>
      AliceTraceful.storeLocalState a (fun _ => rfl)
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx =>
    by_cases hb : b = r.alice
    · subst hb
      change AliceOnlyInitiator r.alice ((Step.bobStart r.alice a kh regIdxA mh pqIdx spqrMsgIdx).next tr)
      rw [htr_eq, bobStart_alice_next_eq hne hms_setup]; rwa [← htr_eq]
    · rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
      refine AliceTraceful.run_snd (Q := fun _ => True) ?_ h; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.bobStart_eq_inline]
      refine bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_bobHandshake b a kh regIdxA mh.ek mh.ct)) fun _ =>
        bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_receiveSignalMsg mh.msg)) fun msg =>
        AliceTraceful.bind (AliceTraceful.ensureReceiverChain r.alice _ msg.ratchetKey) fun x _ => ?_
      rcases x with ⟨st, c, rat⟩
      have hst : b = r.alice → st.initiator = true := fun hba => absurd hba hb
      dsimp only; split
      · split
        · refine bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)) fun _ =>
            bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage _))) fun _ =>
            bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_verifyMacAndDecrypt _ _ _ _)) fun _ => ?_
          split
          · refine bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_guardOnTrace _))) fun _ =>
              bt (lpq _) fun _ => bt (xq (xf Symbolic.Swarm.CREF.XplSteps.xfix_traceLength)) fun _ =>
              bt (lpq _) fun _ => ?_
            split
            · exact bt (ltr _) fun _ => bt (ltr _) fun _ => bt (lc _) fun _ =>
                bt (xq (xf Symbolic.Swarm.CREF.XplSteps.xfix_traceLength)) fun _ =>
                bt (AliceTraceful.logSkippedKeys r.alice _ _ _ _ _ _ _) fun _ =>
                bt (ltr _) fun _ => AliceTraceful.logMessageKeyAndStore b hst
            · exact bt (lc _) fun _ => bt (xq (xf Symbolic.Swarm.CREF.XplSteps.xfix_traceLength)) fun _ =>
                bt (AliceTraceful.logSkippedKeys r.alice _ _ _ _ _ _ _) fun _ =>
                bt (ltr _) fun _ => AliceTraceful.logMessageKeyAndStore b hst
          · refine bt (xq (xf Symbolic.Swarm.CREF.XplSteps.xfix_traceLength)) fun _ => bt (lpq _) fun _ => ?_
            split
            · exact bt (ltr _) fun _ => bt (ltr _) fun _ => bt (lc _) fun _ =>
                bt (xq (xf Symbolic.Swarm.CREF.XplSteps.xfix_traceLength)) fun _ =>
                bt (AliceTraceful.logSkippedKeys r.alice _ _ _ _ _ _ _) fun _ =>
                bt (ltr _) fun _ => AliceTraceful.logMessageKeyAndStore b hst
            · exact bt (lc _) fun _ => bt (xq (xf Symbolic.Swarm.CREF.XplSteps.xfix_traceLength)) fun _ =>
                bt (AliceTraceful.logSkippedKeys r.alice _ _ _ _ _ _ _) fun _ =>
                bt (ltr _) fun _ => AliceTraceful.logMessageKeyAndStore b hst
        · exact AliceTraceful.failure
      · exact AliceTraceful.failure
  | messageEncrypt me stateIdx coinsLen pqIdx =>
    rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    refine AliceTraceful.run_snd (Q := fun _ => True) ?_ h; unfold _root_.DY.Libsignal.TripleRatchet.messageEncrypt
    exact AliceTraceful.bind (AliceTraceful.getLocalState r.alice me stateIdx) fun st hst =>
      bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_guard _))) fun _ =>
      bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_genRand 32)) fun _ =>
      bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_genRand coinsLen)) fun _ =>
      bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)) fun _ =>
      bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage pqIdx))) fun _ =>
      bt (ltr _) fun _ => bt (AliceTraceful.logMessageKeyAndStore me hst) fun _ =>
      xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)
  | messageEncryptAbort me stateIdx =>
    rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    refine AliceTraceful.run_snd (Q := fun _ => True) ?_ h; unfold _root_.DY.Libsignal.TripleRatchet.messageEncryptAbort
    exact AliceTraceful.bind (AliceTraceful.getLocalState r.alice me stateIdx) fun _ _ =>
      bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_genRand 32)) fun _ => AliceTraceful.failure
  | messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx =>
    rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    refine AliceTraceful.run_snd (Q := fun _ => True) ?_ h; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
    refine AliceTraceful.bind (AliceTraceful.getLocalState r.alice me stateIdx) fun st hst =>
      bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_receiveSignalMsg msgIdx)) fun msg =>
      AliceTraceful.bind (AliceTraceful.ensureReceiverChain r.alice st msg.ratchetKey) fun x hx => ?_
    rcases x with ⟨st', c, rat⟩
    have hst' : me = r.alice → st'.initiator = true := fun hme => hx.trans (hst hme)
    dsimp only; split
    · split
      · refine bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)) fun _ =>
          bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage _))) fun _ =>
          bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_verifyMacAndDecrypt _ _ _ _)) fun _ => ?_
        split
        · exact bt (ltr _) fun _ => bt (ltr _) fun _ =>
            bt (AliceTraceful.logSkippedKeys r.alice _ _ _ _ _ _ _) fun _ =>
            bt (ltr _) fun _ => AliceTraceful.logMessageKeyAndStore me hst'
        · exact bt (AliceTraceful.logSkippedKeys r.alice _ _ _ _ _ _ _) fun _ =>
            bt (ltr _) fun _ => AliceTraceful.logMessageKeyAndStore me hst'
      · exact AliceTraceful.failure
    · exact AliceTraceful.failure
  | messageDecryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx =>
    rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    refine AliceTraceful.run_snd (Q := fun _ => True) ?_ h; unfold _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
    refine AliceTraceful.bind (AliceTraceful.getLocalState r.alice me stateIdx) fun st hst =>
      bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_receiveSignalMsg msgIdx)) fun _ =>
      bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_getEntry k))) fun _ => ?_
    split
    · refine bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_guard _))) fun _ =>
        bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_guardTrace _))) fun _ => ?_
      split
      · exact bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)) fun _ =>
          bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage _))) fun _ =>
          bt (xq (Symbolic.Swarm.CREF.XplSteps.xquiet_verifyMacAndDecrypt _ _ _ _)) fun _ =>
          bt (ltr _) fun _ => bt (ltr _) fun _ => AliceTraceful.logMessageKeyAndStore me hst
      · exact AliceTraceful.failure
    · exact AliceTraceful.failure
  | exposeKey me stH kc =>
    rw [← stepToMove_next hs]; clear hs; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    unfold _root_.DY.Libsignal.TripleRatchet.exposeKey; refine AliceTraceful.run_snd (Q := fun _ => True) ?_ h
    refine AliceTraceful.bind (AliceTraceful.getLocalState r.alice me stH) fun _ _ => ?_
    cases kc <;> try exact bt (ltr _) fun _ => xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)
    dsimp only; split
    · exact bt (ltr _) fun _ => xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)
    · exact AliceTraceful.failure
  | exposeSpqr me stH =>
    rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    unfold _root_.DY.Libsignal.TripleRatchet.exposeSpqr
    exact AliceTraceful.run_snd (AliceTraceful.bind (AliceTraceful.getLocalState r.alice me stH) fun _ _ =>
      bt (ltr _) fun _ => xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)) h
  | exposeSkipped evH =>
    rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    unfold _root_.DY.Libsignal.TripleRatchet.exposeSkipped; refine AliceTraceful.run_snd (Q := fun _ => True) ?_ h
    refine bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_getEntry evH))) fun _ => ?_; split
    · exact bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_guardTrace _))) fun _ =>
        bt (ltr _) fun _ => xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)
    · exact AliceTraceful.failure
  | compromiseIK _ _ =>
    rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    unfold _root_.DY.Libsignal.PQXDH.compromiseIK
    exact AliceTraceful.run_snd (bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_getKey _ _ _))) fun _ =>
      bt (lpq _) fun _ => xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)) h
  | compromiseSPK _ _ =>
    rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    unfold _root_.DY.Libsignal.PQXDH.compromiseSPK
    exact AliceTraceful.run_snd (bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_getKey _ _ _))) fun _ =>
      bt (lpq _) fun _ => xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)) h
  | compromisePQSPK _ _ =>
    rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    unfold _root_.DY.Libsignal.PQXDH.compromisePQSPK
    exact AliceTraceful.run_snd (bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_getKey _ _ _))) fun _ =>
      bt (lpq _) fun _ => xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)) h
  | compromiseOPK _ _ =>
    rw [← stepToMove_next hs]; dsimp only [stepToMove, Move.next, Move.act]; rw [bind_pure_unit_snd]
    unfold _root_.DY.Libsignal.PQXDH.compromiseOPK
    exact AliceTraceful.run_snd (bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_getKey _ _ _))) fun _ =>
      bt (xq (xf (Symbolic.Swarm.CREF.XplSteps.xfix_guardOnTrace _))) fun _ =>
      bt (lpq _) fun _ => xq (Symbolic.Swarm.CREF.XplSteps.xquiet_sendMessage _)) h
  | registerIdentity _ | registerCorruptIdentity _ _ | genSignedPrekey _ _
  | genPQPrekey _ _ | genOneTimePrekey _ | breakDH | breakKEM | invertDH _ | invertKEM _ =>
    rcases hs with hc | hc | hc <;> cases hc

private theorem aliceOnlyInitiator_nil (alice : Participant) :
    AliceOnlyInitiator alice _root_.DY.Trace.nil := by
  intro _ _ hat
  simp only [_root_.DY.Trace.at?, Symbolic.DYBridge.DY.Trace.nil_length_not_lt,
    ↓reduceDIte, reduceCtorEq] at hat

private theorem aliceOnlyInitiator_setupTrace (r : ProtocolSetup) (hne : r.alice ≠ r.bob) :
    AliceOnlyInitiator r.alice (setupTrace r) := by
  rw [TR.setupTrace_eq r hne]; cases r.withOpk
  · unfold Symbolic.Swarm.CREF.TR.setupTr4 Symbolic.Swarm.CREF.TR.setupTr3
      Symbolic.Swarm.CREF.TR.setupTr2 Symbolic.Swarm.CREF.TR.setupTr1
    repeat (refine aliceOnlyInitiator_append_non_st _ rfl ?_)
    exact aliceOnlyInitiator_nil r.alice
  · unfold Symbolic.Swarm.CREF.TR.setupTr5 Symbolic.Swarm.CREF.TR.setupTr4
      Symbolic.Swarm.CREF.TR.setupTr3 Symbolic.Swarm.CREF.TR.setupTr2 Symbolic.Swarm.CREF.TR.setupTr1
    repeat (refine aliceOnlyInitiator_append_non_st _ rfl ?_)
    exact aliceOnlyInitiator_nil r.alice

private theorem aliceOnlyInitiator_runTrace {r : ProtocolSetup} (hne : r.alice ≠ r.bob)
    {ss : List Step} (hss : ∀ x ∈ ss, StepHasMove x) :
    AliceOnlyInitiator r.alice (runTrace r ss) := by
  induction ss using List.reverseRecOn with
  | nil => exact aliceOnlyInitiator_setupTrace r hne
  | append_singleton ss₀ s ih =>
    rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
    exact aliceOnlyInitiator_step hne (fun x hx => hss x (List.mem_append_left _ hx))
      (hss s (List.mem_append_right _ (List.mem_singleton_self _)))
      (ih (fun x hx => hss x (List.mem_append_left _ hx)))

/-! ## Exit-0 Explanation -/

private theorem stepIn_isSome (c : _root_.DY.ReachabilityConfig)
    [i : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => ((s.2.run tr).1).isSome) (i.pf_step x).symm

private theorem aliceStart_ok_and_stepView {r : ProtocolSetup} {ms : List Move} (hNe : r.alice ≠ r.bob)
    {oi : Option Nat} {opk : Option _root_.DY.Bytes}
    (hopk : Symbolic.Swarm.CREF.NetOpt (runTraceMoves r ms) oi opk)
    (hlow : (opk.all fun o => !x25519LowOrder o) = true) (wrapped : Bool) :
    let tr := runTraceMoves r ms
    let bh : BundleHandles := { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := oi }
    let s := Step.aliceStart r.alice r.bob 4 6 bh
    s.ok tr = true ∧
      stepView s tr wrapped =
        (⟨.recv, received tr ([14, 15, 20, 21] ++ oi.toList), .bundle, none⟩ : VisEntry) ::
          (rngEntry (randTerm tr.length 32) :: kyberCoinEntries (randTerm (tr.length + 1) 32) ++
            [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }]) := by
  intro tr bh s
  have h14 := at?_of_setupTrace (ms := ms) (Symbolic.Swarm.CREF.setupTrace_at?_14 r hNe)
  rw [Symbolic.Swarm.CREF.setupPublic_4 r hNe] at h14
  have h15 := at?_of_setupTrace (ms := ms) (Symbolic.Swarm.CREF.setupTrace_at?_15 r hNe)
  rw [Symbolic.Swarm.CREF.setupPublic_5 r hNe] at h15
  have h20 := at?_of_setupTrace (ms := ms) (Symbolic.Swarm.CREF.setupTrace_at?_20 r hNe)
  rw [Symbolic.Swarm.CREF.setupPublic_6 r hNe] at h20
  have h21 := at?_of_setupTrace (ms := ms) (Symbolic.Swarm.CREF.setupTrace_at?_21 r hNe)
  rw [Symbolic.Swarm.CREF.setupPublic_7 r hNe] at h21
  have hruns := Symbolic.Swarm.CREF.Runs.aliceStart
    (h := bh)
    (at?_of_setupTrace (setupTrace_at?_4 r hNe))
    (at?_of_setupTrace (setupTrace_at?_6 r hNe))
    h14 h15 h20 h21
    (DY.Signature.verify_sign _ _ _) (DY.Signature.verify_sign _ _ _)
    hopk (by
      simp only [x25519LowOrder, _root_.DY.X25519.normalizeX25519Key,
        DY.DiffieHellman.dhPk, _root_.DY.Literal.CanMkLiteral.bytesToLiteral]
      rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _]
      dsimp only
      rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _]) hlow
  have hok : s.ok tr = true := by
    unfold Step.ok
    dsimp only [s, Step.toInput]
    refine (stepIn_isSome _ _ tr).trans ?_
    dsimp only [_root_.DY.Libsignal.Composed.aliceStart.reachability]
    rw [hruns.1]
    rfl
  refine ⟨hok, ?_⟩
  unfold stepView
  simp only [hok, ↓reduceIte]
  have hnext : s.next tr = (Move.aliceStart r.alice r.bob 4 6 bh 35).next tr :=
    (stepToMove_next (s := s) (Or.inr (Or.inl rfl)) tr).symm
  rw [hnext, next_aliceStart_on_runTrace hNe 35 hopk hlow,
    Symbolic.Swarm.CREF.exposures_iniAliceStartTr, List.append_nil]
  unfold aliceVis
  rw [Symbolic.Swarm.CREF.newRandoms_iniAliceStartTr,
    Symbolic.Swarm.CREF.eventIdx_isAliceDone_iniAliceStartTr]
  rfl

private theorem opkChoice_steps {interp' : ExternInterpretation}
    (hext' : ExternContractsHoldCli interp') {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {S : OpaqueSymbolSemantics} {g₀ : Ghost} (hC₀ : GhostAndSemMatchSetup interp' r S g₀) (ms : List Move)
    {bundle : HwBytes} {ds : List HwBytes}
    (hhon : HonestBundle interp' r bundle) (hok : IniOkBin bundle ds) :
    ∃ (pre : List Step) (oi : Option Nat) (opk : Option _root_.DY.Bytes),
      (pre = [] ∨ ∃ t, pre = [.network t] ∧ t.AttackerKnows (runTraceMoves r ms)) ∧
      Symbolic.Swarm.CREF.NetOpt (runTraceMoves r (ms ++ pre.map stepToMove)) oi opk ∧
      (opk.all fun o => !x25519LowOrder o) = true ∧
      ∀ g' : Ghost, g'.addr = g₀.addr →
        (∀ i j, i < (runTraceMoves r (ms ++ pre.map stepToMove)).length → g'.σ i j = g₀.σ i j) →
        PreKeyBundleLayoutMatches interp' S g' bundle
          (received (runTraceMoves r (ms ++ pre.map stepToMove)) ([14, 15, 20, 21] ++ oi.toList)) := by
  have hNe : r.alice ≠ r.bob := hwf.1
  have hEq := hext'.1
  have hPubCanon := hext'.2.1
  rcases hok.opk with h0 | ⟨h1, hb9, hlowLit⟩
  · refine ⟨[], none, none, Or.inl rfl, ?_, rfl, ?_⟩
    · simp [Symbolic.Swarm.CREF.NetOpt]
    · intro g' haddr hσ
      have hC' := compat_of_sigma_eq_lt hNe (ms ++ []) hC₀ haddr hσ
      rw [List.map_nil, List.append_nil, Option.toList, List.append_nil,
        received_setupHandles r ms hNe]
      exact ⟨bundleCore_of_honestBundle interp' r hNe _ g' hC' bundle hhon hok.bundle_len, h0⟩
  · obtain ⟨hslice, hlen32⟩ := slice_9_33_eq_ecKey hok.bundle_len hb9
    let opkBytes := slice bundle 10 32
    by_cases hHonU : r.withOpk = true ∧
        x25519UCoord opkBytes = x25519UCoord (pubBytes interp' (secretBytes r 6))
    · rcases hHonU with ⟨hWith, huOf⟩
      by_cases hBytes : opkBytes = pubBytes interp' (secretBytes r 6)
      · refine ⟨[], some 25, some (setupPublic r 8), Or.inl rfl, ?_, ?_, ?_⟩
        · simp only [Symbolic.Swarm.CREF.NetOpt, List.map_nil, List.append_nil]
          exact at?_of_setupTrace (setupTrace_at?_25 r hNe hWith)
        · simp only [Option.all, Symbolic.Swarm.CREF.setupPublic_8 r hNe hWith,
            x25519LowOrder, _root_.DY.X25519.normalizeX25519Key,
            DY.DiffieHellman.dhPk, _root_.DY.Literal.CanMkLiteral.bytesToLiteral]
          rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _]
          dsimp only
          rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _]
          rfl
        · intro g' haddr hσ
          have hC' := compat_of_sigma_eq_lt hNe (ms ++ []) hC₀ haddr hσ
          rw [List.map_nil, received_setupHandles_some r (ms ++ []) hNe
            (runTrace_getMessageSentAt_25 r (ms ++ []) hNe hWith)]
          refine ⟨bundleCore_of_honestBundle interp' r hNe _ g' hC' bundle hhon hok.bundle_len,
            h1, ?_⟩
          rw [Symbolic.Swarm.CREF.gamma_setupPublic_8 interp' r hNe hWith _ g' hC', ← hBytes]
          exact hslice
      · let opkTerm := DY.X25519.x25519Variant (setupPublic r 8)
          (_root_.DY.Libsignal.Refinement.keyVariation opkBytes)
        let pre : List Step := [.network opkTerm]
        have hknows : opkTerm.AttackerKnows (runTraceMoves r ms) :=
          attackerKnows_x25519Variant_opkPub r ms hNe hWith
            (_root_.DY.Libsignal.Refinement.keyVariation opkBytes)
        have hsent :
            (runTraceMoves r (ms ++ pre.map stepToMove)).getMessageSentAt (runTraceMoves r ms).length =
              some opkTerm := by
          dsimp only [pre, List.map, stepToMove]
          rw [Symbolic.Swarm.Leaves.IC12Stage1MP.runTrace_snoc]
          exact Symbolic.Swarm.CREF.getMessageSentAt_attackerSend _ _
        refine ⟨pre, some (runTraceMoves r ms).length, some opkTerm,
          Or.inr ⟨opkTerm, rfl, hknows⟩, ?_, ?_, ?_⟩
        · dsimp only [pre, List.map, stepToMove]
          simp only [Symbolic.Swarm.CREF.NetOpt,
            Symbolic.Swarm.Leaves.IC12Stage1MP.runTrace_snoc,
            Symbolic.Swarm.Leaves.IC12Stage1MP.attackerSend_next]
          exact Symbolic.Swarm.CREF.at?_append_self _ _
        · simp [Option.all, opkTerm, x25519LowOrder_x25519Variant_opkPub r hNe hWith]
        · intro g' haddr hσ
          have hC' := compat_of_sigma_eq_lt hNe (ms ++ pre.map stepToMove) hC₀ haddr hσ
          rw [received_setupHandles_some r (ms ++ pre.map stepToMove) hNe hsent]
          refine ⟨bundleCore_of_honestBundle interp' r hNe _ g' hC' bundle hhon hok.bundle_len,
            h1, ?_⟩
          dsimp only [opkTerm]
          rw [gamma_x25519Variant_opkPub hEq hPubCanon hwf hWith _ g' hC' hlen32 huOf]
          exact hslice
    · let opkTerm := Symbolic.Swarm.CREF.compHwLit opkBytes
      let pre : List Step := [.network opkTerm]
      have hknows : opkTerm.AttackerKnows (runTraceMoves r ms) :=
        Symbolic.Swarm.CREF.attackerKnows_compHwLit opkBytes (runTraceMoves r ms)
      have hsent :
          (runTraceMoves r (ms ++ pre.map stepToMove)).getMessageSentAt (runTraceMoves r ms).length =
            some opkTerm := by
        dsimp only [pre, List.map, stepToMove]
        rw [Symbolic.Swarm.Leaves.IC12Stage1MP.runTrace_snoc]
        exact Symbolic.Swarm.CREF.getMessageSentAt_attackerSend _ _
      refine ⟨pre, some (runTraceMoves r ms).length, some opkTerm,
        Or.inr ⟨opkTerm, rfl, hknows⟩, ?_, ?_, ?_⟩
      · dsimp only [pre, List.map, stepToMove]
        simp only [Symbolic.Swarm.CREF.NetOpt,
          Symbolic.Swarm.Leaves.IC12Stage1MP.runTrace_snoc,
          Symbolic.Swarm.Leaves.IC12Stage1MP.attackerSend_next]
        exact Symbolic.Swarm.CREF.at?_append_self _ _
      · dsimp only [Option.all, opkTerm, Symbolic.Swarm.CREF.compHwLit]
        rw [hlowLit]; rfl
      · intro g' haddr hσ
        have hC' := compat_of_sigma_eq_lt hNe (ms ++ pre.map stepToMove) hC₀ haddr hσ
        rw [received_setupHandles_some r (ms ++ pre.map stepToMove) hNe hsent]
        refine ⟨bundleCore_of_honestBundle interp' r hNe _ g' hC' bundle hhon hok.bundle_len,
          h1, ?_⟩
        dsimp only [opkTerm]
        rw [Symbolic.Swarm.CREF.gamma_compHwLit]
        exact hslice

private theorem bytesMatchEntry_rng_iff_eventMatchesEntry
    (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (b : HwBytes) (v : VisEntry) (hv : v.layout ≠ .preKeySend)
    (hv2 : ∀ eks, v.layout ≠ .preKeyInner eks) :
    BytesMatchEntry interp r S g .rng b v ↔
      EventMatchesEntry interp r S g (.rng b) v := by
  unfold BytesMatchEntry EventMatchesEntry
  cases h : v.layout
  case preKeyInner eks => exact absurd h (hv2 eks)
  all_goals simp_all [eventKind, eventBytes]

private theorem forall₂_bytesMatchEntry_rng_iff_eventMatchesEntry
    (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    {ps : List HwBytes} {ws : List VisEntry} (hws : ∀ w ∈ ws, w.layout ≠ .preKeySend)
    (hws2 : ∀ w ∈ ws, ∀ eks, w.layout ≠ .preKeyInner eks) :
    List.Forall₂ (fun p w => BytesMatchEntry interp r S g .rng p w) ps ws ↔
      List.Forall₂ (EventMatchesEntry interp r S g) (ps.map MachineEvent.rng) ws := by
  rw [List.forall₂_map_left_iff]
  constructor <;> intro hf
  · induction hf with
    | nil => exact .nil
    | @cons p w ps ws h _ ih =>
      exact .cons ((bytesMatchEntry_rng_iff_eventMatchesEntry interp r S g p w
        (hws w (List.mem_cons_self ..)) (hws2 w (List.mem_cons_self ..))).mp h)
        (ih (fun u hu => hws u (List.mem_cons_of_mem _ hu))
            (fun u hu => hws2 u (List.mem_cons_of_mem _ hu)))
  · induction hf with
    | nil => exact .nil
    | @cons p w ps ws h _ ih =>
      exact .cons ((bytesMatchEntry_rng_iff_eventMatchesEntry interp r S g p w
        (hws w (List.mem_cons_self ..)) (hws2 w (List.mem_cons_self ..))).mpr h)
        (ih (fun u hu => hws u (List.mem_cons_of_mem _ hu))
            (fun u hu => hws2 u (List.mem_cons_of_mem _ hu)))

private theorem randTerm_inj {i₁ n₁ i₂ n₂ : Nat} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (h : randTerm i₁ n₁ = randTerm i₂ n₂) : i₁ = i₂ ∧ n₁ = n₂ := by
  let gA : Ghost := ⟨fun i n => if i = i₁ ∧ n = n₁ then [1#8] else [], fun _ => []⟩
  let interp₀ : ExternInterpretation := fun _ _ => none
  let S₀ : OpaqueSymbolSemantics := ⟨fun _ _ => [], fun _ _ _ => [], fun _ _ => [], fun _ _ => [], fun _ _ => [],
    fun _ _ => [], fun _ _ => [], fun _ => [], fun _ _ => [], fun _ => [],
    fun _ _ _ => []⟩
  have heq := congrArg (gamma interp₀ S₀ gA) h
  rw [gamma_randTerm_eq interp₀ S₀ gA i₁ n₁ hn₁,
    gamma_randTerm_eq interp₀ S₀ gA i₂ n₂ hn₂] at heq
  dsimp only [gA] at heq
  have h₁ : (if i₁ = i₁ ∧ n₁ = n₁ then ([1#8] : HwBytes) else []) = [1#8] := by simp
  rw [h₁] at heq
  split at heq
  · next h₂ => exact ⟨h₂.1.symm, h₂.2.symm⟩
  · cases heq

private theorem ghostWF_init_draws {g' : Ghost} {vis₀ : List VisEntry}
    (hg₀ : GhostWF g' vis₀) {ts : Nat} {ds : List HwBytes}
    (hds : ds.map List.length = initiateFullDrawLengths)
    (hσ0 : g'.σ ts 32 = ds.getD 0 [])
    (hσ1 : g'.σ (ts + 1) 32 = entropyBytes ds)
    (hσ2 : g'.σ (ts + 2) 32 = ds.getD 33 [])
    (inp : VisEntry) (hinp : inp.kind = .recv) :
    GhostWF g' (vis₀ ++ (inp ::
      (rngEntry (randTerm ts 32) :: kyberCoinEntries (randTerm (ts + 1) 32) ++
        [{ rngEntry (randTerm (ts + 2) 32) with anchor := some (ts + 5) }]))) := by
  have hd0_len : (ds.getD 0 []).length = 32 := by
    have h := congrArg (fun l : List Nat => l[0]?) hds
    simp [initiateFullDrawLengths] at h
    rcases h0 : ds[0]? with _ | d0 <;> simp [List.getD_eq_getElem?_getD, h0] at h ⊢
    exact h
  have hd33_len : (ds.getD 33 []).length = 32 := by
    have h := congrArg (fun l : List Nat => l[33]?) hds
    simp [initiateFullDrawLengths] at h
    rcases h33 : ds[33]? with _ | d33 <;> simp [List.getD_eq_getElem?_getD, h33] at h ⊢
    exact h
  have hent_len : (entropyBytes ds).length = 32 := Symbolic.Swarm.CREF.length_entropyBytes ds
  refine ⟨fun v hv hk i n hn hmem => ?_, hg₀.2.1, fun v hv hk => ?_⟩
  · rcases List.mem_append.mp hv with hv₀ | hv₁
    · exact hg₀.1 v hv₀ hk i n hn hmem
    · rcases List.mem_cons.mp hv₁ with rfl | hv_drs
      · rw [hinp] at hk; cases hk
      · simp only [List.cons_append, List.mem_cons, List.mem_append] at hv_drs
        rcases hv_drs with rfl | hv_kc | rfl | hv_nil
        · simp only [rngEntry, List.mem_singleton] at hmem
          obtain ⟨rfl, rfl⟩ := randTerm_inj hn (by decide) hmem
          rw [hσ0, hd0_len]
        · unfold kyberCoinEntries at hv_kc
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv_kc
          simp only [List.mem_singleton] at hmem
          obtain ⟨rfl, rfl⟩ := randTerm_inj hn (by decide) hmem
          rw [hσ1, hent_len]
        · simp only [rngEntry, List.mem_singleton] at hmem
          obtain ⟨rfl, rfl⟩ := randTerm_inj hn (by decide) hmem
          rw [hσ2, hd33_len]
        · nomatch hv_nil
  · rcases List.mem_append.mp hv with hv₀ | hv₁
    · exact hg₀.2.2 v hv₀ hk
    · rcases List.mem_cons.mp hv₁ with rfl | hv_drs
      · rw [hinp] at hk; cases hk
      · simp only [List.cons_append, List.mem_cons, List.mem_append] at hv_drs
        rcases hv_drs with rfl | hv_kc | rfl | hv_nil
        · cases hk
        · unfold kyberCoinEntries at hv_kc
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv_kc
          cases hk
        · cases hk
        · nomatch hv_nil

private theorem explains_init_exit0 {interp' : ExternInterpretation}
    (hext' : ExternContractsHoldCli interp') {r : ProtocolSetup} (hr : ProtocolSetupWF r)
    {g₀ : Ghost} {ss₀ : List Step} {vis₀ : List VisEntry} {evs_pre : List CliEvent}
    (hex₀ : ExplainsClassical interp' r (compSemOf interp' r) g₀ ss₀ vis₀ evs_pre)
    (hnrc₀ : ¬ ReadCollisionCliClassical interp' r (compSemOf interp' r) g₀ ss₀ evs_pre)
    {ev : RunEvent} {blob : HwBytes}
    (hev_party : ev.party = r.alice)
    (hev_cmd : ev.cmd = .init (peerOf r r.alice) bundleDir)
    (hev_in : ev.input = blob)
    (hev_exit : ev.exit = some (0, []))
    (hcoins : ev.coins.length = initiateTapeLen)
    (hhon : HonestBundle interp' r blob)
    (hbin : IniOkBin blob (Slots.initiateDrawsOfCoins ev.coins)) :
    let S := compSemOf interp' r
    ∃ g' ss' vis',
      ExplainsClassical interp' r S g' ss' vis' (evs_pre ++ [.run ev]) ∧
      ¬ ReadCollisionCliClassical interp' r S g' ss' (evs_pre ++ [.run ev]) := by
  intro S
  let ds := Slots.initiateDrawsOfCoins ev.coins
  let ms₀ := ss₀.map stepToMove
  have htr₀_eq : runTrace r ss₀ = runTraceMoves r ms₀ :=
    runTrace_eq_runTraceMoves r (matchesEvents_stepHasMove hex₀.2.2.2)
  obtain ⟨pre, oi, opk, hpre_shape, hopk, hlow, hBM⟩ :=
    opkChoice_steps hext' hr hex₀.1 ms₀ hhon hbin
  have hpre_inv : ∀ x ∈ pre, x.cls = .invisible := by
    rcases hpre_shape with rfl | ⟨t, rfl, _⟩ <;> simp [Step.cls]
  have hpre_hm : ∀ x ∈ pre, StepHasMove x := fun x hx => Or.inl (hpre_inv x hx)
  let ms₁ := ms₀ ++ pre.map stepToMove
  have htr_pre_eq : runSteps pre (runTrace r ss₀) = runTraceMoves r ms₁ := by
    rw [← Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
    have hall : ∀ x ∈ ss₀ ++ pre, StepHasMove x := by
      intro x hx
      rcases List.mem_append.mp hx with hx₀ | hx₁
      · exact matchesEvents_stepHasMove hex₀.2.2.2 x hx₀
      · exact hpre_hm x hx₁
    rw [runTrace_eq_runTraceMoves r hall, List.map_append]
  let tr := runTraceMoves r ms₁
  let ts := tr.length
  let g₁ : Ghost := { g₀ with σ := TR.FreshSigma.updateFreshAt g₀.σ ts 32 (ds.getD 0 []) }
  let g₂ : Ghost := { g₁ with σ := TR.FreshSigma.updateFreshAt g₁.σ (ts + 1) 32 (entropyBytes ds) }
  let g' : Ghost := { g₂ with σ := TR.FreshSigma.updateFreshAt g₂.σ (ts + 2) 32 (ds.getD 33 []) }
  have hσ_lt : ∀ i j, i < ts → g'.σ i j = g₀.σ i j := by
    intro i j hi; dsimp only [g', g₂, g₁, TR.FreshSigma.updateFreshAt]
    split_ifs with h2 h1 h0
    · exact absurd h2.1 (by omega)
    · exact absurd h1.1 (by omega)
    · exact absurd h0.1 (by omega)
    · rfl
  have hσ0 : g'.σ ts 32 = ds.getD 0 [] := by
    dsimp only [g', g₂, g₁, TR.FreshSigma.updateFreshAt]; split_ifs with h2 h1 h0
    · exact absurd h2.1 (by omega)
    · exact absurd h1.1 (by omega)
    · rfl
    · exact absurd ⟨rfl, rfl⟩ h0
  have hσ1 : g'.σ (ts + 1) 32 = entropyBytes ds := by
    dsimp only [g', g₂, TR.FreshSigma.updateFreshAt]; split_ifs with h2 h1
    · exact absurd h2.1 (by omega)
    · rfl
    · exact absurd ⟨rfl, rfl⟩ h1
  have hσ2 : g'.σ (ts + 2) 32 = ds.getD 33 [] := by
    dsimp only [g', TR.FreshSigma.updateFreshAt]; split_ifs with h2
    · rfl
    · exact absurd ⟨rfl, rfl⟩ h2
  have hlen₀_le_ts : (runTrace r ss₀).length ≤ ts := by
    have hle := runSteps_le pre (runTrace r ss₀); rw [htr_pre_eq] at hle
    exact _root_.DY.Trace.length_le _ _ hle
  have hfr : CBadSigmaFrame g₀ g' ts := ⟨fun i hi n => hσ_lt i n hi, rfl⟩
  have hReach_setup : (setupTrace r).Reachable reachability := hex₀.2.2.1.2.1
  have hwf₀ : StepsWF ss₀ (setupTrace r) := hex₀.2.2.1.2.2.1
  have hReach₀ : (runTrace r ss₀).Reachable reachability := runSteps_reachable ss₀ hReach_setup hwf₀
  have htr₀_lt := TR.FreshSigma.traceEntriesLt_of_reachable interp' S g₀ ts hReach₀ hlen₀_le_ts
  have hvis₀_lt := matchesEvents_visStampsLt hex₀.2.2.2 hReach_setup hwf₀ hlen₀_le_ts htr₀_lt
  have hgwf₀' : GhostWF g' vis₀ := ghostWF_transfer hfr hvis₀_lt hex₀.2.1
  have hme₀' : MatchesEventsClassical interp' r S g' (setupTrace r) ss₀ evs_pre vis₀ :=
    matchesEvents_transfer hfr hex₀.2.2.2 hReach_setup hwf₀ hlen₀_le_ts
  have hC' : GhostAndSemMatchSetup interp' r S g' := compat_of_sigma_eq_lt hr.1 ms₁ hex₀.1 rfl hσ_lt
  let bh : BundleHandles := { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := oi }
  let s := Step.aliceStart r.alice r.bob 4 6 bh
  obtain ⟨hs_ok, hs_view⟩ := aliceStart_ok_and_stepView hr.1 hopk hlow (runWrapped ev)
  let inp : VisEntry := ⟨.recv, received tr ([14, 15, 20, 21] ++ oi.toList), .bundle, none⟩
  let drs : List VisEntry :=
    rngEntry (randTerm ts 32) :: kyberCoinEntries (randTerm (ts + 1) 32) ++
      [{ rngEntry (randTerm (ts + 2) 32) with anchor := some (ts + 5) }]
  have hfor_ev := ini_forall₂_initiate_rng_34 interp' r S g' ts ds hbin.lens hσ0 hσ1 hσ2
  have hdrs_lay : ∀ w ∈ drs, w.layout ≠ .preKeySend := by
    intro w hw
    simp only [drs, List.cons_append, List.mem_cons, List.mem_append] at hw
    rcases hw with rfl | hkc | rfl | hnil
    · intro h; cases h
    · unfold kyberCoinEntries at hkc
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hkc
      intro h; cases h
    · intro h; cases h
    · nomatch hnil
  have hdrs_lay2 : ∀ w ∈ drs, ∀ eks, w.layout ≠ .preKeyInner eks := by
    intro w hw eks
    simp only [drs, List.cons_append, List.mem_cons, List.mem_append] at hw
    rcases hw with rfl | hkc | rfl | hnil
    · intro h; cases h
    · unfold kyberCoinEntries at hkc
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hkc
      intro h; cases h
    · intro h; cases h
    · nomatch hnil
  have hfor_rng : List.Forall₂ (fun p w => BytesMatchEntry interp' r S g' .rng p w) ds drs :=
    (forall₂_bytesMatchEntry_rng_iff_eventMatchesEntry interp' r S g' hdrs_lay hdrs_lay2).mpr hfor_ev
  have hrm : RunMatches interp' r S g' (runSteps pre (runTrace r ss₀)) s ev (inp :: drs) (activeBundleIds evs_pre) := by
    rw [htr_pre_eq]
    refine ⟨rfl, by simp [s, Step.party?, hev_party], by simp [s, hev_cmd, Step.FitsCmd],
      by simp [s, Step.MatchesSetupPeer], hs_ok, ⟨[], hev_exit⟩, hs_view.symm, inp, drs, [],
      congrArg (inp :: ·) (List.append_nil drs).symm, ?_, ?_, ?_, trivial, fun _ _ => trivial⟩
    · simp only [inputKind, hev_cmd, hev_in, BytesMatchEntry, inp]; exact ⟨trivial, hBM g' rfl hσ_lt⟩
    · exact ⟨ds, Slots.initiateDrawsOfCoins_nonempty hcoins,
        by rw [Slots.initiateDrawsOfCoins_flatten hcoins], hfor_rng⟩
    · unfold OutputsMatch; rw [hev_exit, hev_cmd]; rfl
  have hwf_pre : StepsWF pre (runTrace r ss₀) := by
    rcases hpre_shape with rfl | ⟨t, rfl, hknows⟩
    · trivial
    · exact ⟨htr₀_eq.symm ▸ hknows, trivial, trivial⟩
  have hwf_all : StepsWF (ss₀ ++ pre ++ [s]) (setupTrace r) := by
    rw [List.append_assoc, stepsWF_append_iff]; refine ⟨hwf₀, ?_⟩
    rw [stepsWF_append_iff]; exact ⟨hwf_pre, trivial, trivial, trivial⟩
  have hsf_all : StepsStateFaithful r (ss₀ ++ pre ++ [s]) := by
    rw [List.append_assoc]; refine stepsStateFaithful_append_noLoad hex₀.2.2.1.2.2.2 fun x hx => ?_
    rcases List.mem_append.mp hx with hx_pre | hx_s
    · rcases hpre_shape with rfl | ⟨t, rfl, _⟩
      · cases hx_pre
      · simp at hx_pre; subst hx_pre; rfl
    · simp at hx_s; subst hx_s; rfl
  have hmrun' : ModelRunWF r (ss₀ ++ pre ++ [s]) := ⟨hex₀.2.2.1.1, hReach_setup, hwf_all, hsf_all⟩
  have hgwf' : GhostWF g' (vis₀ ++ (inp :: drs)) := ghostWF_init_draws hgwf₀' hbin.lens hσ0 hσ1 hσ2 inp rfl
  have hme' : MatchesEventsClassical interp' r S g' (setupTrace r) (ss₀ ++ pre ++ [s])
      (evs_pre ++ [.run ev]) (vis₀ ++ (inp :: drs)) :=
    matchesEvents_snoc_run1 hme₀' hpre_inv hrm
  have hnrc' : ¬ ReadCollisionCliClassical interp' r S g' (ss₀ ++ pre ++ [s]) (evs_pre ++ [.run ev]) := by
    rw [List.append_assoc]
    refine not_readCollisionCli_snoc_noDecrypt hfr hex₀.2.2.1 hlen₀_le_ts (fun x hx => ?_) ?_ hnrc₀
    · rcases List.mem_append.mp hx with hx_pre | hx_s
      · rcases hpre_shape with rfl | ⟨t, rfl, _⟩
        · cases hx_pre
        · simp at hx_pre; subst hx_pre; rfl
      · simp at hx_s; subst hx_s; rfl
    · intro _ _ hcmd; rw [hev_cmd] at hcmd; cases hcmd
  exact ⟨g', ss₀ ++ pre ++ [s], vis₀ ++ (inp :: drs), ⟨hC', hgwf', hmrun', hme'⟩, hnrc'⟩

/-! ## `AliceRecordPendingInSession` on Exit-0 `init` -/

private theorem eq_of_map_length_eq_and_flatten_eq :
    ∀ {l₁ l₂ : List HwBytes},
      l₁.map List.length = l₂.map List.length →
      l₁.flatten = l₂.flatten →
      l₁ = l₂
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, hflat => by
    simp only [List.map_cons, List.cons.injEq] at hlen
    simp only [List.flatten_cons] at hflat
    obtain ⟨hxy, hxs⟩ := List.append_inj hflat hlen.1
    exact congrArg₂ List.cons hxy (eq_of_map_length_eq_and_flatten_eq hlen.2 hxs)

private theorem eq_of_map_length_eq_and_flatten_prefix {l₁ l₂ : List HwBytes}
    (hlen : l₁.map List.length = l₂.map List.length)
    (hpref : l₁.flatten <+: l₂.flatten) : l₁ = l₂ := by
  obtain ⟨rest, hrest⟩ := hpref
  have hlen_fl : l₁.flatten.length = l₂.flatten.length := by
    rw [List.length_flatten, List.length_flatten, hlen]
  have hrest_len : rest.length = 0 := by
    have h := congrArg List.length hrest
    rw [List.length_append] at h
    omega
  rw [List.eq_nil_of_length_eq_zero hrest_len, List.append_nil] at hrest
  exact eq_of_map_length_eq_and_flatten_eq hlen hrest

private def initDrawExpectedLen (w : VisEntry) : Nat :=
  match w.layout with
  | .kyberCoin _ => 4
  | _ => 32

private theorem draws_eq_ds_of_drawsMatch {interp' : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {vis₁ : List VisEntry} {inp : VisEntry} {ts : Nat}
    {pieces : List HwBytes} {coins : HwBytes}
    (hcoins : coins.length = initiateTapeLen)
    (hgwf : GhostWF g (vis₁ ++ (inp ::
      (rngEntry (randTerm ts 32) :: kyberCoinEntries (randTerm (ts + 1) 32) ++
        [{ rngEntry (randTerm (ts + 2) 32) with anchor := some (ts + 5) }]))))
    (hpref : pieces.flatten <+: coins)
    (hfor : List.Forall₂ (fun p w => BytesMatchEntry interp' r S g .rng p w) pieces
      (rngEntry (randTerm ts 32) :: kyberCoinEntries (randTerm (ts + 1) 32) ++
        [{ rngEntry (randTerm (ts + 2) 32) with anchor := some (ts + 5) }])) :
    pieces = Slots.initiateDrawsOfCoins coins := by
  set drs := rngEntry (randTerm ts 32) :: kyberCoinEntries (randTerm (ts + 1) 32) ++
    [{ rngEntry (randTerm (ts + 2) 32) with anchor := some (ts + 5) }]
  have hσ0_len : (g.σ ts 32).length = 32 :=
    hgwf.1 (rngEntry (randTerm ts 32))
      (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      rfl ts 32 (by decide) (List.mem_singleton_self _)
  have hσ2_len : (g.σ (ts + 2) 32).length = 32 :=
    hgwf.1 { rngEntry (randTerm (ts + 2) 32) with anchor := some (ts + 5) }
      (List.mem_append_right _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))))
      rfl (ts + 2) 32 (by decide) (List.mem_singleton_self _)
  have hmap_drs : drs.map initDrawExpectedLen = initiateFullDrawLengths := rfl
  have hfor_len : ∀ {ps : List HwBytes} {ws : List VisEntry},
      (∀ w ∈ ws, w ∈ drs) →
      List.Forall₂ (fun p w => BytesMatchEntry interp' r S g .rng p w) ps ws →
      ps.map List.length = ws.map initDrawExpectedLen := by
    intro ps ws hsub hf
    induction hf with
    | nil => rfl
    | @cons p w ps ws hbm _ ih =>
      refine congrArg₂ List.cons ?_ (ih fun u hu => hsub u (List.mem_cons_of_mem _ hu))
      have hmem := hsub w (List.mem_cons_self ..)
      simp only [drs, List.cons_append, List.mem_cons, List.mem_append] at hmem
      rcases hmem with rfl | hkc | rfl | hnil
      · rcases hbm with ⟨_, hlay⟩
        simp only [rngEntry, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hlay
        rw [← hlay, gamma_randTerm_eq interp' S g ts 32 (by decide), hσ0_len]; rfl
      · unfold kyberCoinEntries at hkc
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hkc
        exact hbm.2.1
      · rcases hbm with ⟨_, hlay⟩
        simp only [rngEntry, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hlay
        rw [← hlay, gamma_randTerm_eq interp' S g (ts + 2) 32 (by decide), hσ2_len]; rfl
      · nomatch hnil
  have hmap_pieces : pieces.map List.length = drs.map initDrawExpectedLen :=
    hfor_len (fun _ hw => hw) hfor
  have hlen_ds : pieces.map List.length = (Slots.initiateDrawsOfCoins coins).map List.length := by
    rw [hmap_pieces, hmap_drs, (Slots.initiateDrawsOfCoins_lengths hcoins).symm]
  have hpref_ds : pieces.flatten <+: (Slots.initiateDrawsOfCoins coins).flatten := by
    rwa [Slots.initiateDrawsOfCoins_flatten hcoins]
  exact eq_of_map_length_eq_and_flatten_prefix hlen_ds hpref_ds

private theorem aliceRecordPending_init_exit0 {interp' : ExternInterpretation}
    (hext' : ExternContractsHoldCli interp') {r : ProtocolSetup} (hr : ProtocolSetupWF r)
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs_pre : List CliEvent}
    {ev : RunEvent} {blob recState : HwBytes} {records : Participant → Option HwBytes}
    (hex : ExplainsClassical interp' r (compSemOf interp' r) g ss vis (evs_pre ++ [.run ev]))
    (hev_party : ev.party = r.alice)
    (hev_cmd : ev.cmd = .init (peerOf r r.alice) bundleDir)
    (hev_in : ev.input = blob)
    (hev_exit : ev.exit = some (0, []))
    (hcoins : ev.coins.length = initiateTapeLen)
    (hhon : HonestBundle interp' r blob)
    (hbin : IniOkBin blob (Slots.initiateDrawsOfCoins ev.coins))
    (hV1 : IniPure.AliceInitiatedV1PostPure interp' r blob (Slots.initiateDrawsOfCoins ev.coins) recState)
    (hleak : records r.alice = some recState) :
    AliceRecordPendingInSession interp' r (compSemOf interp' r) g (runTrace r ss) records
      (activeBundleIds (evs_pre ++ [.run ev])) := by
  let S := compSemOf interp' r
  let ds := Slots.initiateDrawsOfCoins ev.coins
  obtain ⟨ss₁, pre, s, post, vis₁, v, rfl, rfl, hm₁, hpre_inv, hrm, hpost_inv⟩ :=
    matchesEvents_snoc_run_inv (fun hrej => hrej [] hev_exit) evs_pre hex.2.2.2
  obtain ⟨_, hparty, hfits, hpeer, hs_ok, _, hv_eq, inp, drs, outs,
    hv_split, hbm_in, hdm, hom, _, _⟩ := hrm
  cases s with
  | aliceStart a b idStateIdx regIdxB bh =>
  simp only [Step.party?, hev_party, Option.some.injEq] at hparty
  subst hparty
  simp only [Step.MatchesSetupPeer] at hpeer
  subst hpeer
  simp only [OutputsMatch, hev_exit, hev_cmd] at hom
  subst hom
  rw [List.append_nil] at hv_split
  subst hv_split
  let tr := runSteps pre (runSteps ss₁ (setupTrace r))
  obtain ⟨ikA', ikB', spk', pqpk', opk', _, hnext_ini⟩ := aliceStart_ok_eq_iniAliceStartTr hs_ok
  have hnext_mv : (Step.aliceStart r.alice r.bob idStateIdx regIdxB bh).next tr =
      (Move.aliceStart r.alice r.bob idStateIdx regIdxB bh 35).next tr :=
    (stepToMove_next (Or.inr (Or.inl rfl)) tr).symm
  have hlen_next : ((Move.aliceStart r.alice r.bob idStateIdx regIdxB bh 35).next tr).length =
      tr.length + 9 := by
    rw [← hnext_mv, hnext_ini]
    unfold iniAliceStartTr
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    dsimp only [tr]
  rcases aliceStart_next_cases r.alice r.bob idStateIdx regIdxB bh 35 tr with hmv_id | hmv_rnd |
    ⟨ikA, ikB, vkB, spk, spkSig, pqpk, pqpkSig, opk, honest,
      _, _, hspk_msg, hspkSig_msg, hpq_msg, hpqSig_msg, hopkH, hnext_ok⟩
  · rw [hmv_id] at hlen_next; omega
  · rw [hmv_rnd] at hlen_next; simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hlen_next; omega
  · let o := aliceOut tr ikA ikB spk pqpk opk
    have hdef_ini : aliceStartTrOfOut tr r.alice r.bob o = iniAliceStartTr tr r.alice r.bob o := rfl
    have hs_next : (Step.aliceStart r.alice r.bob idStateIdx regIdxB bh).next tr =
        iniAliceStartTr tr r.alice r.bob o := by
      rw [hnext_mv, hnext_ok, hdef_ini]
    let inp₀ : VisEntry :=
      ⟨.recv, received tr ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList), .bundle, none⟩
    let drs₀ : List VisEntry :=
      rngEntry (randTerm tr.length 32) :: kyberCoinEntries (randTerm (tr.length + 1) 32) ++
        [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }]
    have hs_ok' : (Step.aliceStart r.alice r.bob idStateIdx regIdxB bh).ok tr = true := hs_ok
    have hview_eq : stepView (Step.aliceStart r.alice r.bob idStateIdx regIdxB bh) tr (runWrapped ev) =
        inp₀ :: drs₀ := by
      unfold stepView
      simp only [hs_ok', ↓reduceIte]
      rw [hs_next, Symbolic.Swarm.CREF.exposures_iniAliceStartTr, List.append_nil]
      unfold aliceVis
      rw [Symbolic.Swarm.CREF.newRandoms_iniAliceStartTr,
        Symbolic.Swarm.CREF.eventIdx_isAliceDone_iniAliceStartTr]
      rfl
    have hinp_drs : inp :: drs = inp₀ :: drs₀ := hv_eq.trans hview_eq
    obtain ⟨rfl, rfl⟩ := List.cons.inj hinp_drs
    obtain ⟨pieces, _, hpref, hfor⟩ := hdm
    have hpieces_eq : pieces = ds :=
      draws_eq_ds_of_drawsMatch hcoins hex.2.1 hpref hfor
    subst hpieces_eq
    have hdrs₀_lay : ∀ w ∈ drs₀, w.layout ≠ .preKeySend := by
      intro w hw
      simp only [drs₀, List.cons_append, List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | hkc | rfl | hnil
      · intro h; cases h
      · unfold kyberCoinEntries at hkc
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hkc
        intro h; cases h
      · intro h; cases h
      · nomatch hnil
    have hdrs₀_lay2 : ∀ w ∈ drs₀, ∀ eks, w.layout ≠ .preKeyInner eks := by
      intro w hw eks
      simp only [drs₀, List.cons_append, List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | hkc | rfl | hnil
      · intro h; cases h
      · unfold kyberCoinEntries at hkc
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hkc
        intro h; cases h
      · intro h; cases h
      · nomatch hnil
    have hfor_ev : List.Forall₂ (EventMatchesEntry interp' r S g) (ds.map MachineEvent.rng) drs₀ :=
      (forall₂_bytesMatchEntry_rng_iff_eventMatchesEntry interp' r S g hdrs₀_lay hdrs₀_lay2).mp hfor
    obtain ⟨hγ_ek, hγ_e, _⟩ := rng_vis_aliceStart_35 hbin.lens hfor_ev
    have hspk_get := getMessageSentAt_of_netMsgAt hspk_msg
    have hspkSig_get := getMessageSentAt_of_netMsgAt hspkSig_msg
    have hpq_get := getMessageSentAt_of_netMsgAt hpq_msg
    have hpqSig_get := getMessageSentAt_of_netMsgAt hpqSig_msg
    have hrec_eq : received tr ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList) =
        [spk, spkSig, pqpk, pqpkSig] ++ opk.toList := by
      rcases hopkH with ⟨hbh_none, rfl⟩ | ⟨idx, u, hbh_some, rfl, hu_msg⟩
      · simp [received, hbh_none, hspk_get, hspkSig_get, hpq_get, hpqSig_get]
      · have hu_get := getMessageSentAt_of_netMsgAt hu_msg
        simp [received, hbh_some, hspk_get, hspkSig_get, hpq_get, hpqSig_get, hu_get]
    simp only [inputKind, hev_cmd, hev_in, BytesMatchEntry, inp₀] at hbm_in
    have hBM : PreKeyBundleLayoutMatches interp' S g blob ([spk, spkSig, pqpk, pqpkSig] ++ opk.toList) := by
      rw [← hrec_eq]; exact hbm_in.2
    have hγ_pqpk := (bundleMatches_honest hBM hhon).2.1
    let ctB := kemEncapCtBytes interp' (r.opaqueBytes (setupPublic r 6)) (entropyBytes ds)
    have ho_ek_bytes : ecKey (gamma interp' S g o.ek) =
        ecKey (pubBytes interp' (ds.getD 0 [])) := by
      change ecKey (gamma interp' S g (DY.DiffieHellman.dhPk (randTerm tr.length 32))) = _
      rw [TR.gamma_dhPk, hγ_ek]; rfl
    have ho_ct_bytes : kyberKey (gamma interp' S g o.ct) = kyberKey ctB := by
      change kyberKey (gamma interp' S g (DY.PQKem.kemEncap pqpk (randTerm (tr.length + 1) 32)).1) = _
      rw [TR.gamma_kemEncap_fst, hγ_pqpk, hγ_e]; rfl
    have hmrun_all : ModelRunWF r ((ss₁ ++ pre) ++ ([Step.aliceStart r.alice r.bob idStateIdx regIdxB bh] ++ post)) := by
      simpa [List.append_assoc] using hex.2.2.1
    have htr_eq : tr = runTrace r (ss₁ ++ pre) :=
      (Symbolic.Proofs.Swarm.UA.Base.runTrace_append r ss₁ pre).symm
    have hReach_tr : tr.Reachable reachability := by
      rw [htr_eq]
      exact modelRunWF_reachable (modelRunWF_of_append hmrun_all)
    have hall_hm : ∀ x ∈ ss₁ ++ pre, StepHasMove x := by
      intro x hx
      rcases List.mem_append.mp hx with hx₁ | hx_pre
      · exact matchesEvents_stepHasMove hm₁ x hx₁
      · exact Or.inl (hpre_inv x hx_pre)
    have hrole_tr : ∀ (i : Nat) (st : TRState), (tr.at? i : Option TRStEntry) = some ⟨⟨r.alice, st⟩⟩ →
        st.initiator = true := by
      intro i st hat
      rw [htr_eq] at hat
      exact aliceOnlyInitiator_runTrace hr.1 hall_hm st i hat
    have hap_mid : AlicePendingKeysOn interp' S g r.alice
        (runTrace r (ss₁ ++ pre ++ [Step.aliceStart r.alice r.bob idStateIdx regIdxB bh]))
        (ecKey (gamma interp' S g o.ek)) (kyberKey (gamma interp' S g o.ct)) := by
      have htr_mid : runTrace r (ss₁ ++ pre ++ [Step.aliceStart r.alice r.bob idStateIdx regIdxB bh]) =
          iniAliceStartTr tr r.alice r.bob o := by
        rw [Symbolic.Proofs.Swarm.UA.Base.runTrace_append, ← htr_eq]
        exact hs_next
      rw [htr_mid]
      exact alicePendingKeysOn_iniAliceStartTr o (handshakeSessionValid_reachable hReach_tr) hrole_tr
    have hap_end : AlicePendingKeysOn interp' S g r.alice
        (runTrace r (ss₁ ++ pre ++ [Step.aliceStart r.alice r.bob idStateIdx regIdxB bh] ++ post))
        (ecKey (gamma interp' S g o.ek)) (kyberKey (gamma interp' S g o.ct)) :=
      alicePendingKeysOn_of_matchesEvents (initIds := none) hr hex.2.2.1 (.nil hpost_inv) (by intro _ h; cases h) hap_mid
    obtain ⟨ourIdentity, theirIdentity, theirRatchetKey, baseKey, rk1, ck0,
      sendingKeyPair, ck1, opkId?, spkId, kyberPreKeyId, remoteRegId,
      hcanon₀, _, _, _, _, _, hbaseKey, _, _, _, _, _, _, _, hbids⟩ :=
      IniPure.aliceInitiatedV1_bytes_pure interp' hext'.1 r blob ds recState hV1
    have habi : activeBundleIds (evs_pre ++ [.run ev]) = some (bundlePreKeyIds blob) := by
      rw [← hev_in]
      exact activeBundleIds_snoc_init_ok hev_cmd hev_exit
    intro rec sess hrec hcan
    rw [hleak, Option.some.injEq] at hrec
    subst hrec
    have hsess_eq := Slots.recordCanonical_Q_inj hcanon₀ hcan
    subst hsess_eq
    refine ⟨fun items kpk hp hk => ?_, fun hp_none => ?_⟩
    · simp only [Symbolic.Swarm.CREF.aliceInitiatedSessionV1,
        Symbolic.Swarm.CREF.aliceInitiatedStateV1, Option.some.injEq] at hp hk
      subst hp hk
      dsimp only
      refine ⟨by rw [habi, ← hbids], ?_⟩
      rw [hbaseKey, ← ho_ek_bytes, ← ho_ct_bytes]
      exact hap_end
    · simp [Symbolic.Swarm.CREF.aliceInitiatedSessionV1,
        Symbolic.Swarm.CREF.aliceInitiatedStateV1] at hp_none
  | _ => simp [Step.FitsCmd, hev_cmd] at hfits

/-! ## Main Theorem -/

/-- Alice's `init` slot preserves `PqTurnSim1A` and `UAInv`. -/
theorem slot_init_ua : UASlotInitSpec := by
  intro interp P r hext hagree hr t t_clean c inp code out files accepted evs_pre
    hsim halice hcmd hstdin hcoins hrec_none hflat hhon_files hin hRel
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let ev := runEventOf c (some (code, out))
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  obtain ⟨t_clean', accepted', hsim', hwit, hcont⟩ :=
    Symbolic.Swarm.Coinsplit.Lift.L07.slot_init_cli_ua
      Symbolic.Swarm.Coinsplit.Lift.L02.outcomeFaithfulCli_of_goodExit0Cut
      Symbolic.Swarm.Coinsplit.Lift.L04.bridgeB_quiet_fail
      interp P r hext hagree hr (σ_pre := flatEvents evs_pre)
      hsim halice hcmd hstdin hcoins hrec_none hflat hhon_files hin hRel
  refine ⟨t_clean', accepted', hsim', ?_⟩
  intro who ok hsched hinv
  rcases hinv with hcol | ⟨hlive₀, _, hex₀⟩
  · exact Or.inl (collisionAtCli_append _ hcol)
  · right
    have hfs : failedSend ev = false := by
      by_cases h : failedSend ev = true
      · obtain ⟨⟨peer, hsend⟩, _⟩ := (failedSend_runEventOf c code out).mp h
        rw [hcmd] at hsend; cases hsend
      · exact Bool.not_eq_true _ |>.mp h
    have hcalls : callsOf (evs_pre ++ [.run ev]) =
        callsOf evs_pre ++ [(c.party, decide (code = 0))] := by
      rw [callsOf_append, callsOf_run_call c code out hfs]
    let k := (callStarts (flatEvents evs_pre)).length
    have hk_eq : k = (callsOf evs_pre).length := callStarts_flatEvents_length evs_pre
    have hcall_k : (callsOf (evs_pre ++ [.run ev]))[k]? = some (c.party, decide (code = 0)) := by
      rw [hcalls, hk_eq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    have hwho_k : who[k]? = some c.party := by
      obtain ⟨rest_who, hwho_eq⟩ := hsched.1
      have hmap_k := congrArg (fun l : List Participant => l[k]?) hwho_eq
      have hlt : k < ((callsOf (evs_pre ++ [.run ev])).map Prod.fst).length := by
        rw [List.length_map, hcalls, List.length_append, List.length_singleton, hk_eq]
        omega
      rw [List.getElem?_append_left hlt] at hmap_k
      rw [← hmap_k, List.getElem?_map, hcall_k]
      rfl
    have hok_k : ok k = decide (code = 0) := hsched.2 k c.party (decide (code = 0)) hcall_k
    have hflat_eq : flatEvents (evs_pre ++ [.run ev]) =
        flatEvents evs_pre ++ (cliEntryEvents c ++ cliExitEvents c code out) := by
      rw [flatEvents_append, flatEvents_run_call c code out hfs]
    have hlive' : CliLiveAtCli interp' r S who ok t_clean' accepted'
        (flatEvents (evs_pre ++ [.run ev])) := by
      rw [hflat_eq]
      exact hcont who ok hwho_k hlive₀ hok_k
    obtain ⟨g₀, ss₀, vis₀, hex₀_e, hnrc₀⟩ := hex₀
    rcases hwit with ⟨rfl, rfl, rfl, hrec_clean⟩ |
      ⟨rfl, rfl, pb, recState, hparse_pb, hhon_pb, hbin_pb, hV1_pb, hleak_pb⟩
    · refine ⟨hlive', ?_, ?_⟩
      · intro g ss vis _ _
        refine aliceRecordPendingInSession_of_no_record ?_
        unfold CliTurn.leakRecords
        simp [hr.1, hrec_clean]
      · have hrej : RunRejected ev := by
          intro out' hout'
          simp [ev, runEventOf] at hout'
        have hfr : CBadSigmaFrame g₀ g₀ (runTrace r ss₀).length := ⟨fun _ _ _ => rfl, rfl⟩
        have hnrc' : ¬ ReadCollisionCliClassical interp' r S g₀ (ss₀ ++ []) (evs_pre ++ [.run ev]) := by
          refine not_readCollisionCli_snoc_noDecrypt hfr hex₀_e.2.2.1 (Nat.le_refl _)
            (by intro _ h; cases h) ?_ hnrc₀
          intro peer _ hcmd'
          simp [ev, runEventOf, hcmd] at hcmd'
        rw [List.append_nil] at hnrc'
        exact ⟨g₀, ss₀, vis₀, explains_snoc_rejected hrej hex₀_e, hnrc'⟩
    · have hev_in : ev.input = bundleBlob pb := by
        simp [ev, runEventOf, runInput, hcmd, hparse_pb]
      refine ⟨hlive', ?_, ?_⟩
      · intro g ss vis hex_post _
        exact aliceRecordPending_init_exit0 hext' hr hex_post
          halice hcmd hev_in rfl hcoins hhon_pb hbin_pb hV1_pb hleak_pb
      · exact explains_init_exit0 hext' hr hex₀_e hnrc₀
          halice hcmd hev_in rfl hcoins hhon_pb hbin_pb

end Symbolic.Proofs.Swarm.UA.SlotInit
