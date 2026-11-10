/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.BI.RAB.Defs
public import Symbolic.Proofs.Swarm.CREF.RecvWire.ReadableBy2Pure
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.Leaks
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureA
import Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey
import Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer
import Symbolic.Proofs.Swarm.UA.BI.G.StepsStateFaithful
import Symbolic.Proofs.Swarm.UA.BI.RAB.Base
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.CREF.CBadG2.Stamps -- shake: keep
import Symbolic.Proofs.Swarm.CREF.CBadReadableBridge -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.StateFaithfulMoves -- shake: keep

/-!
# Shared Whisper Receive Helpers

Provides schedule, flattening, and collision bridges across trace translations, preservation of
`AliceRecordPendingInSession` and `UAInvB` on whisper `recv` steps, and lifting of raw decrypt
witnesses to `ModelAcceptsTermAfterAttackerSends`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.G.RecvStep

open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
cref_hide_foreign_instances

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Trace Traceful ExecTraceTypes TraceEntryHas)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.PQXDH (PQXDHEvent BobKeyHandles PreKeyMsgHandles)
open _root_.DY.Libsignal.TripleRatchet (TRState TREvent isCurrentSnapshot parseTrSignalMsg)
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open _root_.DY.Libsignal.Composed (ComposedEvent reachability)
open _root_.DY.Libsignal.Composed.Refinement (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost Step StepClass VisEntry
  VisEventKind VisByteLayout PreKeyFields PreKeyRep GhostAndSemMatchSetup GhostWF ModelRunWF StepsWF StepsStateFaithful
  Step.PreCond Step.LocalOk Step.next Step.ok Step.cls Step.party? Step.stateLoad?
  Step.decryptMsgIdx? Step.FitsCmd Step.MatchesSetupPeer Step.toInput Step.IsLeak stepIn
  setupTrace setupRandoms runSteps runTrace runMoves runTraceMoves runVis Move ModelRun StateFaithful
  gamma gamma' ecKey kyberKey pendingPreKey sessionHasDecrypted activeBundleIds BundlePreKeyIds stepView runWrapped inputKind
  BytesMatchEntry EventMatchesEntry DrawsMatch OutputsMatch ReadsFaithfully PathFaithfulAt
  RunMatches RunRejected MatchesEvents MatchesEventsAt Explains ExplainsMoves MatchedPrefix
  recvRepresentations recvRepresentationsOn preKeyRepresentations preKeyRepresentationsOn
  KnownBaseKey KnownBaseKeyOn honestSalts honestSaltsOf prefixTerms plaintextTerms
  MemoCollisionOn RecvCollision RecvCollisionOn ReselectCollision ReselectCollisionOn
  BobSessionStartCollidesOrImplicitRejects BobSessionStartCollidesOrImplicitRejectsOn bobDoneBaseKeys parsePreKeyWire ReadCollision
  trialTerms whisperTrials bobTrials MacTagForgeryOrCollision
  callStarts newIndices newRandoms rngEntry receivedPlaintext decVis bobVis bobOpkPk
  exposures isAliceDone randTerm eventKind eventBytes)
open _root_.DY.Libsignal.Composed.Refinement.Cli (CliCall CliTurn cliEntryEvents cliExitEvents
  runEventOf runInput ReadCollisionCli ModelAcceptsTermAfterAttackerSends SignalMsgAcceptedOnlyViaCollision
  PreKeyStartCollidesOrRejects CollisionAfterExplainedPrefix ExplainsCli RecvBody)
open CryptoVerification.SignalSession (Cmd Address)
open CryptoGames.LibsignalSessionApi (Session PendingPreKey PendingKyberPreKey)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry getLocalState_tr_fst at?_le_some at?_append_here at?_append_of_lt)
open Symbolic.Swarm.CREF (CBadSigmaFrame CBadGammaAgree CBadStamps
  cbadG2_gammaAgree_of_sigmaFrame cbadG2_stamps_of_matched cbadG2_stampsLt_getMessageSentAt
  isCurrentSnapshot_of_le_of_lt isCurrentSnapshot_false_of_later bks_lt_length_of_at? bks_getEventAt_of_le
  bks_stored_of_getLocalState stateFaithful_snoc_of_isCurrentSnapshot
  recvCollision_append_one_attackerSend_iff exposures_nil_of_not_leakKind)
open Symbolic.Swarm.CREF.CliPure (cbadG2_recvCollision_transfer)
open Symbolic.Swarm.CREF.TR (normPending normPendingS)
open Symbolic.Swarm.CREF.TR.Pure (WireRecCanon slots_RecordCanonical_Q slots_NonEmptyV1Q)
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure
  (sessionToRecordRecPending recordBytes_sessionToRecordRecPending_of_canonical_Q)
open Symbolic.Swarm.Coinsplit.Lift (CliLiveAtCli)
open Symbolic.Proofs.Swarm.UA.Defs (SchedFits callsOf flatEvents failedSend
  AlicePendingKeysOn AliceRecordPendingInSession)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Defs (UAInvB)
open Symbolic.Proofs.Swarm.UA.Base (callsOf_append callsOf_run_call schedFits_of_append
  flatEvents_append flatEvents_run_call callStarts_flatEvents_length runSteps_append runTrace_append)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Base (explains_snoc_rejected
  )
open Symbolic.Proofs.Swarm.UA.BI.G.StepsStateFaithful (stepsStateFaithful_snoc_of_isCurrentSnapshot_gen)

attribute [local instance 2000]
  _root_.DY.Libsignal.Composed.instBytesFunctor_symbolic _root_.DY.Libsignal.Composed.instBytesLength_symbolic
  _root_.DY.Libsignal.Composed.instAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instExecTraceTypes_symbolic
  _root_.DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instHasExecBytes
  _root_.DY.Libsignal.Composed.instHasExecEntryT _root_.DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  _root_.DY.Libsignal.Composed.instHasExecTrace _root_.DY.Libsignal.Composed.instHasSubF
  _root_.DY.Libsignal.Composed.instHasSubFAttackerKnowledge _root_.DY.Libsignal.Composed.instHasSubFLength

/-! ## Schedule, Flattening, and Collision Bridges -/

theorem schedFits_recv_call {c : CliCall} {peer : Address} {code : Nat} {out : HwBytes}
    {evs_pre : List CliEvent} {who : List Participant} {ok : Nat → Bool}
    (hcmd : c.cmd = .recv peer)
    (hfit : SchedFits (callsOf (evs_pre ++ [.run (runEventOf c (some (code, out)))])) who ok) :
    SchedFits (callsOf evs_pre) who ok ∧
      who[(callStarts (flatEvents evs_pre)).length]? = some c.party ∧
      ok (callStarts (flatEvents evs_pre)).length = decide (code = 0) ∧
      flatEvents (evs_pre ++ [.run (runEventOf c (some (code, out)))]) =
        flatEvents evs_pre ++ (cliEntryEvents c ++ cliExitEvents c code out) := by
  have hfs : failedSend (runEventOf c (some (code, out))) = false := by
    simp [failedSend, runEventOf, hcmd]
  have hcalls : callsOf (evs_pre ++ [.run (runEventOf c (some (code, out)))]) =
      callsOf evs_pre ++ [(c.party, decide (code = 0))] := by
    rw [callsOf_append, callsOf_run_call c code out hfs]
  rw [hcalls] at hfit
  have hlen : (callStarts (flatEvents evs_pre)).length = (callsOf evs_pre).length :=
    callStarts_flatEvents_length evs_pre
  refine ⟨schedFits_of_append hfit, ?_, ?_, ?_⟩
  · rw [hlen]; obtain ⟨rest, hrest⟩ := hfit.1
    rw [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append] at hrest
    rw [← hrest, List.getElem?_append_right (by simp),
      show (callsOf evs_pre).length - ((callsOf evs_pre).map Prod.fst).length = 0 by simp]; rfl
  · rw [hlen]; exact hfit.2 (callsOf evs_pre).length c.party (decide (code = 0))
      (by rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
  · rw [flatEvents_append, flatEvents_run_call c code out hfs]

theorem memoCollisionOn_iff_of_terms {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {known : _root_.DY.Bytes → Prop} {tr : ExecTrace} {vis₁ vis₂ : List VisEntry}
    {newTerms newPts : List _root_.DY.Bytes}
    (hpre : prefixTerms r tr vis₁ = prefixTerms r tr vis₂) (hpt : plaintextTerms vis₁ = plaintextTerms vis₂) :
    MemoCollisionOn interp r S g known tr vis₁ newTerms newPts ↔
      MemoCollisionOn interp r S g known tr vis₂ newTerms newPts := by
  unfold MemoCollisionOn; rw [hpre, hpt]

theorem recvRepresentations_eq_of_trace {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {tr : ExecTrace} {b : HwBytes} (htr : runTraceMoves r ms = tr) :
    recvRepresentations interp r S g ms b = recvRepresentationsOn interp S g tr b := by
  unfold recvRepresentations recvRepresentationsOn; rw [htr]

theorem recvCollision_iff_of_xlate {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {ss : List Step} {vis : List VisEntry} {t : _root_.DY.Bytes}
    (htr : runTraceMoves r ms = runTrace r ss) (hsalts : honestSalts r ms = honestSaltsOf r ss)
    (hpre : prefixTerms r (runTrace r ss) (runVis r ms) = prefixTerms r (runTrace r ss) vis)
    (hpt : plaintextTerms (runVis r ms) = plaintextTerms vis) :
    RecvCollision interp r S g ms t ↔
      RecvCollisionOn interp r S g (runTrace r ss) vis (honestSaltsOf r ss) t := by
  unfold RecvCollision RecvCollisionOn; rw [htr, hsalts]
  cases parseTrSignalMsg t with
  | none => exact memoCollisionOn_iff_of_terms hpre hpt
  | some msg => exact or_congr_left (memoCollisionOn_iff_of_terms hpre hpt)

theorem reselectCollision_iff_of_xlate {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {ss : List Step} {vis : List VisEntry} {t : _root_.DY.Bytes}
    (htr : runTraceMoves r ms = runTrace r ss) (hsalts : honestSalts r ms = honestSaltsOf r ss)
    (hpre : prefixTerms r (runTrace r ss) (runVis r ms) = prefixTerms r (runTrace r ss) vis)
    (hpt : plaintextTerms (runVis r ms) = plaintextTerms vis) :
    ReselectCollision interp r S g ms t ↔
      ReselectCollisionOn interp r S g (runTrace r ss) vis (honestSaltsOf r ss) t := by
  unfold ReselectCollision ReselectCollisionOn
  simp only [recvRepresentations_eq_of_trace htr, recvCollision_iff_of_xlate htr hsalts hpre hpt]
  rw [htr]

/-! ## Pending Session Preservation for Whisper Receive -/

private theorem stepIn_next_eq (c : _root_.DY.ReachabilityConfig)
    [inst : _root_.DY.ReachabilityConfig.HasStep c reachability] (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (inst.pf_step x).symm

private theorem stepIn_ok' (c : _root_.DY.ReachabilityConfig)
    [inst : _root_.DY.ReachabilityConfig.HasStep c reachability] (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => (s.2.run tr).1.isSome) (inst.pf_step x).symm

private def EndsWithLogMKStore (me : Participant) {α : Type} (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, (x.run tr).1.isSome = true →
    ∃ (tr₁ : ExecTrace) (st_new : TRState) (seed pqSalt : _root_.DY.Bytes)
      (n : UInt32) (rIdx par : Nat),
      (x.run tr).2.val =
        (tr₁.append (⟨TREvent.MessageKey (st_new.sessionInfo me) .receiver seed pqSalt n rIdx par⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent)).append
          (⟨⟨me, st_new⟩⟩ : TRStEntry)

private theorem endsWith_failure {me : Participant} {α : Type} :
    EndsWithLogMKStore me (failure : Traceful α) := fun _ hok => by cases hok

private theorem endsWith_bind {me : Participant} {α β : Type} (x : Traceful α) {f : α → Traceful β}
    (hf : ∀ a, EndsWithLogMKStore me (f a)) : EndsWithLogMKStore me (x >>= f) := by
  intro tr hok
  rw [Symbolic.Swarm.CREF.TR.run_bind_snd]
  rw [_root_.DY.Traceful.run_bind] at hok
  rcases hx : x.run tr with ⟨_ | a, tr'⟩
  · simp [hx] at hok
  · rw [hx] at hok
    refine hf a tr'.val ?_
    rcases hfa : (f a).run tr'.val with ⟨_ | _, _⟩
    · simp [hfa] at hok
    · rfl

private theorem endsWith_guard {me : Participant} {β : Type} (P : Prop) [Decidable P]
    {f : Unit → Traceful β} (hf : P → EndsWithLogMKStore me (f ())) :
    EndsWithLogMKStore me ((_root_.guard P : Traceful Unit) >>= f) := by
  intro tr hok
  unfold _root_.guard at hok ⊢
  by_cases hP : P
  · simp only [hP, ↓reduceIte] at hok ⊢
    exact endsWith_bind (pure ()) (fun _ => hf hP) tr hok
  · simp only [hP, ↓reduceIte] at hok
    cases hok

private theorem endsWith_leaf {me : Participant} {s : _root_.DY.Libsignal.TripleRatchet.SessionInfo}
    {seed pqSalt : _root_.DY.Bytes} {n : UInt32} {rIdx par : Nat} {st_new : TRState}
    (hs : s = st_new.sessionInfo me) :
    EndsWithLogMKStore me (_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
      me s .receiver seed pqSalt n rIdx par st_new) := by
  intro tr _
  subst hs
  exact ⟨tr, st_new, seed, pqSalt, n, rIdx, par,
    Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logMessageKeyAndStore_snd _ _ _ _ _ _ _ _ _ _⟩

private theorem decrypt_ok_ends_with_logMKStore {s : Step} {me : Participant} {tr : ExecTrace}
    (hs : (∃ stateIdx msgIdx pqIdx spqrMsgIdx,
        s = .messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) ∨
      (∃ stateIdx msgIdx skIdx pqIdx spqrMsgIdx,
        s = .messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx))
    (hok : s.ok tr = true) :
    ∃ (tr₁ : ExecTrace) (st_new : TRState) (seed pqSalt : _root_.DY.Bytes)
      (n : UInt32) (rIdx par : Nat),
      s.next tr =
        (tr₁.append (⟨TREvent.MessageKey (st_new.sessionInfo me) .receiver seed pqSalt n rIdx par⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent)).append
          (⟨⟨me, st_new⟩⟩ : TRStEntry) := by
  rcases hs with ⟨stateIdx, msgIdx, pqIdx, spqrMsgIdx, rfl⟩ |
    ⟨stateIdx, msgIdx, skIdx, pqIdx, spqrMsgIdx, rfl⟩
  · have hnext : (Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).next tr =
        ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val :=
      stepIn_next_eq _root_.DY.Libsignal.TripleRatchet.messageDecrypt.reachability
        (me, stateIdx, msgIdx, pqIdx, spqrMsgIdx) tr
    have hok' : ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).1.isSome = true :=
      (stepIn_ok' _root_.DY.Libsignal.TripleRatchet.messageDecrypt.reachability
        (me, stateIdx, msgIdx, pqIdx, spqrMsgIdx) tr) ▸ hok
    rw [hnext]
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline] at hok' ⊢
    refine (endsWith_bind _ fun st => endsWith_bind _ fun msg =>
      endsWith_bind _ fun ⟨st, c, ratcheted⟩ => ?_) tr hok'
    dsimp only; split
    · split
      · refine endsWith_bind _ fun _ => endsWith_bind _ fun _ => endsWith_bind _ fun _ => ?_
        split
        · exact endsWith_bind _ fun _ => endsWith_bind _ fun _ => endsWith_bind _ fun _ =>
            endsWith_bind _ fun _ => endsWith_leaf rfl
        · exact endsWith_bind _ fun _ => endsWith_bind _ fun _ => endsWith_leaf rfl
      · exact endsWith_failure
    · exact endsWith_failure
  · have hnext : (Step.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).next tr =
        ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run tr).2.val :=
      stepIn_next_eq _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
        (me, stateIdx, msgIdx, skIdx, pqIdx, spqrMsgIdx) tr
    have hok' : ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run tr).1.isSome = true :=
      (stepIn_ok' _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
        (me, stateIdx, msgIdx, skIdx, pqIdx, spqrMsgIdx) tr) ▸ hok
    rw [hnext]
    unfold _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped at hok' ⊢
    refine (endsWith_bind _ fun st => endsWith_bind _ fun msg => endsWith_bind _ fun e => ?_) tr hok'
    split
    · refine endsWith_guard _ fun hg => ?_
      refine endsWith_bind _ fun _ => ?_
      split
      · exact endsWith_bind _ fun _ => endsWith_bind _ fun _ => endsWith_bind _ fun _ =>
          endsWith_bind _ fun _ => endsWith_bind _ fun _ => endsWith_leaf hg.1
      · exact endsWith_failure
    · exact endsWith_failure

private theorem aliceNotPendingOn_of_logMKStore {r : ProtocolSetup} {tr₁ : ExecTrace}
    {st_new : TRState} {seed pqSalt : _root_.DY.Bytes} {n : UInt32} {rIdx par : Nat}
    (hrole : Symbolic.Swarm.CREF.RoleSnapshots r
      ((tr₁.append (⟨TREvent.MessageKey (st_new.sessionInfo r.alice) .receiver seed pqSalt n rIdx par⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent)).append
        (⟨⟨r.alice, st_new⟩⟩ : TRStEntry))) :
    Symbolic.Proofs.Swarm.UA.Defs.AliceNotPendingOn r.alice
      ((tr₁.append (⟨TREvent.MessageKey (st_new.sessionInfo r.alice) .receiver seed pqSalt n rIdx par⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent)).append
        (⟨⟨r.alice, st_new⟩⟩ : TRStEntry)) := by
  let tr_ev := tr₁.append (⟨TREvent.MessageKey (st_new.sessionInfo r.alice) .receiver seed pqSalt n rIdx par⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent)
  let tr_post := tr_ev.append (⟨⟨r.alice, st_new⟩⟩ : TRStEntry)
  change Symbolic.Proofs.Swarm.UA.Defs.AliceNotPendingOn r.alice tr_post
  have hlen_ev : tr_ev.length = tr₁.length + 1 := by simp [tr_ev, Trace.append, Trace.length]
  have hat_last : (tr_post.at? (tr₁.length + 1) : Option TRStEntry) = some ⟨⟨r.alice, st_new⟩⟩ := by
    rw [← hlen_ev]
    exact at?_append_here tr_ev (⟨⟨r.alice, st_new⟩⟩ : TRStEntry)
  intro k st_k hst_k hcur_k
  have hat_k : (tr_post.at? k : Option TRStEntry) = some ⟨⟨r.alice, st_k⟩⟩ :=
    bks_stored_of_getLocalState hst_k
  have hk_lt : k < tr_post.length := bks_lt_length_of_at? hat_k
  have hlen_post : tr_post.length = tr₁.length + 2 := by
    simp [tr_post, hlen_ev, Trace.append, Trace.length]
  by_cases hk : k < tr₁.length + 1
  · have hinit_k := hrole r.alice st_k k hat_k
    have hinit_new := hrole r.alice st_new (tr₁.length + 1) hat_last
    have hfalse := isCurrentSnapshot_false_of_later hat_k hat_last hk
      (by rw [hinit_new, hinit_k])
    rw [hfalse] at hcur_k; cases hcur_k
  · have hk_eq : k = tr₁.length + 1 := by omega
    subst hk_eq
    have hst_eq : st_k = st_new := by
      rw [hat_last] at hat_k
      injection hat_k with h1
      exact (congrArg (fun x => x.st.state) h1).symm
    subst st_k
    unfold pendingPreKey DY.ExecTrace.getLocalStateAt
    rw [hat_last, Option.map_some]
    dsimp only
    have hdec : sessionHasDecrypted tr_post (st_new.sessionInfo r.alice) (tr₁.length + 1) = true := by
      unfold sessionHasDecrypted
      rw [List.any_eq_true]
      refine ⟨tr₁.length, List.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
      have hev_post : tr_post.getEventAt TREvent tr₁.length =
          some (.MessageKey (st_new.sessionInfo r.alice) .receiver seed pqSalt n rIdx par) := by
        rw [bks_getEventAt_of_le TREvent (Trace.append_le _ _) (by omega)]
        unfold _root_.DY.Trace.getEventAt
        rw [show (tr_ev.at? tr₁.length : Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (⟨TREvent.MessageKey (st_new.sessionInfo r.alice) .receiver seed pqSalt n rIdx par⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent) from at?_append_here tr₁ _]
      rw [hev_post]
      simp
    rw [hdec]
    rfl

private theorem runSteps_le_local : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => Trace.le_refl tr
  | s :: ss, tr => Trace.le_trans _ _ _ (((reachability.step s.toInput).2.run tr).2.property)
      (runSteps_le_local ss (s.next tr))

/-- On Alice whisper `recv` `code = 0`, the updated record satisfies `WireRecCanon` (`sess.pendingPreKey = none`),
and Alice's decrypt step logs `TREvent.MessageKey _ .receiver ..`, establishing `AliceNotPendingOn` and
`AliceRecordPendingInSession` on any explanation with `RoleSnapshots`. -/
theorem aliceRecordPendingInSession_of_alice_canon {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs_pre : List CliEvent} {ev : RunEvent} {peer : Address} {out body : HwBytes}
    {records : Participant → Option HwBytes} {rec_out : HwBytes}
    {initIds : Option BundlePreKeyIds}
    (hwf : ProtocolSetupWF r)
    (hcmd : ev.cmd = .recv peer)
    (hp : ev.party = r.alice)
    (hexit : ev.exit = some (0, out))
    (hinp : ev.input = wireWhisperTag :: body)
    (hex : Explains interp r S g ss vis (evs_pre ++ [.run ev]))
    (hrole : Symbolic.Swarm.CREF.RoleSnapshots r (runTrace r ss))
    (hrec : records r.alice = some rec_out)
    (hwrc : WireRecCanon rec_out) :
    AliceRecordPendingInSession interp r S g (runTrace r ss) records initIds := by
  refine Symbolic.Proofs.Swarm.UA.PendingPreKey.aliceRecordPendingInSession_of_not_pending ?_ ?_
  · intro rec sess hrec' hrc
    rw [hrec] at hrec'; injection hrec' with hrec_eq; subst hrec_eq
    obtain ⟨sess₀, hc₀, _, _, _, _, hppk₀⟩ := hwrc
    have hnorm : normPending (sessionToRecordRecPending sess) =
        normPending (sessionToRecordRecPending sess₀) :=
      Symbolic.Swarm.CREF.TR.recordBytes_injective (by
        rw [recordBytes_sessionToRecordRecPending_of_canonical_Q hrc,
          recordBytes_sessionToRecordRecPending_of_canonical_Q hc₀, ← hrc.1, ← hc₀.1])
    have hp_eq := congrArg (fun x => x.current.pendingPreKey) hnorm
    dsimp only [normPending, normPendingS, sessionToRecordRecPending] at hp_eq
    cases hpp : sess.pendingPreKey
    · rfl
    · rw [hpp, hppk₀] at hp_eq; cases hp_eq
  · obtain ⟨_, _, hrun, hm⟩ := hex
    obtain ⟨ss₁, ss₂, _, vis₂, rfl, rfl, _, hm₂⟩ :=
      Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey.matchesEvents_split [.run ev] evs_pre hm
    have hevs_no_start : ∀ ev₀, .run ev₀ ∈ ([CliEvent.run ev] : List CliEvent) →
        (∀ p d, ev₀.cmd ≠ .init p d) ∧
        (ev₀.party = r.alice → ∀ p, ev₀.cmd = .recv p → ev₀.input.head? = some wireWhisperTag) := by
      intro ev₀ hmem
      simp only [List.mem_singleton, CliEvent.run.injEq] at hmem
      subst hmem
      exact ⟨fun _ _ h => by simp [hcmd] at h, fun _ _ _ => by simp [hinp]⟩
    have hno_start :=
      Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey.matchesEvents_noStart_alice hwf hm₂ hevs_no_start
    generalize hE : ([CliEvent.run ev] : List CliEvent) = E at hm₂
    cases hm₂ with
    | nil _ => cases hE
    | env _ _ _ => cases hE
    | run0 _ hrej _ =>
      injection hE with hev _
      injection hev with hev'
      subst hev'
      exact absurd hexit (hrej out)
    | @run1 _ _ pre s tail ev' evs_rem _ vs hpre hrm htail =>
      injection hE with hev hevs_rem
      injection hev with hev'
      subst hev' hevs_rem
      obtain ⟨_, hparty, hfits, _, hok, _⟩ := hrm
      rw [hp] at hparty
      rw [hcmd] at hfits
      have hs_no := hno_start s (by simp)
      have hs_dec : (∃ stateIdx msgIdx pqIdx spqrMsgIdx,
            s = .messageDecrypt r.alice stateIdx msgIdx pqIdx spqrMsgIdx) ∨
          (∃ stateIdx msgIdx skIdx pqIdx spqrMsgIdx,
            s = .messageDecryptSkipped r.alice stateIdx msgIdx skIdx pqIdx spqrMsgIdx) := by
        cases s with
        | bobStart b a kh regA mh pqIdx spqrIdx =>
          simp only [Step.party?, Option.some.injEq] at hparty
          subst hparty
          exact absurd rfl (hs_no.2 a kh regA mh pqIdx spqrIdx)
        | messageDecrypt p stateIdx msgIdx pqIdx spqrMsgIdx =>
          simp only [Step.party?, Option.some.injEq] at hparty
          subst hparty
          exact Or.inl ⟨stateIdx, msgIdx, pqIdx, spqrMsgIdx, rfl⟩
        | messageDecryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx =>
          simp only [Step.party?, Option.some.injEq] at hparty
          subst hparty
          exact Or.inr ⟨stateIdx, msgIdx, skIdx, pqIdx, spqrMsgIdx, rfl⟩
        | _ => cases hfits
      obtain ⟨tr₁, st_new, seed, pqSalt, n, rIdx, par, hs_next⟩ :=
        decrypt_ok_ends_with_logMKStore hs_dec hok
      have hss_assoc : ss₁ ++ (pre ++ s :: tail) = (ss₁ ++ pre ++ [s]) ++ tail := by
        simp [List.append_assoc]
      have htr_post_eq : runTrace r (ss₁ ++ pre ++ [s]) = s.next (runSteps pre (runSteps ss₁ (setupTrace r))) := by
        simp [runTrace, runSteps_append, runSteps]
      have hle_tail : s.next (runSteps pre (runSteps ss₁ (setupTrace r))) ≤
          runTrace r (ss₁ ++ (pre ++ s :: tail)) := by
        rw [hss_assoc, runTrace_append, htr_post_eq]
        exact runSteps_le_local tail _
      have hrole_post : Symbolic.Swarm.CREF.RoleSnapshots r
          (s.next (runSteps pre (runSteps ss₁ (setupTrace r)))) :=
        fun p st i hat => hrole p st i (at?_le_some hle_tail hat)
      have hnp_post : Symbolic.Proofs.Swarm.UA.Defs.AliceNotPendingOn r.alice
          (runTrace r (ss₁ ++ pre ++ [s])) := by
        rw [htr_post_eq, hs_next]
        exact aliceNotPendingOn_of_logMKStore (hs_next ▸ hrole_post)
      rw [hss_assoc]
      exact Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey.aliceNotPendingOn_of_matchesEvents
        hwf (hss_assoc ▸ hrun) (htr_post_eq ▸ htail) (fun _ h => by cases h) hnp_post

private theorem run_snd_eq {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr : ExecTrace}
    (hx : (x.run tr).2.val = tr) (hf : ∀ a, ((f a).run tr).2.val = tr) :
    ((x >>= f).run tr).2.val = tr := by
  rw [Symbolic.Swarm.CREF.TR.run_bind_snd, hx]
  cases (x.run tr).1 with | none => rfl | some a => exact hf a

private theorem guard_run_snd (P : Prop) [Decidable P] (tr : ExecTrace) :
    ((_root_.guard P : Traceful Unit).run tr).2.val = tr := by unfold _root_.guard; split <;> rfl

private theorem getLocalState_tr_run_snd (p : Participant) (i : Nat) (tr : ExecTrace) :
    ((_root_.DY.PersistentLocalState.getLocalState (StateT := TRState) p i).run tr).2.val = tr := by
  unfold _root_.DY.PersistentLocalState.getLocalState _root_.DY.PersistentGlobalState.getGlobalState
  exact run_snd_eq (run_snd_eq rfl fun _ => rfl) fun _ => run_snd_eq (guard_run_snd _ tr) fun _ => rfl

private theorem receiveMessage_run_snd (i : Nat) (tr : ExecTrace) :
    ((_root_.DY.Network.receiveMessage i).run tr).2.val = tr := by
  unfold _root_.DY.Network.receiveMessage; exact run_snd_eq rfl fun _ => rfl

private theorem verifyMacAndDecrypt_run_snd (st : TRState)
    (msg : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg) (pqSalt seed : _root_.DY.Bytes)
    (tr : ExecTrace) :
    ((_root_.DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed).run tr).2.val = tr := by
  have h := Symbolic.Swarm.COMPOSED.CompPresTRExp.bind_verifyMacAndDecrypt_at
    (Inv := (· = tr)) (f := pure) st msg pqSalt seed tr rfl (fun _ => rfl)
  have hbp : ∀ (x : Traceful _root_.DY.Bytes),
      ((x >>= pure).run tr).2.val = (x.run tr).2.val := fun x => by
    rw [_root_.DY.Traceful.run_bind]
    rcases x.run tr with ⟨_ | _, _⟩ <;> rfl
  rwa [hbp] at h

/-- Preserves `AliceRecordPendingInSession` across a single whisper `recv` event whenever Alice's
leaked record bytes are unchanged and the event is not an accepting Alice `recv`. -/
theorem aliceRecordPendingInSession_whisper_same_record {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {evs_pre : List CliEvent} {ev : RunEvent} {peer : Address}
    {records₁ records₂ : Participant → Option HwBytes}
    (hwf : ProtocolSetupWF r) (hcmd : ev.cmd = .recv peer)
    (hno_alice_acc : ev.party = r.alice → ∀ out, ev.exit ≠ some (0, out))
    (hrec_eq : records₂ r.alice = records₁ r.alice)
    (hap_pre : ∀ g ss vis, Explains interp r S g ss vis evs_pre →
      ¬ ReadCollisionCli interp r S g ss evs_pre →
      AliceRecordPendingInSession interp r S g (runTrace r ss) records₁ (activeBundleIds evs_pre)) :
    ∀ g ss vis, Explains interp r S g ss vis (evs_pre ++ [.run ev]) →
      ¬ ReadCollisionCli interp r S g ss (evs_pre ++ [.run ev]) →
      AliceRecordPendingInSession interp r S g (runTrace r ss) records₂
        (activeBundleIds (evs_pre ++ [.run ev])) := by
  have hevs_ok : ∀ ev₀, .run ev₀ ∈ ([CliEvent.run ev] : List CliEvent) →
      (∀ p d, ev₀.cmd ≠ .init p d) ∧
      (ev₀.party = r.alice → ∀ p out, ev₀.cmd = .recv p → ev₀.exit ≠ some (0, out)) := by
    intro ev₀ hmem
    simp only [List.mem_singleton, CliEvent.run.injEq] at hmem
    subst hmem
    exact ⟨fun p d h => by simp [hcmd] at h, fun ha _ out _ => hno_alice_acc ha out⟩
  intro g ss vis hex hnrc
  exact Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey.aliceRecordPendingInSession_of_explains_append
    hwf hex hnrc hevs_ok hrec_eq
    (fun ss₁ vis₁ hex₁ hnrc₁ => hap_pre g ss₁ vis₁ hex₁ hnrc₁)

/-- Closes `UAInvB` on a rejected whisper `recv` call once `CliLiveAtCli` is updated and Alice's
leaked record is unchanged. -/
theorem uaInv_recv_rejected {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {t_clean t_clean' : CliTurn}
    {accepted' : List HwBytes} {evs_pre : List CliEvent}
    {c : CliCall} {peer : Address} {code : Nat} {out : HwBytes}
    (hwf : ProtocolSetupWF r) (hcmd : c.cmd = .recv peer) (hne : code ≠ 0)
    (_hhead : c.party = r.alice → (runInput c).head? = some wireWhisperTag)
    (hrec_alice : t_clean'.leakRecords r r.alice = t_clean.leakRecords r r.alice)
    (hlive' : CliLiveAtCli interp r S who ok t_clean' accepted'
      (flatEvents (evs_pre ++ [.run (runEventOf c (some (code, out)))])))
    (hap_pre : ∀ g ss vis, Explains interp r S g ss vis evs_pre →
      ¬ ReadCollisionCli interp r S g ss evs_pre →
      AliceRecordPendingInSession interp r S g (runTrace r ss) (t_clean.leakRecords r)
        (activeBundleIds evs_pre))
    (hex_pre : ∃ g ss vis, Explains interp r S g ss vis evs_pre ∧
      ¬ ReadCollisionCli interp r S g ss evs_pre) :
    UAInvB interp r S who ok t_clean' accepted'
      (evs_pre ++ [.run (runEventOf c (some (code, out)))]) := by
  let ev := runEventOf c (some (code, out))
  have hrej : RunRejected ev := by
    intro out' h
    simp only [ev, runEventOf, Option.some.injEq, Prod.mk.injEq] at h
    exact hne h.1
  right
  refine ⟨hlive', aliceRecordPendingInSession_whisper_same_record (peer := peer) hwf
    (by simp [runEventOf, hcmd]) (fun _ out' => hrej out') hrec_alice hap_pre, ?_⟩
  obtain ⟨g, ss, vis, hex, hnrc⟩ := hex_pre
  refine ⟨g, ss, vis, explains_snoc_rejected hrej hex, ?_⟩
  rintro ⟨evs₁, ev₀, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out₀, b₀, t₀,
    heq, hss, hrcmd, hexit₀, hrb, hm₁, hdec, hget, hcol⟩
  rcases evs₂.eq_nil_or_concat with rfl | ⟨evs₂', e_last, rfl⟩
  · have hlast : [CliEvent.run ev] = [CliEvent.run ev₀] := List.append_inj_right' heq rfl
    injection hlast with hlast'
    injection hlast' with hev_eq
    subst hev_eq
    exact hrej out₀ hexit₀
  · have hevs_eq : evs_pre = evs₁ ++ .run ev₀ :: evs₂' := by
      have h1 : evs_pre ++ [CliEvent.run ev] =
          (evs₁ ++ .run ev₀ :: evs₂') ++ [e_last] := by
        simpa only [List.concat_eq_append, List.cons_append, List.append_assoc] using heq
      exact List.append_inj_left' h1 rfl
    subst hevs_eq
    exact hnrc ⟨evs₁, ev₀, evs₂', ss₁, ss₂, m, vis₁, msgIdx, out₀, b₀, t₀,
      rfl, hss, hrcmd, hexit₀, hrb, hm₁, hdec, hget, hcol⟩

/-! ## Whisper Accepting Witness Lift -/

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

private theorem bind_pure_unit_snd {α : Type} (x : Traceful α) (tr : ExecTrace) :
    ((x >>= fun _ => pure ()).run tr).2.val = (x.run tr).2.val := by
  rw [_root_.DY.Traceful.run_bind]; rcases x.run tr with ⟨_ | _, _⟩ <;> rfl

private theorem stepIn_ok (c : _root_.DY.ReachabilityConfig)
    [i : _root_.DY.ReachabilityConfig.HasStep c reachability] (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => (s.2.run tr).1.isSome) (i.pf_step x).symm

private theorem stepIn_preCond_of (c : _root_.DY.ReachabilityConfig)
    [inst : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) (h : c.PreCond x tr) :
    reachability.PreCond (stepIn c x) tr := (inst.pf_pre x tr).mp h

private theorem stepToMove_next {s : Step} (hs : StepHasMove s) (tr : ExecTrace) :
    (stepToMove s).next tr = s.next tr := by
  cases s <;> (try (rcases hs with h | h | h <;> cases h)) <;>
    (dsimp only [stepToMove, Move.next, Move.act, Step.next, Step.toInput];
     symm; refine (stepIn_next_eq _ _ tr).trans (bind_pure_unit_snd _ tr).symm)

private theorem network_next_eq_append (msg : _root_.DY.Bytes) (tr : ExecTrace) :
    (Step.network msg).next tr = tr.append (⟨msg⟩ : _root_.DY.Network.ExecEntryT) :=
  stepIn_next_eq _root_.DY.Network.reachability msg tr

private theorem isCurrentSnapshot_runSteps_network :
    ∀ (ext : List _root_.DY.Bytes) (tr : ExecTrace) (k : Nat),
      isCurrentSnapshot (runSteps (ext.map .network) tr) k = isCurrentSnapshot tr k
  | [], _, _ => rfl
  | x :: ext, tr, k => by
    simp only [List.map_cons, runSteps, network_next_eq_append,
      isCurrentSnapshot_runSteps_network ext]
    exact Symbolic.Swarm.CREF.TR.RecvDec.isCurrentSnapshot_append_non_st tr
      (⟨x⟩ : _root_.DY.Network.ExecEntryT) rfl k

theorem stepsStateFaithful_snoc_decrypt {r : ProtocolSetup} {ss : List Step}
    {ext : List _root_.DY.Bytes} {s : Step}
    (hsf : StepsStateFaithful r ss)
    (hcur : ∀ p k b, s.stateLoad? = some (p, k, b) →
      isCurrentSnapshot (runTrace r ss) k = true) :
    StepsStateFaithful r (ss ++ ext.map .network ++ [s]) := by
  have hsf_net : StepsStateFaithful r (ss ++ ext.map .network) :=
    Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.stepsStateFaithful_append_noLoad hsf
      (fun x hx => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; rfl)
  refine stepsStateFaithful_snoc_of_isCurrentSnapshot_gen hsf_net fun p k b hload => ?_
  rw [runTrace_append, isCurrentSnapshot_runSteps_network]
  exact hcur p k b hload

private theorem at?_eq_of_le_lt {E : Type} [ExecTraceTypes.Has E] {t₁ t₂ : ExecTrace}
    (hle : t₁ ≤ t₂) {i : Nat} (hlt : i < t₁.length) :
    (t₂.at? i : Option E) = t₁.at? i := by
  have hlt₂ : i < t₂.length := Nat.lt_of_lt_of_le hlt (Trace.length_le t₁ t₂ hle)
  simp only [Trace.at?, hlt, hlt₂, ↓reduceDIte]
  rw [Trace.at_le t₁ t₂ i hlt hle]

private theorem at?_eq_none_of_ge {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace}
    {i : Nat} (hge : tr.length ≤ i) : (tr.at? i : Option E) = none := by
  have hnot : ¬ (i < tr.length) := Nat.not_lt_of_ge hge
  simp [Trace.at?, hnot]

private def PreVerifyInv (tr tr' : ExecTrace) : Prop :=
  tr ≤ tr' ∧
  (∀ i, tr.length ≤ i → (tr'.at? i : Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) = none) ∧
  (∀ i, tr.length ≤ i → ∀ e : _root_.DY.Random.ExecEntryT, tr'.at? i = some e → e.length = 32)

private theorem preVerifyInv_refl (tr : ExecTrace) : PreVerifyInv tr tr :=
  ⟨Trace.le_refl tr, fun _ hi => at?_eq_none_of_ge hi,
    fun _ hi _ he => by rw [at?_eq_none_of_ge hi] at he; cases he⟩

private theorem preVerifyInv_same {tr tr' : ExecTrace} (h : tr' = tr) : PreVerifyInv tr tr' :=
  h ▸ preVerifyInv_refl tr

private theorem preVerifyInv_trans {t₀ t₁ t₂ : ExecTrace}
    (h1 : PreVerifyInv t₀ t₁) (h2 : PreVerifyInv t₁ t₂) : PreVerifyInv t₀ t₂ := by
  refine ⟨Trace.le_trans _ _ _ h1.1 h2.1, fun i hi => ?_, fun i hi e he => ?_⟩
  · by_cases hlt : i < t₁.length
    · rw [at?_eq_of_le_lt h2.1 hlt]; exact h1.2.1 i hi
    · exact h2.2.1 i (Nat.le_of_not_lt hlt)
  · by_cases hlt : i < t₁.length
    · rw [at?_eq_of_le_lt h2.1 hlt] at he; exact h1.2.2 i hi e he
    · exact h2.2.2 i (Nat.le_of_not_lt hlt) e he

private theorem preVerifyInv_append_nonTR_nonRnd {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hTR : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) = none := by rfl)
    (hRnd : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option _root_.DY.Random.ExecEntryT) = none := by rfl) :
    PreVerifyInv tr (tr.append e) := by
  have hlen : (tr.append e).length = tr.length + 1 := by simp [Trace.append, Trace.length]
  refine ⟨Trace.append_le tr e, fun i hi => ?_, fun i hi r hr => ?_⟩
  · by_cases heq : i = tr.length
    · subst heq
      have hat_eq : ((tr.append e).at? tr.length :
          Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) =
          TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]
      rw [hat_eq]; exact hTR
    · exact at?_eq_none_of_ge (by omega)
  · by_cases heq : i = tr.length
    · subst heq
      have hat_eq : ((tr.append e).at? tr.length : Option _root_.DY.Random.ExecEntryT) =
          TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]
      rw [hat_eq, hRnd] at hr; cases hr
    · rw [at?_eq_none_of_ge (by omega)] at hr; cases hr

private theorem preVerifyInv_genRand32 (tr : ExecTrace) :
    PreVerifyInv tr ((_root_.DY.Random.genRand 32).run tr).2.val := by
  simp only [_root_.DY.Random.genRand, _root_.DY.appendEntry, Traceful.run_mk,
    Traceful.run_bind, Traceful.run_pure]
  have hlen : (tr.append ({ length := 32 } : _root_.DY.Random.ExecEntryT)).length = tr.length + 1 := by
    simp [Trace.append, Trace.length]
  refine ⟨Trace.append_le tr _, fun i hi => ?_, fun i hi r hr => ?_⟩
  · by_cases heq : i = tr.length
    · subst heq
      have hat_eq : ((tr.append ({ length := 32 } : _root_.DY.Random.ExecEntryT)).at? tr.length :
          Option (_root_.DY.ProtocolEvent.ExecEntryT TREvent)) =
          TraceEntryHas.proj (TraceEntryHas.inj ({ length := 32 } : _root_.DY.Random.ExecEntryT) :
            ExecTrace.Entry) := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]
      rw [hat_eq]; rfl
    · exact at?_eq_none_of_ge (by omega)
  · by_cases heq : i = tr.length
    · subst heq
      have hat_eq : ((tr.append ({ length := 32 } : _root_.DY.Random.ExecEntryT)).at? tr.length :
          Option _root_.DY.Random.ExecEntryT) =
          TraceEntryHas.proj (TraceEntryHas.inj ({ length := 32 } : _root_.DY.Random.ExecEntryT) :
            ExecTrace.Entry) := by
        simp [Trace.at?, Trace.append, Trace.at, Trace.length]
      have hproj : (TraceEntryHas.proj (TraceEntryHas.inj ({ length := 32 } :
          _root_.DY.Random.ExecEntryT) : ExecTrace.Entry) :
          Option _root_.DY.Random.ExecEntryT) = some { length := 32 } := rfl
      rw [hat_eq, hproj] at hr; injection hr with h; rw [← h]
    · rw [at?_eq_none_of_ge (by omega)] at hr; cases hr

private theorem preVerifyInv_bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr : ExecTrace} (hx : PreVerifyInv tr (x.run tr).2.val)
    (hf : ∀ a, PreVerifyInv (x.run tr).2.val ((f a).run (x.run tr).2.val).2.val) :
    PreVerifyInv tr ((x >>= f).run tr).2.val := by
  dsimp only [Bind.bind, Monad.toBind, Traceful.run] at hx ⊢
  rcases hrun : x tr with ⟨_ | a, tr₁⟩
  · rw [hrun] at hx; exact hx
  · have hf_a := hf a
    dsimp only [Traceful.run] at hf_a
    rw [hrun] at hx hf_a
    exact preVerifyInv_trans hx hf_a

private theorem preVerifyInv_ensureReceiverChain (st : TRState) (rk : _root_.DY.Bytes)
    (tr : ExecTrace) :
    PreVerifyInv tr ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st rk).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  rcases _root_.DY.Libsignal.TripleRatchet.recvChainFor st.toDRState rk with _ | ⟨c, false | true⟩
  · exact preVerifyInv_refl tr
  · exact preVerifyInv_refl tr
  · simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
    refine preVerifyInv_bind ?_ fun _ => preVerifyInv_refl _
    refine preVerifyInv_bind (preVerifyInv_same (guard_run_snd _ tr)) fun _ => ?_
    rcases _root_.DY.Libsignal.TripleRatchet.createChain st.rk rk st.dhs with ⟨rk1, ckr⟩
    exact preVerifyInv_bind (preVerifyInv_genRand32 _) fun _ => preVerifyInv_refl _

private theorem onlyRand32_append_nonRnd {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hRnd : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option _root_.DY.Random.ExecEntryT) = none := by rfl) :
    (tr ≤ tr.append e) ∧
      ∀ i, tr.length ≤ i → ∀ r : _root_.DY.Random.ExecEntryT, (tr.append e).at? i = some r →
        r.length = 32 := by
  have hlen : (tr.append e).length = tr.length + 1 := by simp [Trace.append, Trace.length]
  refine ⟨Trace.append_le tr e, fun i hi r hr => ?_⟩
  by_cases heq : i = tr.length
  · subst heq
    have hat_eq : ((tr.append e).at? tr.length : Option _root_.DY.Random.ExecEntryT) =
        TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) := by
      simp [Trace.at?, Trace.append, Trace.at, Trace.length]
    rw [hat_eq, hRnd] at hr; cases hr
  · rw [at?_eq_none_of_ge (by omega)] at hr; cases hr

private def OkAndRand32 {α : Type} (x : Traceful α) (tr : ExecTrace) : Prop :=
  (x.run tr).1.isSome = true ∧ tr ≤ (x.run tr).2.val ∧
    ∀ i, tr.length ≤ i → ∀ r : _root_.DY.Random.ExecEntryT,
      (x.run tr).2.val.at? i = some r → r.length = 32

private theorem okAndRand32_pure {α : Type} (a : α) (tr : ExecTrace) :
    OkAndRand32 (pure a) tr :=
  ⟨rfl, (preVerifyInv_refl tr).1, (preVerifyInv_refl tr).2.2⟩

private theorem okAndRand32_bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr : ExecTrace} (hx : OkAndRand32 x tr)
    (hf : ∀ a, OkAndRand32 (f a) (x.run tr).2.val) :
    OkAndRand32 (x >>= f) tr := by
  rcases hx with ⟨hx_ok, hx_le, hx_r⟩
  unfold OkAndRand32
  dsimp only [Bind.bind, Monad.toBind, Traceful.run] at hx_ok hx_le hx_r ⊢
  rcases hrun : x tr with ⟨_ | a, tr₁⟩
  · rw [hrun] at hx_ok; cases hx_ok
  · have hf_a := hf a
    unfold OkAndRand32 at hf_a
    dsimp only [Traceful.run] at hf_a
    rw [hrun] at hx_le hx_r hf_a
    dsimp only at hx_le hx_r hf_a ⊢
    obtain ⟨hf_ok, hf_le, hf_r⟩ := hf_a
    refine ⟨hf_ok, Trace.le_trans _ _ _ hx_le hf_le, fun i hi r hr => ?_⟩
    by_cases hlt : i < tr₁.val.length
    · rw [at?_eq_of_le_lt hf_le hlt] at hr
      exact hx_r i hi r hr
    · exact hf_r i (Nat.le_of_not_lt hlt) r hr

private theorem okAndRand32_logTR (e : TREvent) (tr : ExecTrace) :
    OkAndRand32 (_root_.DY.ProtocolEvent.logEvent e) tr := by
  simp only [OkAndRand32, _root_.DY.ProtocolEvent.logEvent, _root_.DY.appendEntry,
    Traceful.run_mk, Traceful.run_bind, Traceful.run_pure]
  exact ⟨rfl, onlyRand32_append_nonRnd tr (⟨e⟩ : _root_.DY.ProtocolEvent.ExecEntryT TREvent)⟩

private theorem okAndRand32_storeTR (p : Participant) (st : TRState) (tr : ExecTrace) :
    OkAndRand32 (_root_.DY.PersistentLocalState.storeLocalState p st) tr := by
  unfold _root_.DY.PersistentLocalState.storeLocalState
    _root_.DY.PersistentGlobalState.storeGlobalState
  exact ⟨rfl, onlyRand32_append_nonRnd tr (⟨⟨p, st⟩⟩ : TRStEntry)⟩

private theorem okAndRand32_logSkippedKeys (s : _root_.DY.Libsignal.TripleRatchet.SessionInfo)
    (pk : _root_.DY.Bytes) (rIdx srcIdx : Nat) :
    ∀ (k : Nat) (ck : _root_.DY.Bytes) (idx : UInt32) (tr : ExecTrace),
      OkAndRand32 (_root_.DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx k) tr
  | 0, _, _, tr => okAndRand32_pure () tr
  | k + 1, ck, idx, tr => by
    unfold _root_.DY.Libsignal.TripleRatchet.logSkippedKeys
    exact okAndRand32_bind (okAndRand32_logTR _ tr) fun _ =>
      okAndRand32_logSkippedKeys s pk rIdx srcIdx k _ _ _

private theorem okAndRand32_logMessageKeyAndStore (me : Participant)
    (s : _root_.DY.Libsignal.TripleRatchet.SessionInfo)
    (dir : _root_.DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : _root_.DY.Bytes)
    (n : UInt32) (rIdx parIdx : Nat) (st : TRState) (tr : ExecTrace) :
    OkAndRand32 (_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
      me s dir seed pqSalt n rIdx parIdx st) tr := by
  unfold _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact okAndRand32_bind (okAndRand32_logTR _ tr) fun _ =>
    okAndRand32_storeTR me st _

private theorem receivedPlaintext_eq_none_of_preVerifyInv {tr tr' : ExecTrace}
    (h : PreVerifyInv tr tr') : receivedPlaintext tr tr' = none := by
  unfold receivedPlaintext
  rw [List.findSome?_eq_none_iff]
  intro idx hidx
  unfold newIndices at hidx
  rw [List.mem_range'_1] at hidx
  have hnone := h.2.1 idx hidx.1
  unfold Trace.getEventAt
  rw [hnone]

private theorem preVerify_and_tail_ok {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr₀ tr : ExecTrace} (hpv : PreVerifyInv tr₀ tr) (hx : PreVerifyInv tr (x.run tr).2.val)
    (hf : ∀ a, (receivedPlaintext tr₀ (((f a).run (x.run tr).2.val).2.val) ≠ none →
        (((f a).run (x.run tr).2.val).1.isSome = true)) ∧
      (∀ i, tr₀.length ≤ i → ∀ r : _root_.DY.Random.ExecEntryT,
        ((f a).run (x.run tr).2.val).2.val.at? i = some r → r.length = 32)) :
    (receivedPlaintext tr₀ (((x >>= f).run tr).2.val) ≠ none →
      (((x >>= f).run tr).1.isSome = true)) ∧
    (∀ i, tr₀.length ≤ i → ∀ r : _root_.DY.Random.ExecEntryT,
      (((x >>= f).run tr).2.val).at? i = some r → r.length = 32) := by
  dsimp only [Bind.bind, Monad.toBind, Traceful.run] at hx ⊢
  rcases hrun : x tr with ⟨_ | a, tr₁⟩
  · rw [hrun] at hx
    have hpv₁ := preVerifyInv_trans hpv hx
    exact ⟨fun hrec => absurd (receivedPlaintext_eq_none_of_preVerifyInv hpv₁) hrec, hpv₁.2.2⟩
  · have hf' := hf a
    dsimp only [Traceful.run] at hf'; rwa [hrun] at hf'

private theorem preVerify_same_ok {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr₀ tr : ExecTrace} (hpv : PreVerifyInv tr₀ tr) (hx : (x.run tr).2.val = tr)
    (hf : ∀ a, ((receivedPlaintext tr₀ ((f a).run tr).2.val ≠ none → ((f a).run tr).1.isSome = true)) ∧
      (∀ i, tr₀.length ≤ i → ∀ r : _root_.DY.Random.ExecEntryT,
        ((f a).run tr).2.val.at? i = some r → r.length = 32)) :
    (receivedPlaintext tr₀ (((x >>= f).run tr).2.val) ≠ none →
      (((x >>= f).run tr).1.isSome = true)) ∧
    (∀ i, tr₀.length ≤ i → ∀ r : _root_.DY.Random.ExecEntryT,
      (((x >>= f).run tr).2.val).at? i = some r → r.length = 32) := by
  refine preVerify_and_tail_ok hpv (preVerifyInv_same hx) fun a => ?_
  rw [hx]; exact hf a

private theorem preVerify_leaf_ok {α : Type} {x : Traceful α} {tr₀ tr : ExecTrace}
    (hpv : PreVerifyInv tr₀ tr) (hok : OkAndRand32 x tr) :
    (receivedPlaintext tr₀ (x.run tr).2.val ≠ none → (x.run tr).1.isSome = true) ∧
    (∀ i, tr₀.length ≤ i → ∀ r : _root_.DY.Random.ExecEntryT,
      (x.run tr).2.val.at? i = some r → r.length = 32) := by
  refine ⟨fun _ => hok.1, fun i hi r hr => ?_⟩
  by_cases hlt : i < tr.length
  · rw [at?_eq_of_le_lt hok.2.1 hlt] at hr; exact hpv.2.2 i hi r hr
  · exact hok.2.2 i (Nat.le_of_not_lt hlt) r hr

private theorem receiveSignalMsg_run_snd (msgIdx : Nat) (tr₁ : ExecTrace) :
    ((_root_.DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx).run tr₁).2.val = tr₁ := by
  unfold _root_.DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine run_snd_eq (receiveMessage_run_snd msgIdx tr₁) fun raw => ?_
  cases parseTrSignalMsg raw with
  | none => rfl
  | some _ => exact run_snd_eq (guard_run_snd _ tr₁) fun _ => rfl

private theorem decrypt_step_ok_and_rand32 {s : Step} {p : Participant}
    {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} (tr : ExecTrace)
    (hs : s = .messageDecrypt p stateIdx msgIdx pqIdx spqrMsgIdx ∨
      ∃ skIdx, s = .messageDecryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx) :
    (receivedPlaintext tr (s.next tr) ≠ none → s.ok tr = true) ∧
    (∀ i, tr.length ≤ i → ∀ r : _root_.DY.Random.ExecEntryT,
      (s.next tr).at? i = some r → r.length = 32) := by
  have hpv₀ := preVerifyInv_refl tr
  rcases hs with rfl | ⟨skIdx, rfl⟩
  · have hnext : (Step.messageDecrypt p stateIdx msgIdx pqIdx spqrMsgIdx).next tr =
        ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt p stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val :=
      stepIn_next_eq _root_.DY.Libsignal.TripleRatchet.messageDecrypt.reachability
        (p, stateIdx, msgIdx, pqIdx, spqrMsgIdx) tr
    have hok_eq : (Step.messageDecrypt p stateIdx msgIdx pqIdx spqrMsgIdx).ok tr =
        ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt p stateIdx msgIdx pqIdx spqrMsgIdx).run tr).1.isSome :=
      stepIn_ok _root_.DY.Libsignal.TripleRatchet.messageDecrypt.reachability
        (p, stateIdx, msgIdx, pqIdx, spqrMsgIdx) tr
    rw [hnext, hok_eq]
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
    refine preVerify_same_ok hpv₀ (getLocalState_tr_run_snd p stateIdx tr) fun st => ?_
    refine preVerify_same_ok hpv₀ (receiveSignalMsg_run_snd msgIdx tr) fun msg => ?_
    have hx_ens := preVerifyInv_ensureReceiverChain st msg.ratchetKey tr
    refine preVerify_and_tail_ok hpv₀ hx_ens fun r_ec => ?_
    rcases r_ec with ⟨st', c, ratcheted⟩
    dsimp only
    rcases _root_.DY.Libsignal.TripleRatchet.consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
    · exact ⟨fun hrec => absurd (receivedPlaintext_eq_none_of_preVerifyInv hx_ens) hrec, hx_ens.2.2⟩
    · rcases _root_.DY.Spqr.spqrRecv st'.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
      · exact ⟨fun hrec => absurd (receivedPlaintext_eq_none_of_preVerifyInv hx_ens) hrec, hx_ens.2.2⟩
      · let tr_ens := ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st msg.ratchetKey).run tr).2.val
        have hx_send := preVerifyInv_append_nonTR_nonRnd tr_ens (⟨key⟩ : _root_.DY.Network.ExecEntryT)
        have hpv_send := preVerifyInv_trans hx_ens hx_send
        refine preVerify_and_tail_ok hx_ens hx_send fun _ => ?_
        let tr_send := tr_ens.append (⟨key⟩ : _root_.DY.Network.ExecEntryT)
        refine preVerify_same_ok hpv_send (receiveMessage_run_snd pqIdx tr_send) fun pqSalt => ?_
        refine preVerify_same_ok hpv_send (verifyMacAndDecrypt_run_snd st' msg pqSalt seed tr_send) fun m => ?_
        cases ratcheted
        · exact preVerify_leaf_ok hpv_send
            (okAndRand32_bind (okAndRand32_logSkippedKeys _ _ _ _ _ _ _ _) fun _ =>
              okAndRand32_bind (okAndRand32_logTR _ _) fun _ =>
              okAndRand32_logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _)
        · exact preVerify_leaf_ok hpv_send
            (okAndRand32_bind (okAndRand32_logTR _ _) fun _ =>
              okAndRand32_bind (okAndRand32_logTR _ _) fun _ =>
              okAndRand32_bind (okAndRand32_logSkippedKeys _ _ _ _ _ _ _ _) fun _ =>
              okAndRand32_bind (okAndRand32_logTR _ _) fun _ =>
              okAndRand32_logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _)
  · have hnext : (Step.messageDecryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx).next tr =
        ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run tr).2.val :=
      stepIn_next_eq _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
        (p, stateIdx, msgIdx, skIdx, pqIdx, spqrMsgIdx) tr
    have hok_eq : (Step.messageDecryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx).ok tr =
        ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run tr).1.isSome :=
      stepIn_ok _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
        (p, stateIdx, msgIdx, skIdx, pqIdx, spqrMsgIdx) tr
    rw [hnext, hok_eq]
    unfold _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
    refine preVerify_same_ok hpv₀ (getLocalState_tr_run_snd p stateIdx tr) fun st => ?_
    refine preVerify_same_ok hpv₀ (receiveSignalMsg_run_snd msgIdx tr) fun msg => ?_
    refine preVerify_same_ok hpv₀ rfl fun e => ?_
    cases e.ev with
    | SkippedKeyStored s pk n seed rIdx srcIdx =>
      dsimp only
      refine preVerify_same_ok hpv₀ (guard_run_snd _ tr) fun _ => ?_
      refine preVerify_same_ok hpv₀ rfl fun _ => ?_
      rcases _root_.DY.Spqr.spqrRecv _ _ spqrMsgIdx with _ | ⟨spqr', key⟩
      · exact ⟨fun hrec => absurd (receivedPlaintext_eq_none_of_preVerifyInv hpv₀) hrec, hpv₀.2.2⟩
      · have hx_send := preVerifyInv_append_nonTR_nonRnd tr (⟨key⟩ : _root_.DY.Network.ExecEntryT)
        refine preVerify_and_tail_ok hpv₀ hx_send fun _ => ?_
        let tr_send := tr.append (⟨key⟩ : _root_.DY.Network.ExecEntryT)
        refine preVerify_same_ok hx_send (receiveMessage_run_snd pqIdx tr_send) fun pqSalt => ?_
        refine preVerify_same_ok hx_send (verifyMacAndDecrypt_run_snd st msg pqSalt seed tr_send) fun m => ?_
        exact preVerify_leaf_ok hx_send
          (okAndRand32_bind (okAndRand32_logTR _ _) fun _ =>
            okAndRand32_bind (okAndRand32_logTR _ _) fun _ =>
            okAndRand32_logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _)
    | _ => exact ⟨fun hrec => absurd (receivedPlaintext_eq_none_of_preVerifyInv hpv₀) hrec, hpv₀.2.2⟩

private theorem recvRepOn_transfer {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {ts : Nat} (hga : Symbolic.Swarm.CREF.CBadGammaAgree interp S g₁ g₂ ts) {tr : ExecTrace}
    (htr : Symbolic.Swarm.CREF.TR.FreshSigma.TraceEntriesLt interp S g₁ ts tr)
    {b : HwBytes} {t : _root_.DY.Bytes}
    (ht : t ∈ recvRepresentationsOn interp S g₁ tr b) :
    t ∈ recvRepresentationsOn interp S g₂ tr b := by
  obtain ⟨hk, hb, hp, hf⟩ := ht
  have hts := Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_knows htr hk
  refine ⟨hk, (Symbolic.Swarm.CREF.cbadG2_gamma_eq hga hts).trans hb, hp, fun msg hmsg => ?_⟩
  obtain ⟨hw, hm, hrk, hct, hpq⟩ :=
    Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_parseTrSignalMsg hts hmsg
  obtain ⟨h1, h2, h3, h4⟩ := hf msg hmsg
  refine ⟨(Symbolic.Swarm.CREF.cbadG2_gamma_eq hga hw).trans h1,
    (Symbolic.Swarm.CREF.cbadG2_gamma_eq hga hm).trans h2, h3, fun m hm' => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := h4 m hm'
  exact ⟨(Symbolic.Swarm.CREF.cbadG2_gamma_eq hga hct).trans e1,
    (Symbolic.Swarm.CREF.cbadG2_gamma_eq hga hrk).trans e2,
    (Symbolic.Swarm.CREF.cbadG2_gamma_eq hga hpq).trans e3, e4, e5⟩

private theorem randTerm_inj {interp : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {i₁ n₁ i₂ n₂ : Nat} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (h : randTerm i₁ n₁ = randTerm i₂ n₂) : i₁ = i₂ ∧ n₁ = n₂ := by
  let g_test : Ghost :=
    { σ := fun i n => if i = i₁ ∧ n = n₁ then [0#8] else [], addr := fun _ => [] }
  have h1 := Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.gamma_randTerm_eq interp S g_test i₁ n₁ hn₁
  have h2 := Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.gamma_randTerm_eq interp S g_test i₂ n₂ hn₂
  rw [h, h2] at h1
  dsimp only [g_test] at h1
  simp only [and_self, ↓reduceIte] at h1
  by_cases heq : i₂ = i₁ ∧ n₂ = n₁
  · exact ⟨heq.1.symm, heq.2.symm⟩
  · simp [heq] at h1

private theorem forall2_append_inv {α β : Type} {R : α → β → Prop} :
    ∀ {xs₁ xs₂ : List α} {ys₁ ys₂ : List β},
      xs₁.length = ys₁.length →
      List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂) →
      List.Forall₂ R xs₂ ys₂
  | [], xs₂, [], ys₂, _, h => h
  | _ :: _, _, [], _, hlen, _ => by cases hlen
  | [], _, _ :: _, _, hlen, _ => by cases hlen
  | _ :: xs₁, xs₂, _ :: ys₁, ys₂, hlen, h => by
    cases h with
    | cons _ hrest => exact forall2_append_inv (Nat.succ.inj hlen) hrest

private theorem eventMatchesEntry_to_bytesMatchEntry {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {e : MachineEvent} {v : VisEntry}
    {initIds : Option BundlePreKeyIds} (hv : v.layout ≠ .preKeySend)
    (hv2 : ∀ eks, v.layout ≠ .preKeyInner eks)
    (h : EventMatchesEntry interp r S g e v) :
    BytesMatchEntry interp r S g (eventKind e) (eventBytes e) v initIds := by
  unfold EventMatchesEntry at h
  unfold BytesMatchEntry
  refine ⟨h.1, ?_⟩
  have hm := h.2
  cases hl : v.layout <;> simp only [hl] at hm ⊢
  case preKeySend => exact absurd hl hv
  case preKeyInner eks => exact absurd hl (hv2 eks)
  all_goals exact hm

/-- Lifts `RecvDecryptRawWitness` on a whisper `recv` call to `ModelAcceptsTermAfterAttackerSends` on `Step` runs. -/
theorem acceptsViaCli_whisper_of_rawWitness {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs_pre : List CliEvent}
    {ms : List Move} {τ mid : List MachineEvent}
    {ev : RunEvent} {peer : Address} {body pt : HwBytes}
    (hex_pre : Explains interp r S g ss vis evs_pre)
    (hmp_pre : MatchedPrefix interp r S who g ms τ)
    (htr : runTraceMoves r ms = runTrace r ss)
    (hcmd : ev.cmd = .recv peer)
    (hexit : ev.exit = some (0, pt))
    (hinp : ev.input = wireWhisperTag :: body)
    (hcoins : ev.coins.length = 32)
    (hmid : mid = [] ∨ mid = [.rng ev.coins])
    (hw : Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.RecvDecryptRawWitness interp r S who g ms τ mid
      ev.party wireWhisperTag body body pt) :
    ∃ t_m ∈ recvRepresentationsOn interp S g (runTrace r ss) body,
      ModelAcceptsTermAfterAttackerSends interp r S g ss evs_pre ev t_m := by
  obtain ⟨g₁, stateIdx, spqrMsgIdx, pqSalt, t_m, m_mv,
    hfr_mv, ht_m_mv, hpq_kn_mv, hcur_mv, hm_mv, hmp₁⟩ := hw
  have hfr : CBadSigmaFrame g g₁ (runTrace r ss).length := htr ▸ hfr_mv
  have ht_m_on : t_m ∈ recvRepresentationsOn interp S g (runTrace r ss) body :=
    recvRepresentations_eq_of_trace htr ▸ ht_m_mv
  have hpq_kn : pqSalt.AttackerKnows (runTrace r ss) := htr ▸ hpq_kn_mv
  have hcur : isCurrentSnapshot (runTrace r ss) stateIdx = true := htr ▸ hcur_mv
  let ext : List _root_.DY.Bytes := [pqSalt, t_m]
  let pqIdx := (runTrace r ss).length
  let msgIdx := (runTrace r ss).length + 1
  have hmv_ex : ∃ m_step : Step,
      (m_step = .messageDecrypt ev.party stateIdx msgIdx pqIdx spqrMsgIdx ∨
        ∃ skIdx, m_step = .messageDecryptSkipped ev.party stateIdx msgIdx skIdx pqIdx spqrMsgIdx) ∧
      stepToMove m_step = m_mv := by
    simp only [htr, ne_eq, not_true_eq_false, decide_false] at hm_mv
    rcases hm_mv with rfl | ⟨skIdx, rfl⟩
    · exact ⟨.messageDecrypt ev.party stateIdx msgIdx pqIdx spqrMsgIdx, Or.inl rfl, rfl⟩
    · exact ⟨.messageDecryptSkipped ev.party stateIdx msgIdx skIdx pqIdx spqrMsgIdx,
        Or.inr ⟨skIdx, rfl⟩, rfl⟩
  obtain ⟨m_step, hm_cases, hstm⟩ := hmv_ex
  refine ⟨t_m, ht_m_on, ext, m_step, msgIdx, g₁, ?_⟩
  let tr_ss := runTrace r ss
  let tr_net := runTrace r (ss ++ ext.map .network)
  have htr_net_eq : tr_net =
      ((tr_ss.append (⟨pqSalt⟩ : _root_.DY.Network.ExecEntryT)).append
        (⟨t_m⟩ : _root_.DY.Network.ExecEntryT)) := by
    simp [tr_net, tr_ss, ext, runTrace_append, runSteps, network_next_eq_append]
  have hget_msg : tr_net.getMessageSentAt msgIdx = some t_m := by
    rw [htr_net_eq]
    have hlen1 : (tr_ss.append (⟨pqSalt⟩ : _root_.DY.Network.ExecEntryT)).length = msgIdx := by
      simp [msgIdx, tr_ss, Trace.append, Trace.length]
    rw [← hlen1]
    exact Symbolic.Swarm.CREF.TR.RecvDec.getMessageSentAt_attackerSend _ t_m
  have hext_kn : ∀ x ∈ ext, x.AttackerKnows tr_ss := by
    intro x hx
    simp only [ext, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hpq_kn
    · exact ht_m_on.1
  have hm_dec : m_step.decryptMsgIdx? = some msgIdx := by
    rcases hm_cases with rfl | ⟨_, rfl⟩ <;> rfl
  have hm_party_cls : m_step.cls = .party := by
    rcases hm_cases with rfl | ⟨_, rfl⟩ <;> rfl
  have hm_next_eq : m_mv.next tr_net = m_step.next tr_net := by
    rw [← hstm]; exact stepToMove_next (Or.inr (Or.inl hm_party_cls)) tr_net
  have hm_vis_eq : m_mv.vis tr_net =
      decVis tr_net (m_step.next tr_net) stateIdx msgIdx false := by
    have hnot_leak : ¬ Symbolic.Swarm.CREF.LeakKind m_mv := by
      rw [← hstm]; rcases hm_cases with rfl | ⟨_, rfl⟩ <;> intro h <;> cases h
    have his_setup : m_mv.isSetup = false := by
      rw [← hstm]; rcases hm_cases with rfl | ⟨_, rfl⟩ <;> rfl
    have hexp : exposures tr_net (m_mv.next tr_net) = [] :=
      exposures_nil_of_not_leakKind his_setup hnot_leak
    have hm_vis_raw : m_mv.vis tr_net =
        decVis tr_net (m_mv.next tr_net) stateIdx msgIdx false ++
          exposures tr_net (m_mv.next tr_net) := by
      rw [← hstm]; rcases hm_cases with rfl | ⟨_, rfl⟩ <;> rfl
    rw [hm_vis_raw, hexp, List.append_nil, hm_next_eq]
  have hrunVis_ext : runVis r (ms ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [m_mv])) =
      runVis r ms ++ m_mv.vis tr_net := by
    unfold runVis
    rw [← List.cons_append, Symbolic.Swarm.CREF.b5_runMoves_append_snd]
    change runVis r ms ++ (runMoves ([.attackerSend pqSalt, .attackerSend t_m] ++ [m_mv])
      (runTraceMoves r ms)).2 = _
    rw [htr]
    have hv1 : (Move.attackerSend pqSalt).vis tr_ss = [] := by
      have hraw : (Move.attackerSend pqSalt).vis tr_ss =
          [] ++ exposures tr_ss ((Move.attackerSend pqSalt).next tr_ss) := rfl
      rw [hraw, List.nil_append]
      exact exposures_nil_of_not_leakKind (m := .attackerSend pqSalt) rfl fun h => nomatch h
    have hn1 : (Move.attackerSend pqSalt).next tr_ss =
        tr_ss.append (⟨pqSalt⟩ : _root_.DY.Network.ExecEntryT) := by
      change ((_root_.DY.Network.sendMessage pqSalt >>= fun _ => pure ()).run tr_ss).2.val = _
      exact bind_pure_unit_snd _ tr_ss
    have hv2 : (Move.attackerSend t_m).vis ((Move.attackerSend pqSalt).next tr_ss) = [] := by
      have hraw : (Move.attackerSend t_m).vis ((Move.attackerSend pqSalt).next tr_ss) =
          [] ++ exposures _ ((Move.attackerSend t_m).next ((Move.attackerSend pqSalt).next tr_ss)) := rfl
      rw [hraw, List.nil_append]
      exact exposures_nil_of_not_leakKind (m := .attackerSend t_m) rfl fun h => nomatch h
    have hn2 : (Move.attackerSend t_m).next ((Move.attackerSend pqSalt).next tr_ss) = tr_net := by
      rw [hn1, htr_net_eq]
      exact bind_pure_unit_snd _ _
    have hrm_snd : (runMoves ([.attackerSend pqSalt, .attackerSend t_m] ++ [m_mv]) tr_ss).2 =
        m_mv.vis tr_net := by
      dsimp only [List.cons_append, List.nil_append, runMoves]
      rw [hv1, hv2, hn2, List.nil_append, List.nil_append, List.append_nil]
    exact congrArg (runVis r ms ++ ·) hrm_snd
  have htail_for : List.Forall₂ (EventMatchesEntry interp r S g₁)
      (.recv (wireWhisperTag :: body) :: (mid ++ [.accept pt]))
      (decVis tr_net (m_step.next tr_net) stateIdx msgIdx false) := by
    have hall := hmp₁.2.2.2.2.2
    rw [hrunVis_ext, hm_vis_eq] at hall
    exact forall2_append_inv hmp_pre.2.2.2.2.2.length_eq hall
  obtain ⟨hok_of_rec, hrand32⟩ := decrypt_step_ok_and_rand32 tr_net hm_cases
  have hrec_some : receivedPlaintext tr_net (m_step.next tr_net) ≠ none := by
    intro hnone
    unfold decVis at htail_for
    rw [hget_msg, hnone] at htail_for
    simp only [Option.map_some, Option.toList_some, Option.map_none, Option.toList_none,
      List.append_nil, List.singleton_append] at htail_for
    generalize hdrs0 : List.map (fun r => rngEntry r.1) (newRandoms tr_net (m_step.next tr_net)) =
      drs0 at htail_for
    have hdrs0_kind : ∀ u ∈ drs0, u.kind = .rng := by
      rw [← hdrs0]
      intro u hu
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hu; rfl
    cases htail_for with
    | cons _ hrest =>
      rcases hmid with rfl | rfl
      · cases hrest with
        | cons hacc _ =>
          have hk := hdrs0_kind _ List.mem_cons_self
          rw [← hacc.1] at hk; cases hk
      · cases hrest with
        | cons _ hrest2 =>
          cases hrest2 with
          | cons hacc _ =>
            have hk := hdrs0_kind _ (List.mem_cons_of_mem _ List.mem_cons_self)
            rw [← hacc.1] at hk; cases hk
  have hm_ok : m_step.ok tr_net = true := hok_of_rec hrec_some
  have hview_eq : stepView m_step tr_net (runWrapped ev) =
      decVis tr_net (m_step.next tr_net) stateIdx msgIdx false := by
    have hwrap : runWrapped ev = false := by
      unfold runWrapped
      cases hcmd_eq : ev.cmd <;> simp [hcmd] at hcmd_eq
      simp [hinp]
    have hexp_step : exposures tr_net (m_step.next tr_net) = [] := by
      rw [← hm_next_eq]
      have hnot_leak : ¬ Symbolic.Swarm.CREF.LeakKind m_mv := by
        rw [← hstm]; rcases hm_cases with rfl | ⟨_, rfl⟩ <;> intro h <;> cases h
      have his_setup : m_mv.isSetup = false := by
        rw [← hstm]; rcases hm_cases with rfl | ⟨_, rfl⟩ <;> rfl
      exact exposures_nil_of_not_leakKind his_setup hnot_leak
    rw [hwrap]
    rcases hm_cases with rfl | ⟨_, rfl⟩ <;>
      simp [stepView, hm_ok, hexp_step]
  let v_m := stepView m_step tr_net (runWrapped ev)
  refine ⟨vis ++ v_m, hext_kn, hm_dec, hfr.2,
    fun i hi => funext fun n => hfr.1 i hi n, hget_msg, ?_⟩
  have hReach_setup : (setupTrace r).Reachable reachability := hex_pre.2.2.1.2.1
  have hwf_ss : StepsWF ss (setupTrace r) := hex_pre.2.2.1.2.2.1
  have hReach_ss := Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.runSteps_reachable ss hReach_setup hwf_ss
  have htr_lt := Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable interp S g
    (runSteps ss (setupTrace r)).length hReach_ss (Nat.le_refl _)
  have hvis_lt :=
    Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.matchesEvents_visStampsLt
      hex_pre.2.2.2 hReach_setup hwf_ss (Nat.le_refl _) htr_lt
  have hgwf_vis : GhostWF g₁ vis :=
    Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.ghostWF_transfer hfr hvis_lt hex_pre.2.1
  rcases hrec_opt : receivedPlaintext tr_net (m_step.next tr_net) with _ | ptTerm
  · exact absurd hrec_opt hrec_some
  let inp : VisEntry := ⟨.recv, [t_m], .whisper, none⟩
  let drs : List VisEntry :=
    (newRandoms tr_net (m_step.next tr_net)).map (fun r => rngEntry r.1)
  let v_acc : VisEntry := ⟨.accept, [ptTerm], .single, none⟩
  have hdecVis_eq : decVis tr_net (m_step.next tr_net) stateIdx msgIdx false =
      inp :: (drs ++ [v_acc]) := by
    unfold decVis
    rw [hget_msg, hrec_opt]
    simp [inp, drs, v_acc]
  have hfor_3 : List.Forall₂ (EventMatchesEntry interp r S g₁)
      (.recv (wireWhisperTag :: body) :: (mid ++ [.accept pt]))
      (inp :: (drs ++ [v_acc])) := hdecVis_eq ▸ htail_for
  cases hfor_3 with
  | cons hinp_em hfor_mid_acc =>
    have hdrs_and_acc : DrawsMatch interp r S g₁ drs ev.coins ∧
        BytesMatchEntry interp r S g₁ .accept pt v_acc ∧
        GhostWF g₁ v_m := by
      rcases hmid with rfl | rfl
      · simp only [List.nil_append] at hfor_mid_acc
        have hdrs_nil : drs = [] := by
          have hl := hfor_mid_acc.length_eq
          simp at hl; exact hl
        rw [hdrs_nil, List.nil_append] at hfor_mid_acc
        cases hfor_mid_acc with
        | cons hacc_em _ =>
          refine ⟨⟨[], by simp, List.nil_prefix, ?_⟩,
            eventMatchesEntry_to_bytesMatchEntry (fun h => by cases h) (fun _ h => by cases h) hacc_em, ?_⟩
          · rw [hdrs_nil]; exact List.Forall₂.nil
          · refine ⟨?_, hgwf_vis.2.1, ?_⟩
            · intro v hv hvk
              dsimp only [v_m] at hv
              rw [hview_eq, hdecVis_eq, hdrs_nil] at hv
              simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with rfl | rfl <;> cases hvk
            · intro v hv hvk
              dsimp only [v_m] at hv
              rw [hview_eq, hdecVis_eq, hdrs_nil] at hv
              simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with rfl | rfl <;> cases hvk
      · have hdrs_len : drs.length = 1 := by
          have hl := hfor_mid_acc.length_eq
          simp at hl; omega
        have hnr_len : (newRandoms tr_net (m_step.next tr_net)).length = 1 := by
          simpa [drs] using hdrs_len
        rcases hnr_eq : newRandoms tr_net (m_step.next tr_net) with _ | ⟨r_pair, _ | _⟩
        · simp [hnr_eq] at hnr_len
        · have hr_mem : r_pair ∈ newRandoms tr_net (m_step.next tr_net) := by simp [hnr_eq]
          obtain ⟨r_idx, hidx_mem, hr_opt⟩ := List.mem_filterMap.mp hr_mem
          have hr_ge : tr_net.length ≤ r_idx := by
            simp only [newIndices, List.mem_range'_1] at hidx_mem
            exact hidx_mem.1
          rcases hat_r : ((m_step.next tr_net).at? r_idx : Option _root_.DY.Random.ExecEntryT) with _ | r_e
          · simp [hat_r] at hr_opt
          · simp only [hat_r, Option.map_some, Option.some.injEq] at hr_opt
            have hr_len32 : r_e.length = 32 := hrand32 r_idx hr_ge r_e hat_r
            have hdrs_eq : drs = [rngEntry (randTerm r_idx 32)] := by
              simp [drs, hnr_eq, ← hr_opt, hr_len32]
            rw [hdrs_eq] at hfor_mid_acc
            simp only [List.singleton_append] at hfor_mid_acc
            cases hfor_mid_acc with
            | cons hrng_em hfor_acc =>
              cases hfor_acc with
              | cons hacc_em _ =>
                refine ⟨⟨[ev.coins], ?_, ⟨[], by simp⟩, ?_⟩,
                  eventMatchesEntry_to_bytesMatchEntry (fun h => by cases h) (fun _ h => by cases h) hacc_em, ?_⟩
                · intro p hp
                  simp only [List.mem_singleton] at hp
                  subst hp
                  intro hnil; simp [hnil] at hcoins
                · rw [hdrs_eq]
                  exact .cons (eventMatchesEntry_to_bytesMatchEntry (fun h => by cases h) (fun _ h => by cases h) hrng_em) .nil
                · refine ⟨?_, hgwf_vis.2.1, ?_⟩
                  · intro v hv hvk ts n hn htm
                    dsimp only [v_m] at hv
                    rw [hview_eq, hdecVis_eq, hdrs_eq] at hv
                    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hv
                    rcases hv with rfl | rfl | rfl
                    · cases hvk
                    · simp only [rngEntry, List.mem_singleton] at htm
                      obtain ⟨rfl, rfl⟩ := randTerm_inj (interp := interp) (S := S) hn (by decide) htm
                      have hgam_eq : gamma interp S g₁ (randTerm ts 32) = ev.coins := by
                        have hm2 := hrng_em.2
                        simp [rngEntry, eventBytes] at hm2
                        exact hm2
                      rw [Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.gamma_randTerm_eq interp S g₁ ts 32
                        (by decide)] at hgam_eq
                      rw [hgam_eq, hcoins]
                    · cases hvk
                  · intro v hv hvk
                    dsimp only [v_m] at hv
                    rw [hview_eq, hdecVis_eq, hdrs_eq] at hv
                    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hv
                    rcases hv with rfl | rfl | rfl <;> cases hvk
        · simp [hnr_eq] at hnr_len
    obtain ⟨hdrs_m, hacc_bme, hgwf_vm⟩ := hdrs_and_acc
    have hgwf_all : GhostWF g₁ (vis ++ v_m) := by
      refine ⟨fun v hv hk ts n hn hmem => ?_, hgwf_vis.2.1, fun v hv hk => ?_⟩
      · rcases List.mem_append.mp hv with hv | hv
        · exact hgwf_vis.1 v hv hk ts n hn hmem
        · exact hgwf_vm.1 v hv hk ts n hn hmem
      · rcases List.mem_append.mp hv with hv | hv
        · exact hgwf_vis.2.2 v hv hk
        · exact hgwf_vm.2.2 v hv hk
    have hswf_net : StepsWF (ext.map Step.network) tr_ss := by
      have htm1 : t_m.AttackerKnows ((Step.network pqSalt).next tr_ss) :=
        _root_.DY.Bytes.AttackerKnows_le _ _ _ (Trace.append_le _ _) ht_m_on.1
      exact ⟨hpq_kn, trivial, htm1, trivial, trivial⟩
    have hcur_net : isCurrentSnapshot tr_net stateIdx = true := by
      have heq : tr_net = runSteps (ext.map Step.network) tr_ss := runTrace_append r ss (ext.map Step.network)
      rw [heq, isCurrentSnapshot_runSteps_network]
      exact hcur
    have hm_pre_loc : m_step.PreCond tr_net ∧ m_step.LocalOk tr_net := by
      rcases hm_cases with rfl | ⟨_, rfl⟩
      · exact ⟨stepIn_preCond_of _root_.DY.Libsignal.TripleRatchet.messageDecrypt.reachability
          (ev.party, stateIdx, msgIdx, pqIdx, spqrMsgIdx) tr_net hcur_net, trivial⟩
      · exact ⟨stepIn_preCond_of _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
          (ev.party, stateIdx, msgIdx, _, pqIdx, spqrMsgIdx) tr_net hcur_net, trivial⟩
    have hswf_all : StepsWF (ss ++ ext.map Step.network ++ [m_step]) (setupTrace r) := by
      rw [Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.stepsWF_append_iff,
        Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.stepsWF_append_iff]
      refine ⟨⟨hwf_ss, hswf_net⟩, ?_⟩
      have htr_eq_net : runSteps (ss ++ ext.map Step.network) (setupTrace r) = tr_net := rfl
      rw [htr_eq_net]
      exact ⟨hm_pre_loc.1, hm_pre_loc.2, trivial⟩
    have hssf_all : StepsStateFaithful r (ss ++ ext.map Step.network ++ [m_step]) :=
      stepsStateFaithful_snoc_decrypt hex_pre.2.2.1.2.2.2
        fun p k b hld => by
          rcases hm_cases with rfl | ⟨_, rfl⟩ <;>
            (simp only [Step.stateLoad?, Option.some.injEq, Prod.mk.injEq] at hld;
             rcases hld with ⟨_, rfl, _⟩; exact hcur)
    have hrf_ua : ReadsFaithfully interp r S g₁ tr_net inp ev.input := by
      rw [hinp]
      have hga := Symbolic.Swarm.CREF.cbadG2_gammaAgree_of_sigmaFrame interp S hfr
      obtain ⟨hkn_tm, hrest_g₁⟩ := recvRepOn_transfer hga htr_lt ht_m_on
      have hkn_tm1 : t_m.AttackerKnows (tr_ss.append (⟨pqSalt⟩ : _root_.DY.Network.ExecEntryT)) :=
        _root_.DY.Bytes.AttackerKnows_le _ _ _ (Trace.append_le _ _) hkn_tm
      have hkn_tm2 : t_m.AttackerKnows tr_net := by
        rw [htr_net_eq]
        exact _root_.DY.Bytes.AttackerKnows_le _ _ _ (Trace.append_le _ _) hkn_tm1
      exact ⟨hkn_tm2, hrest_g₁⟩
    have hpf_ua : PathFaithfulAt interp S g₁ tr_net m_step ev.input := by
      rw [hinp]
      intro q hq
      simp [parsePreKeyWire, wireWhisperTag,
        _root_.DY.Libsignal.PQXDH.Refinement.wirePrekeyTag] at hq
    have hrm_ua : RunMatches interp r S g₁ tr_net m_step ev v_m (activeBundleIds evs_pre) := by
      have hkind : inputKind ev = .recv := by simp [inputKind, hcmd]
      have hout_m : OutputsMatch interp r S g₁ ev [v_acc] (activeBundleIds evs_pre) := by
        simp only [OutputsMatch, hexit, hcmd]
        exact ⟨v_acc, rfl, hacc_bme⟩
      refine ⟨hm_party_cls, ?_, ?_, ?_, hm_ok, ⟨pt, hexit⟩, rfl,
        inp, drs, [v_acc], hview_eq.trans hdecVis_eq, ?_, hdrs_m, hout_m, hrf_ua, hpf_ua⟩
      · rcases hm_cases with rfl | ⟨_, rfl⟩ <;> rfl
      · rw [hcmd]; rcases hm_cases with rfl | ⟨_, rfl⟩ <;> trivial
      · rcases hm_cases with rfl | ⟨_, rfl⟩ <;> trivial
      · rw [hkind, hinp]; exact eventMatchesEntry_to_bytesMatchEntry (fun h => by cases h) (fun _ h => by cases h) hinp_em
    have hme_pre₁ : MatchesEvents interp r S g₁ (setupTrace r) ss evs_pre vis :=
      Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.matchesEvents_transfer hfr
        hex_pre.2.2.2 hReach_setup hwf_ss (Nat.le_refl _)
    have hrm_ua' : RunMatches interp r S g₁
        (runSteps (ext.map Step.network) (runSteps ss (setupTrace r))) m_step ev v_m
        (activeBundleIds evs_pre) := by
      have heq_tr : runSteps (ext.map Step.network) (runSteps ss (setupTrace r)) = tr_net :=
        (runTrace_append r ss (ext.map Step.network)).symm
      exact heq_tr ▸ hrm_ua
    have hme_all : MatchesEvents interp r S g₁ (setupTrace r)
        (ss ++ ext.map Step.network ++ [m_step]) (evs_pre ++ [.run ev]) (vis ++ v_m) :=
      Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer.matchesEvents_snoc_run1 hme_pre₁
        (fun x hx => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; rfl) hrm_ua'
    exact ⟨hmp₁.1, hgwf_all, ⟨hex_pre.2.2.1.1, hReach_setup, hswf_all, hssf_all⟩, hme_all⟩

end Symbolic.Proofs.Swarm.UA.BI.G.RecvStep
