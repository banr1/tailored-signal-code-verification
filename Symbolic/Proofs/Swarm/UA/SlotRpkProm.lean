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
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3PureGates
import Symbolic.Proofs.Swarm.CREF.CBadG2.StampsReachBob
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptCollisionPickPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyPromSlot
import Symbolic.Proofs.Swarm.CREF.Cli.World.CallCountPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.TR.MessageKeyCurrentInv
import Symbolic.Proofs.Swarm.CREF.Xpl.NoRatchet
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L02GoodExit0Cut
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L04BridgeBQuietFail
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L05BridgeCCaseA
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L06BridgeCCaseB
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L11SlotRpkPromCli
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L11SlotRpkPromCliRawKn
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.SlotInitTransfer
import Symbolic.Proofs.Swarm.UA.SlotRpkNOHelpers
import Symbolic.Proofs.Swarm.UA.SlotRpkPromAux
import Symbolic.Proofs.Swarm.UA.XlateInv
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Bob Session-Promotion Pre-Key `recv` Slot

Proves `slot_rpk_prom_ua_of_xlate` and `slot_rpk_prom_ua_of_exc_w`, preserving `PqTurnSim1A`
and `UAInv` across Bob's matching-session pre-key `recv` call by lifting a non-colliding
move-level decrypt witness to `ModelAcceptsTermAfterAttackerSendsClassical` on exit `0` and
extending rejected runs on exit `1`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.SlotRpkProm

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Traceful ExecTraceTypes)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent CliEvent)
open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed (reachability)
open _root_.DY.Libsignal.Composed.Refinement (ProtocolSetup Ghost OpaqueSymbolSemantics Step VisEntry
  ProtocolSetupWF ExplainsClassical MatchesEventsClassical RunMatches RunRejected ecKey gamma
  pubBytes secretBytes
  runSteps runTrace setupTrace PreKeyFields parsePreKeyWire EligibleForSessionPromotion PqFromHonest
  KnownBaseKeyOn recvRepresentationsOn RecvCollisionOn ReselectCollisionOn honestSaltsOf
  plaintextTerms prefixTerms stepView runWrapped)
open _root_.DY.Libsignal.Composed.Refinement.Cli (CliTurn CliCall DirectorySnapshot InputsFor StdinBounded
  FilesBounded BobCallAllowed runEventOf ReadCollisionCliClassical ModelAcceptsTermAfterAttackerSendsClassical SignalMsgAcceptedOnlyViaCollisionClassical
  CollisionAfterExplainedPrefixClassical NextEventCollidesClassical ExternContractsHoldCli peerOf PqModelRel ModelAgree)
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3 (PqTurnSim1A)
open _root_.DY.Libsignal.TripleRatchet (TRState isCurrentSnapshot)
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.SignalSession (Inputs)
open Symbolic.Swarm.CREF (compSemOf compSemOf_ready SemReady)
open Symbolic.Swarm.CREF.Cli (interpOfParams)
open Symbolic.Swarm.Coinsplit.Lift (CliLiveAtCli)
open Symbolic.Proofs.Swarm.UA.Defs (UASlotRpkPromSpec XlateInvSpec XlateExcWSpec callsOf flatEvents)
open Symbolic.Proofs.Swarm.UA.Base (collisionAtCli_append explains_snoc_rejected)
open Symbolic.Proofs.Swarm.UA.SlotRpkNOHelpers (aliceRecordPendingInSession_bob_recv)
open Symbolic.Proofs.Swarm.UA.XlateInv (xlate_inv)
open Symbolic.Proofs.Swarm.UA.SlotRpkPromAux (not_readCollisionCli_snoc_rejected
  recvCollision_iff_of_terms not_readCollisionCli_of_acceptsViaCli ValidLoadStep stepToLoadMove
  validLoadStep_of_matchesEvents run_bind_pure_unit_isSome run_bind_pure_unit_snd
  stepToLoadMove_next stepToLoadMove_ok stepsStateFaithful_snoc_of_isCurrentSnapshot
  recvRepresentations_eq_of_trace knownBaseKey_iff_of_trace reselectCollision_iff_of_terms
  runMoves_append_eq runMoves_attackerSend_map forall₂_append_eq_length_inv randTerm_inj_of_ne_zero
  NoTREvFrom quietOnNone_messageDecrypt quietOnNone_messageDecryptSkipped
  receivedPlaintext_eq_none_of_xquietFrom bobDoneBaseKeys_runSteps_network
  attackerKnows_runSteps_network stepsWF_network_map mid_accept_take_inv forall₂_mem_left)

/-! ## Witness Lifting and Slot Theorems -/

private def NoRandLocal {α : Type} (x : Traceful α) : Prop :=
  ∀ (tr : ExecTrace) (i : Nat),
    ((x.run tr).2.val.at? i : Option _root_.DY.Random.ExecEntryT) =
      (tr.at? i : Option _root_.DY.Random.ExecEntryT)

private theorem noRandLocal_of_fix {α : Type} {x : Traceful α}
    (hs : Symbolic.Swarm.CREF.XplSteps.XFix x) : NoRandLocal x :=
  fun tr _ => by rw [hs tr]

private theorem noRandLocal_bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : NoRandLocal x) (hf : ∀ a, NoRandLocal (f a)) : NoRandLocal (x >>= f) := by
  intro tr i
  rw [Symbolic.Swarm.CREF.TR.RecvDec.run_bind_snd]
  rcases (x.run tr).1 with _ | a
  · exact hx tr i
  · exact (hf a (x.run tr).2.val i).trans (hx tr i)

private theorem noRandLocal_append_nonRand {E : Type} [ExecTraceTypes.Has E] (e : E)
    (hnone : (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option _root_.DY.Random.ExecEntryT) = none) :
    NoRandLocal (_root_.DY.appendEntry e) := by
  intro tr i
  rw [Symbolic.DYBridge.DY.appendEntry_eq_1]
  erw [_root_.DY.Traceful.run_mk]
  exact Symbolic.Swarm.CREF.TR.RecvDec.at?_append_non_entry tr e hnone i

private theorem noRandLocal_logSkippedKeys (s : _root_.DY.Libsignal.TripleRatchet.SessionInfo)
    (rk : _root_.DY.Bytes) (rIdx stateIdx : Nat) (ck : _root_.DY.Bytes) (idx : UInt32) (n : Nat) :
    NoRandLocal (_root_.DY.Libsignal.TripleRatchet.logSkippedKeys s rk rIdx stateIdx ck idx n) := by
  intro tr i
  rw [(Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeys_run s rk rIdx stateIdx ck idx n tr).2]
  induction n generalizing ck idx tr with
  | zero => rfl
  | succ k ih =>
    unfold Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeysTr
    exact (ih _ _ _).trans (Symbolic.Swarm.CREF.TR.RecvDec.at?_append_non_entry tr _ rfl i)

private theorem noRandLocal_logMessageKeyAndStore (me : Participant)
    (s : _root_.DY.Libsignal.TripleRatchet.SessionInfo)
    (dir : _root_.DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : _root_.DY.Bytes)
    (cnt : UInt32) (r par : Nat) (st : TRState) :
    NoRandLocal (_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
      me s dir seed pqSalt cnt r par st) := by
  unfold _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine noRandLocal_bind
    (by
      rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
      exact noRandLocal_bind
        (noRandLocal_append_nonRand
          ({ ev := _ } : _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.TripleRatchet.TREvent)
          rfl)
        fun _ => noRandLocal_of_fix fun _ => by erw [_root_.DY.Traceful.run_pure])
    fun _ => ?_
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]
  exact noRandLocal_append_nonRand
    ({ st := _ } : _root_.DY.PersistentGlobalState.State.ExecEntryT
      (_root_.DY.PersistentLocalState.LocalState TRState))
    rfl

private theorem xfix_receiveSignalMsg_local (idx : Nat) :
    Symbolic.Swarm.CREF.XplSteps.XFix (_root_.DY.Libsignal.TripleRatchet.receiveSignalMsg idx) := by
  unfold _root_.DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine Symbolic.Swarm.CREF.XplSteps.xfix_bind
    (Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage idx) fun _ => ?_
  split <;> first
    | exact fun _ => by erw [_root_.DY.Traceful.run_failure]
    | exact Symbolic.Swarm.CREF.XplSteps.xfix_bind
        (Symbolic.Swarm.CREF.XplSteps.xfix_guard _) fun _ _ => by erw [_root_.DY.Traceful.run_pure]

private theorem xfix_liftM_err {α : Type} (o : _root_.DY.Err α) :
    Symbolic.Swarm.CREF.XplSteps.XFix (liftM o) := by
  intro tr
  cases o <;> (dsimp only [liftM, monadLift, MonadLift.monadLift]; erw [_root_.DY.Traceful.run_mk])

private theorem xfix_verifyMacAndDecrypt_local (st : TRState)
    (msg : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg) (s seed : _root_.DY.Bytes) :
    Symbolic.Swarm.CREF.XplSteps.XFix
      (_root_.DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg s seed) := by
  unfold _root_.DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  refine Symbolic.Swarm.CREF.XplSteps.xfix_bind
    (Symbolic.Swarm.CREF.XplSteps.xfix_guard _) fun _ => xfix_liftM_err _

private theorem newRandoms_eq_nil_at {tr t : ExecTrace}
    (h : ∀ i, tr.length ≤ i → (t.at? i : Option _root_.DY.Random.ExecEntryT) = none) :
    _root_.DY.Libsignal.Composed.Refinement.newRandoms tr t = [] := by
  unfold _root_.DY.Libsignal.Composed.Refinement.newRandoms
  rw [List.filterMap_eq_nil_iff]
  intro i hi
  obtain ⟨hlo, _⟩ := List.mem_range'_1.mp hi
  rw [h i hlo]
  rfl

private theorem newRandoms_eq_nil_of_noRandLocal {α : Type} {x : Traceful α} {tr : ExecTrace}
    (h : NoRandLocal x) :
    _root_.DY.Libsignal.Composed.Refinement.newRandoms tr (x.run tr).2.val = [] :=
  newRandoms_eq_nil_at fun i hi =>
    (h tr i).trans (Symbolic.Swarm.CREF.TR.RecvDec.at?_eq_none_of_le tr hi)

private theorem newRandoms_messageDecryptSkipped_nil (me : Participant)
    (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace) :
    _root_.DY.Libsignal.Composed.Refinement.newRandoms tr
      ((Step.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).next tr) = [] := by
  change _root_.DY.Libsignal.Composed.Refinement.newRandoms tr
    ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
      me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run tr).2.val = []
  apply newRandoms_eq_nil_of_noRandLocal
  unfold _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine noRandLocal_bind (noRandLocal_of_fix
    (Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState me stateIdx)) fun st => ?_
  refine noRandLocal_bind (noRandLocal_of_fix
    (xfix_receiveSignalMsg_local msgIdx)) fun msg => ?_
  refine noRandLocal_bind (noRandLocal_of_fix
    (Symbolic.Swarm.CREF.XplSteps.xfix_getEntry skIdx)) fun e => ?_
  cases e.ev with
  | SkippedKeyStored s pk n seed rIdx srcIdx =>
    dsimp only
    refine noRandLocal_bind (noRandLocal_of_fix
      (Symbolic.Swarm.CREF.XplSteps.xfix_guard _)) fun _ => ?_
    refine noRandLocal_bind (noRandLocal_of_fix
      (Symbolic.Swarm.CREF.XplSteps.xfix_guardTrace _)) fun _ => ?_
    rcases _root_.DY.Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; exact noRandLocal_of_fix fun _ => by erw [_root_.DY.Traceful.run_failure]
    · dsimp only
      refine noRandLocal_bind
        (by
          rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1]
          exact noRandLocal_append_nonRand ({ msg := key } : _root_.DY.Network.ExecEntryT) rfl)
        fun _ => ?_
      refine noRandLocal_bind (noRandLocal_of_fix
        (Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage pqIdx)) fun pqSalt => ?_
      refine noRandLocal_bind (noRandLocal_of_fix
        (xfix_verifyMacAndDecrypt_local st msg pqSalt seed)) fun _ => ?_
      refine noRandLocal_bind
        (by
          rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
          exact noRandLocal_bind
            (noRandLocal_append_nonRand
              ({ ev := _ } : _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.TripleRatchet.TREvent)
              rfl)
            fun _ => noRandLocal_of_fix fun _ => by erw [_root_.DY.Traceful.run_pure])
        fun _ => ?_
      refine noRandLocal_bind
        (by
          rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
          exact noRandLocal_bind
            (noRandLocal_append_nonRand
              ({ ev := _ } : _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.TripleRatchet.TREvent)
              rfl)
            fun _ => noRandLocal_of_fix fun _ => by erw [_root_.DY.Traceful.run_pure])
        fun _ => ?_
      exact noRandLocal_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
  | _ => dsimp only; exact noRandLocal_of_fix fun _ => by erw [_root_.DY.Traceful.run_failure]

private theorem newRandoms_messageDecrypt_singleton (me : Participant)
    (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace)
    (hnr : _root_.DY.Libsignal.Composed.Refinement.newRandoms tr
      ((Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).next tr) ≠ []) :
    _root_.DY.Libsignal.Composed.Refinement.newRandoms tr
      ((Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).next tr) =
      [(_root_.DY.Libsignal.Composed.Refinement.randTerm tr.length 32, 32)] := by
  have hnext_eq : (Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).next tr =
      ((_root_.DY.Libsignal.Composed.Refinement.Move.decrypt
        me stateIdx msgIdx pqIdx spqrMsgIdx false).next tr) :=
    (stepToLoadMove_next (s := .messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) trivial tr).symm
  have hact_eq : (Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).next tr =
      ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt
        me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val := rfl
  rcases hst : ((_root_.DY.PersistentLocalState.getLocalState me stateIdx :
      Traceful TRState).run tr).1 with _ | st
  · exfalso; apply hnr; rw [hact_eq]; apply newRandoms_eq_nil_at; intro i hi
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
    rw [Symbolic.Swarm.CREF.TR.RecvDec.run_bind_snd, hst,
      Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState me stateIdx tr]
    exact Symbolic.Swarm.CREF.TR.RecvDec.at?_eq_none_of_le tr hi
  · rcases hrcv : ((_root_.DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx).run tr).1 with _ | msg
    · exfalso; apply hnr; rw [hact_eq]; apply newRandoms_eq_nil_at; intro i hi
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
      rw [Symbolic.Swarm.CREF.TR.RecvDec.run_bind_snd, hst,
        Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState me stateIdx tr]
      dsimp only
      rw [Symbolic.Swarm.CREF.TR.RecvDec.run_bind_snd, hrcv, xfix_receiveSignalMsg_local msgIdx tr]
      exact Symbolic.Swarm.CREF.TR.RecvDec.at?_eq_none_of_le tr hi
    · rcases hrc : _root_.DY.Libsignal.TripleRatchet.recvChainFor st.toDRState msg.ratchetKey
          with _ | ⟨c, b⟩
      · exfalso; apply hnr; rw [hact_eq]; apply newRandoms_eq_nil_at; intro i hi
        simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
        rw [Symbolic.Swarm.CREF.TR.RecvDec.run_bind_snd, hst,
          Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState me stateIdx tr]
        dsimp only
        rw [Symbolic.Swarm.CREF.TR.RecvDec.run_bind_snd, hrcv, xfix_receiveSignalMsg_local msgIdx tr]
        dsimp only
        have hens : ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st msg.ratchetKey).run tr).1 = none ∧
            ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st msg.ratchetKey).run tr).2.val = tr := by
          simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; rw [hrc]; dsimp only
          erw [_root_.DY.Traceful.run_failure]; exact ⟨rfl, rfl⟩
        rw [Symbolic.Swarm.CREF.TR.RecvDec.run_bind_snd, hens.1, hens.2]
        exact Symbolic.Swarm.CREF.TR.RecvDec.at?_eq_none_of_le tr hi
      · cases b
        · exfalso; apply hnr; rw [hact_eq]; apply newRandoms_eq_nil_at; intro i hi
          simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
          rw [Symbolic.Swarm.CREF.TR.RecvDec.run_bind_snd, hst,
            Symbolic.Swarm.CREF.XplSteps.xfix_getLocalState me stateIdx tr]
          dsimp only
          rw [Symbolic.Swarm.CREF.TR.RecvDec.run_bind_snd, hrcv, xfix_receiveSignalMsg_local msgIdx tr]
          dsimp only
          have hens : ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st msg.ratchetKey).run tr).1 =
              some (st, c, false) ∧
              ((_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st msg.ratchetKey).run tr).2.val = tr := by
            simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; rw [hrc]; dsimp only
            erw [_root_.DY.Traceful.run_pure]; exact ⟨rfl, rfl⟩
          rw [Symbolic.Swarm.CREF.TR.RecvDec.run_bind_snd, hens.1, hens.2]; dsimp only
          rcases _root_.DY.Libsignal.TripleRatchet.consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
          · dsimp only; erw [_root_.DY.Traceful.run_failure]
            exact Symbolic.Swarm.CREF.TR.RecvDec.at?_eq_none_of_le tr hi
          · dsimp only
            rcases _root_.DY.Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
            · dsimp only; erw [_root_.DY.Traceful.run_failure]
              exact Symbolic.Swarm.CREF.TR.RecvDec.at?_eq_none_of_le tr hi
            · dsimp only
              refine ((noRandLocal_bind
                (by
                  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1]
                  exact noRandLocal_append_nonRand ({ msg := key } : _root_.DY.Network.ExecEntryT) rfl)
                fun _ =>
                noRandLocal_bind (noRandLocal_of_fix
                  (Symbolic.Swarm.CREF.XplSteps.xfix_receiveMessage pqIdx)) fun pqSalt =>
                noRandLocal_bind (noRandLocal_of_fix
                  (xfix_verifyMacAndDecrypt_local st msg pqSalt seed)) fun _ => ?_) tr i).trans
                (Symbolic.Swarm.CREF.TR.RecvDec.at?_eq_none_of_le tr hi)
              simp only [Bool.false_eq_true, ↓reduceIte]
              refine noRandLocal_bind (noRandLocal_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
              refine noRandLocal_bind
                (by
                  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
                  exact noRandLocal_bind
                    (noRandLocal_append_nonRand
                      ({ ev := _ } : _root_.DY.ProtocolEvent.ExecEntryT
                        _root_.DY.Libsignal.TripleRatchet.TREvent)
                      rfl)
                    fun _ => noRandLocal_of_fix fun _ => by erw [_root_.DY.Traceful.run_pure])
                fun _ => ?_
              exact noRandLocal_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
        · rw [hnext_eq]
          exact Symbolic.Swarm.CREF.newRandoms_decrypt_of_recvChainFor_true
            (pqIdx := pqIdx) (spqrMsgIdx := spqrMsgIdx) (wrapped := false) hst hrcv hrc


set_option maxHeartbeats 400000 in
private theorem acceptsViaCli_of_acceptsVia_prom
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {evs_pre : List CliEvent} {c : CliCall} {body out : HwBytes} {q : PreKeyFields}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {τ : List MachineEvent} {ms : List _root_.DY.Libsignal.Composed.Refinement.Move}
    {mid : List MachineEvent} {t : _root_.DY.Bytes}
    (hex_pre : ExplainsClassical interp r S g ss vis evs_pre)
    (hex_mv : _root_.DY.Libsignal.Composed.Refinement.ExplainsMoves interp r S who ok g ms τ)
    (htr_eq : _root_.DY.Libsignal.Composed.Refinement.runTraceMoves r ms = runTrace r ss)
    (hwho : who[(_root_.DY.Libsignal.Composed.Refinement.callStarts τ).length]? = some r.bob)
    (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r r.bob))
    (hstdin : c.stdin = _root_.CryptoVerification.E2E.wirePrekey :: body)
    (hcoins : c.coins.length = 32)
    (hq_wire : parsePreKeyWire (_root_.CryptoVerification.E2E.wirePrekey :: body) = some q)
    (hq_ver : q.version = 4)
    (hq_ik : q.identityKey.take 33 = ecKey (pubBytes interp (secretBytes r 0)))
    (hkb : KnownBaseKeyOn interp S g (runTrace r ss) q)
    (hmid : mid = [] ∨ mid = [.rng c.coins])
    (ht : t ∈ recvRepresentationsOn interp S g (runTrace r ss) q.message)
    (hacc : _root_.DY.Libsignal.Composed.Refinement.ModelAcceptsTermAfterCoinSplit interp r S who ok g ms τ
      (.recv (_root_.CryptoVerification.E2E.wirePrekey :: body)) (mid ++ [.accept out]) t) :
    ModelAcceptsTermAfterAttackerSendsClassical interp r S g ss evs_pre (runEventOf c (some (0, out))) t := by
  let ev := runEventOf c (some (0, out))
  let wpk := _root_.CryptoVerification.E2E.wirePrekey
  have hev_in : ev.input = wpk :: body := by
    dsimp only [ev, wpk]
    simp [runEventOf, _root_.DY.Libsignal.Composed.Refinement.Cli.runInput, hcmd, hstdin]
  have hev_cmd : ev.cmd = .recv (peerOf r r.bob) := by
    dsimp only [ev]
    simp [runEventOf, hcmd]
  have hev_pty : ev.party = r.bob := by
    dsimp only [ev]
    simp [runEventOf, hbob]
  have hev_kind : _root_.DY.Libsignal.Composed.Refinement.inputKind ev = .recv := by
    dsimp only [ev]
    simp [runEventOf, hcmd, _root_.DY.Libsignal.Composed.Refinement.inputKind]
  obtain ⟨ext, m_mv, msgIdx, k, pt', g₁, hext_kn, hm_dec, hg_addr, hg_sig, hmsg_mv,
    htau2_k, htau2_rng, hexpl₁⟩ := hacc
  obtain ⟨hpt_eq, htake_eq⟩ := mid_accept_take_inv hmid htau2_k htau2_rng
  subst pt'
  rw [htake_eq] at hexpl₁
  have hext_kn_ua : ∀ x ∈ ext, x.AttackerKnows (runTrace r ss) := htr_eq ▸ hext_kn
  have hfr : Symbolic.Swarm.CREF.CBadSigmaFrame g g₁ (runTrace r ss).length :=
    ⟨fun i hi n => by rw [hg_sig i (htr_eq ▸ hi)], hg_addr⟩
  have hfr_mv : Symbolic.Swarm.CREF.CBadSigmaFrame g g₁
      (_root_.DY.Libsignal.Composed.Refinement.runTraceMoves r ms).length := htr_eq.symm ▸ hfr
  let tr₁ := runTrace r (ss ++ ext.map Step.network)
  have htr₁_steps : tr₁ = runSteps (ext.map Step.network) (runTrace r ss) := by
    unfold tr₁; exact Symbolic.Proofs.Swarm.UA.Base.runTrace_append r ss (ext.map Step.network)
  let v_ms := (_root_.DY.Libsignal.Composed.Refinement.runMoves ms (setupTrace r)).2
  have hms_pair : _root_.DY.Libsignal.Composed.Refinement.runMoves ms (setupTrace r) =
      (runTrace r ss, v_ms) := by
    refine Prod.ext ?_ rfl
    unfold _root_.DY.Libsignal.Composed.Refinement.runTraceMoves at htr_eq
    simp only [_root_.DY.Libsignal.Composed.Refinement.runMoves,
      _root_.DY.Libsignal.Composed.Refinement.setupMove_next_nil r] at htr_eq
    exact htr_eq
  have hrm_ext : _root_.DY.Libsignal.Composed.Refinement.runMoves
      (ms ++ ext.map _root_.DY.Libsignal.Composed.Refinement.Move.attackerSend) (setupTrace r) =
      (tr₁, v_ms) := by
    rw [runMoves_append_eq, hms_pair]
    dsimp only
    rw [runMoves_attackerSend_map, List.append_nil, ← htr₁_steps]
  have htr₁_mv : _root_.DY.Libsignal.Composed.Refinement.runTraceMoves r
      (ms ++ ext.map _root_.DY.Libsignal.Composed.Refinement.Move.attackerSend) = tr₁ := by
    unfold _root_.DY.Libsignal.Composed.Refinement.runTraceMoves
    simp only [_root_.DY.Libsignal.Composed.Refinement.runMoves,
      _root_.DY.Libsignal.Composed.Refinement.setupMove_next_nil r]
    exact congrArg Prod.fst hrm_ext
  have hvis_ext : _root_.DY.Libsignal.Composed.Refinement.runVis r
      (ms ++ ext.map _root_.DY.Libsignal.Composed.Refinement.Move.attackerSend) =
      _root_.DY.Libsignal.Composed.Refinement.runVis r ms := by
    unfold _root_.DY.Libsignal.Composed.Refinement.runVis
    simp only [_root_.DY.Libsignal.Composed.Refinement.runMoves,
      _root_.DY.Libsignal.Composed.Refinement.setupMove_next_nil r, hrm_ext, hms_pair]
  have hvis_full : _root_.DY.Libsignal.Composed.Refinement.runVis r
      (ms ++ ext.map _root_.DY.Libsignal.Composed.Refinement.Move.attackerSend ++ [m_mv]) =
      _root_.DY.Libsignal.Composed.Refinement.runVis r ms ++ m_mv.vis tr₁ := by
    rw [_root_.DY.Libsignal.Composed.Refinement.runVis_snoc, hvis_ext, htr₁_mv]
  have hmsg_ua : tr₁.getMessageSentAt msgIdx = some t := htr₁_mv ▸ hmsg_mv
  have hlen_τ : τ.length = (_root_.DY.Libsignal.Composed.Refinement.runVis r ms).length :=
    hex_mv.1.2.2.2.2.2.length_eq
  have hf₂_full := hexpl₁.1.2.2.2.2.2
  rw [hvis_full] at hf₂_full
  have hf₂_step : List.Forall₂
      (_root_.DY.Libsignal.Composed.Refinement.EventMatchesEntry interp r S g₁)
      (.recv (wpk :: body) :: (mid ++ [.accept out])) (m_mv.vis tr₁) :=
    (forall₂_append_eq_length_inv hlen_τ hf₂_full).2
  have hreach_next : (m_mv.next tr₁).Reachable reachability := by
    have hr_full := hexpl₁.1.2.1.2.2.1.1
    unfold _root_.DY.Libsignal.Composed.Refinement.runTraceMoves at hr_full
    dsimp only [_root_.DY.Libsignal.Composed.Refinement.runMoves] at hr_full
    rw [_root_.DY.Libsignal.Composed.Refinement.setupMove_next_nil r,
      runMoves_append_eq, hrm_ext] at hr_full
    simpa only [_root_.DY.Libsignal.Composed.Refinement.runMoves] using hr_full
  have hex_acc_vis : ∃ v ∈ m_mv.vis tr₁, v.kind = .accept := by
    have hmem_acc : MachineEvent.accept out ∈
        (.recv (wpk :: body) :: (mid ++ [.accept out])) := by simp
    obtain ⟨v, hv_mem, hv_em⟩ := forall₂_mem_left hf₂_step hmem_acc
    exact ⟨v, hv_mem, hv_em.1.symm⟩
  have hex_unified : ∃ (me : Participant) (stateIdx : Nat) (wrapped : Bool) (s : Step),
      m_mv.party? = some me ∧
      s.decryptMsgIdx? = some msgIdx ∧ s.cls = .party ∧ s.party? = some me ∧
      s.FitsCmd ev.cmd ∧ s.MatchesSetupPeer r ∧ ValidLoadStep s ∧ s.next tr₁ = m_mv.next tr₁ ∧
      (∀ p k b, s.stateLoad? = some (p, k, b) → p = me ∧ k = stateIdx ∧ b = true) ∧
      s.PreCond tr₁ ∧ s.LocalOk tr₁ ∧ isCurrentSnapshot tr₁ stateIdx = true ∧
      (s.ok tr₁ = false → NoTREvFrom tr₁.length (s.next tr₁)) ∧
      (_root_.DY.Libsignal.Composed.Refinement.newRandoms tr₁ (s.next tr₁) ≠ [] →
        _root_.DY.Libsignal.Composed.Refinement.newRandoms tr₁ (s.next tr₁) =
          [(_root_.DY.Libsignal.Composed.Refinement.randTerm tr₁.length 32, 32)]) ∧
      m_mv.vis tr₁ = _root_.DY.Libsignal.Composed.Refinement.decVis tr₁ (s.next tr₁)
        stateIdx msgIdx wrapped ∧
      (∀ w, s.ok tr₁ = true → stepView s tr₁ w =
        _root_.DY.Libsignal.Composed.Refinement.decVis tr₁ (s.next tr₁) stateIdx msgIdx w) ∧
      _root_.DY.Libsignal.Composed.Refinement.PathFaithfulAt interp S g₁ tr₁ s ev.input := by
    have hpf_known : ∀ p₀, parsePreKeyWire ev.input = some p₀ →
        ∃ ek ∈ _root_.DY.Libsignal.Composed.Refinement.bobDoneBaseKeys tr₁,
          ecKey (gamma interp S g₁ ek) = p₀.baseKey.take 33 := by
      intro p₀ hp₀
      rw [hev_in, hq_wire] at hp₀
      injection hp₀ with hp₀_eq; subst hp₀_eq
      obtain ⟨ek, hek_mem, hek_ec⟩ := hkb
      have hreach₀ : (runTrace r ss).Reachable reachability :=
        Symbolic.Proofs.Swarm.UA.SlotInitTransfer.runSteps_reachable ss
          hex_pre.2.2.1.2.1 hex_pre.2.2.1.2.2.1
      have hek_st : Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g
          (runTrace r ss).length ek := by
        unfold _root_.DY.Libsignal.Composed.Refinement.bobDoneBaseKeys at hek_mem
        obtain ⟨idx, _, hidx⟩ := List.mem_filterMap.mp hek_mem
        split at hidx
        · rename_i b' a' ikB ikA spk pqpk opk ek' ct keys hget
          cases hidx
          exact Symbolic.Swarm.CREF.g2b_bobDoneEk_stampsLt_of_reachable interp S g
            (runTrace r ss).length hreach₀ (Nat.le_refl _) idx b' a' ikB ikA spk pqpk opk
            ek ct keys hget
        · cases hidx
      have hga := Symbolic.Swarm.CREF.cbadG2_gammaAgree_of_sigmaFrame interp S hfr
      have hgam_eq := Symbolic.Swarm.CREF.cbadG2_gamma_eq hga hek_st
      refine ⟨ek, ?_, ?_⟩
      · rw [htr₁_steps, bobDoneBaseKeys_runSteps_network]; exact hek_mem
      · rw [hgam_eq]; exact hek_ec.symm
    cases m_mv <;> simp [_root_.DY.Libsignal.Composed.Refinement.Move.decryptMsgIdx?] at hm_dec
    · rename_i me stateIdx msgIdx' pqIdx spqrMsgIdx wrapped
      subst msgIdx'
      have hcur_s := Symbolic.Swarm.CREF.TR.isCurrentSnapshot_of_decrypt_accept hreach_next hex_acc_vis
      refine ⟨me, stateIdx, wrapped, .messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx,
        rfl, rfl, rfl, rfl, by rw [hev_cmd]; trivial, trivial, trivial,
        (run_bind_pure_unit_snd _ tr₁).symm,
        fun p k b hl => by simp [Step.stateLoad?] at hl; exact ⟨hl.1.symm, hl.2.1.symm, hl.2.2⟩,
        hcur_s, trivial, hcur_s, ?_,
        newRandoms_messageDecrypt_singleton me stateIdx msgIdx pqIdx spqrMsgIdx tr₁,
        ?_, ?_, hpf_known⟩
      · intro hok_f
        have hiff := stepToLoadMove_ok
          (s := .messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) rfl tr₁
        rcases hrun : ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt
            me stateIdx msgIdx pqIdx spqrMsgIdx).run tr₁).1 with _ | _
        · exact quietOnNone_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx tr₁ hrun
        · have hok_t : (Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).ok tr₁ = true :=
            hiff.mp (by
              dsimp only [stepToLoadMove, _root_.DY.Libsignal.Composed.Refinement.Move.act,
                _root_.DY.Libsignal.Composed.Refinement.stepIn]
              rw [run_bind_pure_unit_isSome, hrun]; rfl)
          rw [hok_t] at hok_f; cases hok_f
      · rw [Symbolic.Swarm.CREF.xpl_vis_eq]
        dsimp only [Symbolic.Swarm.CREF.xpl_ownVis]
        have hn : (_root_.DY.Libsignal.Composed.Refinement.Move.decrypt
            me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr₁ =
            (Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).next tr₁ :=
          run_bind_pure_unit_snd _ tr₁
        rw [Symbolic.Swarm.CREF.exposures_nil_of_not_leakKind
            (m := _root_.DY.Libsignal.Composed.Refinement.Move.decrypt
              me stateIdx msgIdx pqIdx spqrMsgIdx wrapped) rfl (by intro h; cases h),
          List.append_nil, hn]
      · intro w hok_t
        unfold stepView
        have hexp : _root_.DY.Libsignal.Composed.Refinement.exposures tr₁
            ((Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).next tr₁) = [] := by
          have hn : (Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).next tr₁ =
              (_root_.DY.Libsignal.Composed.Refinement.Move.decrypt
                me stateIdx msgIdx pqIdx spqrMsgIdx false).next tr₁ :=
            (run_bind_pure_unit_snd _ tr₁).symm
          rw [hn]
          exact Symbolic.Swarm.CREF.exposures_nil_of_not_leakKind
            (m := _root_.DY.Libsignal.Composed.Refinement.Move.decrypt
              me stateIdx msgIdx pqIdx spqrMsgIdx false) rfl (by intro h; cases h)
        simp [hok_t, hexp]
    · rename_i me stateIdx msgIdx' skIdx pqIdx spqrMsgIdx wrapped
      subst msgIdx'
      have hcur_s :=
        Symbolic.Swarm.CREF.TR.isCurrentSnapshot_of_decryptSkipped_accept hreach_next hex_acc_vis
      refine ⟨me, stateIdx, wrapped,
        .messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx,
        rfl, rfl, rfl, rfl, by rw [hev_cmd]; trivial, trivial, trivial,
        (run_bind_pure_unit_snd _ tr₁).symm,
        fun p k b hl => by simp [Step.stateLoad?] at hl; exact ⟨hl.1.symm, hl.2.1.symm, hl.2.2⟩,
        hcur_s, trivial, hcur_s, ?_, ?_, ?_, ?_, hpf_known⟩
      · intro hok_f
        have hiff := stepToLoadMove_ok
          (s := .messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx) rfl tr₁
        rcases hrun : ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
            me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run tr₁).1 with _ | _
        · exact quietOnNone_messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx tr₁ hrun
        · have hok_t : (Step.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx
              spqrMsgIdx).ok tr₁ = true :=
            hiff.mp (by
              dsimp only [stepToLoadMove, _root_.DY.Libsignal.Composed.Refinement.Move.act,
                _root_.DY.Libsignal.Composed.Refinement.stepIn]
              rw [run_bind_pure_unit_isSome, hrun]; rfl)
          rw [hok_t] at hok_f; cases hok_f
      · intro hnr; exact absurd (newRandoms_messageDecryptSkipped_nil me stateIdx msgIdx skIdx pqIdx
          spqrMsgIdx tr₁) hnr
      · rw [Symbolic.Swarm.CREF.xpl_vis_eq]
        dsimp only [Symbolic.Swarm.CREF.xpl_ownVis]
        have hn : (_root_.DY.Libsignal.Composed.Refinement.Move.decryptSkipped
            me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next tr₁ =
            (Step.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).next tr₁ :=
          run_bind_pure_unit_snd _ tr₁
        rw [Symbolic.Swarm.CREF.exposures_nil_of_not_leakKind
            (m := _root_.DY.Libsignal.Composed.Refinement.Move.decryptSkipped
              me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped) rfl (by intro h; cases h),
          List.append_nil, hn]
      · intro w hok_t
        unfold stepView
        have hexp : _root_.DY.Libsignal.Composed.Refinement.exposures tr₁
            ((Step.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).next tr₁) = [] := by
          have hn : (Step.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).next tr₁ =
              (_root_.DY.Libsignal.Composed.Refinement.Move.decryptSkipped
                me stateIdx msgIdx skIdx pqIdx spqrMsgIdx false).next tr₁ :=
            (run_bind_pure_unit_snd _ tr₁).symm
          rw [hn]
          exact Symbolic.Swarm.CREF.exposures_nil_of_not_leakKind
            (m := _root_.DY.Libsignal.Composed.Refinement.Move.decryptSkipped
              me stateIdx msgIdx skIdx pqIdx spqrMsgIdx false) rfl (by intro h; cases h)
        simp [hok_t, hexp]
  obtain ⟨me, stateIdx, wrapped, s, hm_pty, hs_dec, hs_cls, hs_pty, hs_fit, hs_peer,
    hs_valid, hs_next, hs_load, hs_pre, hs_loc, hcur, hs_qnone, hs_nr, hvis_m, hsv, hpf_at⟩ :=
    hex_unified
  have hme_bob : me = r.bob := by
    let pfx := ms ++ ext.map _root_.DY.Libsignal.Composed.Refinement.Move.attackerSend
    have hget_m : (pfx ++ [m_mv])[pfx.length]? = some m_mv := by simp
    have htake_m : (pfx ++ [m_mv]).take pfx.length = pfx := List.take_left
    have hrf := hexpl₁.1.2.2.1 pfx.length m_mv me hget_m hm_pty
    rw [htake_m, hvis_ext, _root_.DY.Libsignal.Composed.Refinement.callCount_eq_callStarts_length
      hex_mv.1.2.2.2.2.2] at hrf
    exact Option.some.inj (hrf.symm.trans hwho)
  subst hme_bob
  have hrpt_some : ∃ ptTerm,
      _root_.DY.Libsignal.Composed.Refinement.receivedPlaintext tr₁ (s.next tr₁) = some ptTerm := by
    obtain ⟨v_a, hv_a, hk_a⟩ := hex_acc_vis
    rw [hvis_m] at hv_a
    unfold _root_.DY.Libsignal.Composed.Refinement.decVis at hv_a
    rw [hmsg_ua] at hv_a
    simp only [Option.map_some, Option.toList_some, List.singleton_append, List.mem_cons,
      List.mem_append, List.mem_map] at hv_a
    rcases hv_a with (rfl | ⟨_, _, rfl⟩) | hv_pt
    · cases hk_a
    · cases hk_a
    · rcases hrp : _root_.DY.Libsignal.Composed.Refinement.receivedPlaintext tr₁ (s.next tr₁)
          with _ | ptTerm
      · simp [hrp] at hv_pt
      · exact ⟨ptTerm, rfl⟩
  obtain ⟨ptTerm, hrpt⟩ := hrpt_some
  have hs_ok : s.ok tr₁ = true := by
    cases hok_b : s.ok tr₁
    · have hnone := receivedPlaintext_eq_none_of_xquietFrom (hs_qnone hok_b)
      rw [hrpt] at hnone; cases hnone
    · rfl
  let inp : VisEntry :=
    ⟨.recv, [t],
      if wrapped then .preKeyInner (_root_.DY.Libsignal.Composed.Refinement.sessionBaseKeys tr₁ stateIdx)
      else .whisper, none⟩
  let drs : List VisEntry :=
    (_root_.DY.Libsignal.Composed.Refinement.newRandoms tr₁ (s.next tr₁)).map
      fun r => _root_.DY.Libsignal.Composed.Refinement.rngEntry r.1
  let v_out : VisEntry := ⟨.accept, [ptTerm], .single, none⟩
  have hvis_decomp : m_mv.vis tr₁ = inp :: (drs ++ [v_out]) := by
    rw [hvis_m]
    unfold _root_.DY.Libsignal.Composed.Refinement.decVis
    simp [hmsg_ua, hrpt, inp, drs, v_out]
  rw [hvis_decomp] at hf₂_step
  cases hf₂_step with
  | cons hem_recv hf₂_tail =>
    have htag_ne : wpk ≠ wireWhisperTag :=
      Symbolic.Swarm.Coinsplit.Lift.L11.prom_tag_ne_wireWhisperTag_of_parsePreKeyWire hq_wire
    have hwrapped : wrapped = true := by
      cases hwr : wrapped
      · simp only [inp, hwr, Bool.false_eq_true, ↓reduceIte,
          _root_.DY.Libsignal.Composed.Refinement.EventMatchesEntry,
          _root_.DY.Libsignal.Composed.Refinement.eventBytes] at hem_recv
        obtain ⟨_, _, _, hcons_eq⟩ := hem_recv
        injection hcons_eq with htag_eq
        exact absurd htag_eq htag_ne
      · rfl
    have hrun_wr : runWrapped ev = wrapped := by
      rw [hwrapped]
      unfold runWrapped
      rw [hev_cmd, hev_in]
      simp [htag_ne]
    have hsv_eq : stepView s tr₁ (runWrapped ev) = inp :: (drs ++ [v_out]) := by
      rw [hrun_wr, hsv wrapped hs_ok, ← hvis_m, hvis_decomp]
    have hdrs_out :
        _root_.DY.Libsignal.Composed.Refinement.DrawsMatch interp r S g₁ drs ev.coins ∧
        _root_.DY.Libsignal.Composed.Refinement.OutputsMatch interp r S g₁ ev [v_out]
          (_root_.DY.Libsignal.Composed.Refinement.activeBundleIds evs_pre) ∧
        (∀ v ∈ stepView s tr₁ (runWrapped ev), v.kind = .rng →
          ∀ ts n, n ≠ 0 → _root_.DY.Libsignal.Composed.Refinement.randTerm ts n ∈ v.terms →
            (g₁.σ ts n).length = n) := by
      have hev_coins : ev.coins = c.coins := rfl
      have hev_exit : ev.exit = some (0, out) := rfl
      rcases hmid with rfl | rfl
      · simp only [List.nil_append] at hf₂_tail
        rcases hdrs : drs with _ | ⟨d₀, drs'⟩
        · rw [hdrs, List.nil_append] at hf₂_tail
          cases hf₂_tail with
          | cons hem_out hf₂_nil =>
            refine ⟨⟨[], by simp, List.nil_prefix, .nil⟩, ?_, ?_⟩
            · simp only [_root_.DY.Libsignal.Composed.Refinement.OutputsMatch, hev_exit, hev_cmd]
              exact ⟨v_out, rfl, ⟨hem_out.1, hem_out.2⟩⟩
            · intro v hv hk
              rw [hsv_eq, hdrs, List.nil_append] at hv
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with rfl | rfl <;> cases hk
        · exfalso
          rw [hdrs, List.cons_append] at hf₂_tail
          cases hf₂_tail with
          | cons hem_bad hf₂_rest =>
            cases drs' with
            | nil => cases hf₂_rest
            | cons _ _ => cases hf₂_rest
      · simp only [List.cons_append, List.nil_append] at hf₂_tail
        rcases hdrs : drs with _ | ⟨d₀, drs'⟩
        · rw [hdrs, List.nil_append] at hf₂_tail
          cases hf₂_tail with
          | cons _ hf₂_rest => cases hf₂_rest
        · rcases drs' with _ | ⟨d₁, drs''⟩
          · rw [hdrs, List.cons_append, List.nil_append] at hf₂_tail
            cases hf₂_tail with
            | cons hem_rng hf₂_out =>
              cases hf₂_out with
              | cons hem_out _ =>
                have hnr_ne : _root_.DY.Libsignal.Composed.Refinement.newRandoms tr₁
                    (s.next tr₁) ≠ [] := by
                  intro hnil; simp [drs, hnil] at hdrs
                have hnr_eq := hs_nr hnr_ne
                have hd₀_eq : d₀ = _root_.DY.Libsignal.Composed.Refinement.rngEntry
                    (_root_.DY.Libsignal.Composed.Refinement.randTerm tr₁.length 32) := by
                  simp [drs, hnr_eq] at hdrs; exact hdrs.symm
                have hc_ne : c.coins ≠ [] := by intro hc; rw [hc] at hcoins; simp at hcoins
                have hem_rng_b : _root_.DY.Libsignal.Composed.Refinement.BytesMatchEntry
                    interp r S g₁ .rng c.coins d₀ := by
                  rw [hd₀_eq] at hem_rng ⊢; exact ⟨hem_rng.1, hem_rng.2⟩
                refine ⟨⟨[c.coins], ?_, ?_, .cons hem_rng_b .nil⟩, ?_, ?_⟩
                · intro p hp; simp at hp; subst hp; exact hc_ne
                · rw [hev_coins]; simp
                · simp only [_root_.DY.Libsignal.Composed.Refinement.OutputsMatch, hev_exit, hev_cmd]
                  exact ⟨v_out, rfl, ⟨hem_out.1, hem_out.2⟩⟩
                · intro v hv hk ts n hn hmem_t
                  rw [hsv_eq, hdrs] at hv
                  simp only [List.cons_append, List.nil_append, List.mem_cons,
                    List.not_mem_nil, or_false] at hv
                  rcases hv with rfl | rfl | rfl
                  · cases hk
                  · rw [hd₀_eq] at hmem_t hem_rng
                    simp only [_root_.DY.Libsignal.Composed.Refinement.rngEntry,
                      List.mem_singleton] at hmem_t
                    obtain ⟨rfl, rfl⟩ := randTerm_inj_of_ne_zero (interp := interp) (S := S)
                      hn (by decide) hmem_t
                    simp only [_root_.DY.Libsignal.Composed.Refinement.EventMatchesEntry,
                      _root_.DY.Libsignal.Composed.Refinement.rngEntry,
                      _root_.DY.Libsignal.Composed.Refinement.eventBytes, List.map,
                      List.cons.injEq, and_true] at hem_rng
                    have hgam := Symbolic.Proofs.Swarm.UA.SlotInitTransfer.gamma_randTerm_eq
                      interp S g₁ tr₁.length 32 (by decide)
                    rw [hgam] at hem_rng
                    rw [hem_rng.2]
                    exact hcoins
                  · cases hk
          · exfalso
            rw [hdrs, List.cons_append, List.cons_append] at hf₂_tail
            cases hf₂_tail with
            | cons _ hf₂_1 =>
              cases hf₂_1 with
              | cons _ hf₂_2 =>
                have hlen := hf₂_2.length_eq
                simp at hlen
    obtain ⟨hdraws, houts, hgwf_step⟩ := hdrs_out
    have hrf_ua : _root_.DY.Libsignal.Composed.Refinement.ReadsFaithfully interp r S g₁ tr₁
        inp ev.input := by
      rw [hev_in]
      simp only [inp, hwrapped, ↓reduceIte, _root_.DY.Libsignal.Composed.Refinement.ReadsFaithfully]
      intro p₀ hp₀
      rw [hq_wire] at hp₀; injection hp₀ with hp₀_eq; subst hp₀_eq
      have ht_mv : t ∈ _root_.DY.Libsignal.Composed.Refinement.recvRepresentations interp r S g ms
          q.message := by
        rw [recvRepresentations_eq_of_trace htr_eq]; exact ht
      have ht_g₁ : t ∈ _root_.DY.Libsignal.Composed.Refinement.recvRepresentations interp r S g₁ ms
          q.message :=
        Symbolic.Swarm.CREF.CliPure.cbadG2_recvRep_of_sigmaFrame hfr_mv hex_mv.1 ht_mv
      rw [recvRepresentations_eq_of_trace htr_eq] at ht_g₁
      obtain ⟨hkn_t, hrest_t⟩ := ht_g₁
      exact ⟨htr₁_steps ▸ attackerKnows_runSteps_network ext hext_kn_ua hkn_t, hrest_t⟩
    have hrm_ua : RunMatches interp r S g₁ tr₁ s ev (stepView s tr₁ (runWrapped ev))
        (_root_.DY.Libsignal.Composed.Refinement.activeBundleIds evs_pre) := by
      refine ⟨hs_cls, ?_, hs_fit, hs_peer, hs_ok, ⟨out, rfl⟩, rfl,
        inp, drs, [v_out], hsv_eq, ?_, hdraws, houts, hrf_ua, hpf_at⟩
      · rw [hev_pty]; exact hs_pty
      · rw [hev_kind, hev_in]
        simp only [inp, hwrapped, ↓reduceIte,
          _root_.DY.Libsignal.Composed.Refinement.EventMatchesEntry,
          _root_.DY.Libsignal.Composed.Refinement.BytesMatchEntry,
          _root_.DY.Libsignal.Composed.Refinement.eventKind,
          _root_.DY.Libsignal.Composed.Refinement.eventBytes] at hem_recv ⊢
        obtain ⟨hk_eq, t', p', hterms, hpw', hex_ek, hmsg'⟩ := hem_recv
        change parsePreKeyWire (_root_.CryptoVerification.E2E.wirePrekey :: body) = some p' at hpw'
        injection (hpw'.symm.trans hq_wire) with hp_eq
        subst hp_eq
        exact ⟨hk_eq, t', p', hterms, hpw', hq_ver, hq_ik, hex_ek, hmsg'⟩
    have hreach₀ : (runTrace r ss).Reachable reachability :=
      Symbolic.Proofs.Swarm.UA.SlotInitTransfer.runSteps_reachable ss
        hex_pre.2.2.1.2.1 hex_pre.2.2.1.2.2.1
    have htr_lt₀ := Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable
      interp S g (runTrace r ss).length hreach₀ (Nat.le_refl _)
    have hvis_st : ∀ v ∈ vis,
        Symbolic.Swarm.CREF.TR.FreshSigma.VisStampsLt interp S g (runTrace r ss).length v :=
      Symbolic.Proofs.Swarm.UA.SlotInitTransfer.matchesEvents_visStampsLt
        hex_pre.2.2.2 hex_pre.2.2.1.2.1 hex_pre.2.2.1.2.2.1 (Nat.le_refl _) htr_lt₀
    have hgwf_pre₁ : _root_.DY.Libsignal.Composed.Refinement.GhostWF g₁ vis :=
      Symbolic.Proofs.Swarm.UA.SlotInitTransfer.ghostWF_transfer hfr hvis_st hex_pre.2.1
    have hgwf_all : _root_.DY.Libsignal.Composed.Refinement.GhostWF g₁
        (vis ++ stepView s tr₁ (runWrapped ev)) := by
      refine ⟨?_, hgwf_pre₁.2.1, ?_⟩
      · intro v hv hk ts n hn hmem
        rcases List.mem_append.mp hv with hv₁ | hv₂
        · exact hgwf_pre₁.1 v hv₁ hk ts n hn hmem
        · exact hgwf_step v hv₂ hk ts n hn hmem
      · intro v hv hk
        rcases List.mem_append.mp hv with hv₁ | hv₂
        · exact hgwf_pre₁.2.2 v hv₁ hk
        · rw [hsv_eq] at hv₂
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv₂
          rcases hv₂ with rfl | (hv_drs | rfl)
          · cases hk
          · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv_drs
            cases hk
          · cases hk
    have hswf_all : _root_.DY.Libsignal.Composed.Refinement.StepsWF
        (ss ++ ext.map Step.network ++ [s]) (setupTrace r) := by
      rw [Symbolic.Proofs.Swarm.UA.SlotInitTransfer.stepsWF_append_iff,
        Symbolic.Proofs.Swarm.UA.SlotInitTransfer.stepsWF_append_iff]
      refine ⟨⟨hex_pre.2.2.1.2.2.1, stepsWF_network_map ext hext_kn_ua⟩, ?_⟩
      change _root_.DY.Libsignal.Composed.Refinement.StepsWF [s] tr₁
      exact ⟨hs_pre, hs_loc, trivial⟩
    have hssf_ext : _root_.DY.Libsignal.Composed.Refinement.StepsStateFaithful r
        (ss ++ ext.map Step.network) :=
      Symbolic.Proofs.Swarm.UA.SlotInitTransfer.stepsStateFaithful_append_noLoad
        hex_pre.2.2.1.2.2.2 (by intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; rfl)
    have hv_ss_ext : ∀ x ∈ ss ++ ext.map Step.network, ValidLoadStep x := by
      intro x hx
      rcases List.mem_append.mp hx with hx₁ | hx₂
      · exact validLoadStep_of_matchesEvents hex_pre.2.2.2 x hx₁
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx₂; trivial
    have hssf_all : _root_.DY.Libsignal.Composed.Refinement.StepsStateFaithful r
        (ss ++ ext.map Step.network ++ [s]) :=
      stepsStateFaithful_snoc_of_isCurrentSnapshot hv_ss_ext hs_valid hssf_ext
        (fun p k b hld => (hs_load p k b hld).2.1 ▸ hcur)
    have hme_pre₁ : MatchesEventsClassical interp r S g₁ (setupTrace r) ss evs_pre vis :=
      Symbolic.Proofs.Swarm.UA.SlotInitTransfer.matchesEvents_transfer hfr
        hex_pre.2.2.2 hex_pre.2.2.1.2.1 hex_pre.2.2.1.2.2.1 (Nat.le_refl _)
    have hme_all : MatchesEventsClassical interp r S g₁ (setupTrace r)
        (ss ++ ext.map Step.network ++ [s]) (evs_pre ++ [.run ev])
        (vis ++ stepView s tr₁ (runWrapped ev)) :=
      Symbolic.Proofs.Swarm.UA.SlotInitTransfer.matchesEvents_snoc_run1 hme_pre₁
        (by intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; rfl)
        (htr₁_steps ▸ hrm_ua)
    exact ⟨ext, s, msgIdx, g₁, vis ++ stepView s tr₁ (runWrapped ev),
      hext_kn_ua, hs_dec, hg_addr, htr_eq ▸ hg_sig, hmsg_ua,
      hexpl₁.1.1, hgwf_all, ⟨hex_pre.2.2.1.1, hex_pre.2.2.1.2.1, hswf_all, hssf_all⟩, hme_all⟩

private theorem prom_make_acceptCall_local
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc_hw mid : List MachineEvent} {rec_ b rec' pt : HwBytes}
    {pf : PreKeyFields} {sess sess' : _root_.CryptoGames.LibsignalSessionApi.Session HwBytes}
    {coins : BitVec 256} {expected : Option HwBytes}
    (hwf : ProtocolSetupWF r)
    (hwho : who[(_root_.DY.Libsignal.Composed.Refinement.callStarts acc_hw).length]? = some r.bob)
    (hrec : records r.bob = some rec_)
    (hlen : rec_.length < 2 ^ 32 - 2 ^ 20)
    (hpm : EligibleForSessionPromotion rec_ b)
    (hhon : _root_.DY.Libsignal.Composed.Refinement.HonestIdentity interp r b)
    (hpqh : ∀ q₀, parsePreKeyWire b = some q₀ → PqFromHonest sent q₀.message)
    (hclean : ∃ g ms, _root_.DY.Libsignal.Composed.Refinement.Clean interp r S who ok g ms acc_hw)
    (hrel : Symbolic.Swarm.CREF.PureCRel interp r S who ok records sent accepted acc_hw)
    (hopk : Symbolic.Swarm.CREF.COpkRelC interp r S who ok opkUsed acc_hw)
    (hout : Symbolic.Swarm.CREF.Cli.PromPureAcceptOut interp r rec_ b rec' mid pt pf sess sess'
      coins expected) :
    Symbolic.Swarm.CREF.CliPure.PromAcceptCall interp r S who ok
      (_root_.DY.Libsignal.Composed.Refinement.callStarts acc_hw).length
      ⟨records, sent, accepted, opkUsed⟩ mid acc_hw rec_ b
      { state := rec', message := List.replicate 47 0#8 ++ pt }
      pf sess sess' coins expected pt :=
  { entry := Symbolic.Swarm.CREF.CliPure.prom_entry_hyps_pure hwf ⟨hclean, hrel, hopk⟩ hwho
      hrec hlen hpm hhon hpqh
    hj := rfl
    out :=
      { hpf := hout.hpf
        hcan_in := hout.hcan_in
        hcoins := hout.hcoins
        hdecOk := hout.hdecOk
        hexec := hout.hexec
        halice := hout.halice
        hpend := hout.hpend
        hkyb := hout.hkyb
        hstate := hout.hstate
        hmsg := rfl
        hwrc := hout.hwrc
        hcanon_out := hout.hcanon_out }
    ver := hout.hver
    nodraw := hout.hnodraw }

private theorem rpkPromMid_cases_local (interp : ExternInterpretation)
    (x : _root_.CryptoVerification.E2E.RecordExtras)
    (g : _root_.CryptoGames.LibsignalSession.GhostState HwBytes)
    (inner : _root_.CryptoGames.LibsignalSession.SignalMessage) (c_coins : HwBytes) :
    Symbolic.Swarm.CREF.Cli.rpkPromMid interp x g inner c_coins = [] ∨
      Symbolic.Swarm.CREF.Cli.rpkPromMid interp x g inner c_coins = [.rng c_coins] := by
  unfold Symbolic.Swarm.CREF.Cli.rpkPromMid
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

section PromAcceptExtract
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
  (pqFieldsMatch_of_promoteMatch_v4 preKeyOfBody?_some_inv pqRecvMatchingFieldsModel_accept_eval
    toCliCallNone inputsFor_toCliCallNone)
open Symbolic.Swarm.CREF.Cli
  (PqDirInv PqPartyInv BobPromDirInv bobPromDirInv_of_pqPartyInv wfPq_of_pqPartyInv
    records_of_pqPartyInv keyToBytes32_bytesToKey32 modelAgree_interpOfParams
    externContractsHoldCli_interpOfParams modelHookBridge_interpOfParams
    exited_eq_pqObserve_iff inputsEquiv_pqRecvInputs peerOf_eq_addrE_other)
open Symbolic.Swarm.CREF.CliPure
  (leakRecords_eq_records_of_bobOff_false coinSplit_callStarts_length_eq)

private theorem prom_accept_contract_local
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hwf : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs} {rec_ : HwBytes} {q : PreKeyFields}
    {out : HwBytes} {files : DirectorySnapshot} {accepted : List HwBytes}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r r.bob))
    (hbun : c.bundle = [])
    (hcoins : c.coins.length = 32)
    (hsb : StdinBounded c)
    (hfb : FilesBounded (t.dirs c.party))
    (hbca : BobCallAllowed r t c)
    (hrec_bob : t.records r r.bob = some rec_)
    (hq_wire : parsePreKeyWire c.stdin = some q)
    (hpm : EligibleForSessionPromotion rec_ c.stdin)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited 0 out files))) :
    let interp' := interpOfParams interp P
    ExternContractsHoldCli interp' ∧
    t_clean = t ∧
    t.leakRecords r r.bob = some rec_ ∧
    rec_.length < 2 ^ 32 - 2 ^ 20 ∧
    q.version = 4 ∧
    ∃ (body : HwBytes) (stB st' : _root_.CryptoVerification.SignalSession.PqParty)
      (x : _root_.CryptoVerification.E2E.RecordExtras)
      (g_st : _root_.CryptoGames.LibsignalSession.GhostState HwBytes),
      c.stdin = _root_.CryptoVerification.E2E.wirePrekey :: body ∧
      _root_.DY.Libsignal.PQXDH.Refinement.parsePreKey body = some q ∧
      Symbolic.Swarm.CREF.Cli.ModelHookBridge interp' P ∧
      BobPromDirInv interp' P r stB rec_ ∧
      stB.session = some (x, g_st) ∧
      rec_ = _root_.CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) g_st ∧
      _root_.DY.Libsignal.Composed.Refinement.Cli.pqRecvMatchingFieldsModel P stB x g_st q
        (_root_.CryptoGames.HKDF.bytesToKey32 c.coins) = some (some (st', out)) := by
  let interp' := interpOfParams interp P
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  have hagree' : ModelAgree interp' P := (modelAgree_interpOfParams interp P).mpr hagree
  have hmb : Symbolic.Swarm.CREF.Cli.ModelHookBridge interp' P := modelHookBridge_interpOfParams hagree
  have hoff : t.bobOff = false := by
    cases hbo : t.bobOff
    · rfl
    · exact absurd hbob (hbca hbo)
  have htc_eq : t_clean = t := hsim.bobOff_false_eq hoff
  subst t_clean
  have hDir : PqDirInv interp' P r t accepted := hsim.dirInv
  have hfb_bob : FilesBounded (t.dirs r.bob) := hbob ▸ hfb
  obtain ⟨stB, hBobInv⟩ := hDir.2.1
  have hinvB : PqPartyInv interp' P r accepted r.bob stB (t.dirs r.bob) := by
    unfold Symbolic.Swarm.CREF.Cli.PqBobInv at hBobInv; rwa [hoff] at hBobInv
  have hwfB := wfPq_of_pqPartyInv hinvB hfb_bob
  let c1 := toCliCallNone c
  have hin1 : InputsFor c1 (t.dirs c1.party) i := inputsFor_toCliCallNone hbun hin
  have hi_enc : InputsFor c1 (_root_.CryptoVerification.SignalSession.filesOf
      (_root_.CryptoVerification.SignalSession.encodeDir P stB)) i := by
    rwa [show c1.party = r.bob from hbob, hinvB.dir_eq] at hin1
  let rc := _root_.CryptoGames.HKDF.bytesToKey32 c.coins
  have hcoins_rc : c1.coins = _root_.CryptoGames.HMAC.keyToBytes32 rc :=
    (keyToBytes32_bytesToKey32 hcoins).symm
  have hcmd_stB : c1.cmd = .recv (_root_.CryptoVerification.SignalSession.partyAddress stB.party.other) := by
    change c.cmd = .recv (_root_.CryptoVerification.SignalSession.partyAddress stB.party.other)
    rw [hcmd, peerOf_eq_addrE_other, ← hinvB.party_eq]
  have heq_recv := inputsEquiv_pqRecvInputs (c := c1) hi_enc hcmd_stB rfl hcoins_rc
  have hp := _root_.DY.Libsignal.Composed.Refinement.Cli.PqModelRel.exited_iff.mp hRel
  have hrec_map := hrec_bob
  rw [records_of_pqPartyInv hinvB] at hrec_map
  rcases hsess : stB.session with _ | ⟨x, g_st⟩
  · rw [hsess] at hrec_map; cases hrec_map
  have hrec_eq : rec_ = _root_.CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) g_st := by
    rw [hsess] at hrec_map
    exact (Option.some.inj hrec_map).symm
  have hstdin_ex : ∃ body, c.stdin = _root_.CryptoVerification.E2E.wirePrekey :: body ∧
      _root_.DY.Libsignal.PQXDH.Refinement.parsePreKey body = some q := by
    rcases hcs : c.stdin with _ | ⟨tag, body⟩
    · rw [hcs] at hq_wire; cases hq_wire
    · rw [hcs] at hq_wire
      unfold parsePreKeyWire at hq_wire
      dsimp only at hq_wire
      split_ifs at hq_wire with htag
      exact ⟨body, by rw [htag]; rfl, hq_wire⟩
  obtain ⟨body, hstdin, hq⟩ := hstdin_ex
  have hnw_tag : c.stdin.head? ≠ some wireWhisperTag := by
    rw [hstdin, List.head?_cons, ne_eq, Option.some.injEq]
    unfold _root_.CryptoVerification.E2E.wirePrekey wireWhisperTag
    decide
  unfold StdinBounded at hsb
  rw [hcmd] at hsb
  have hlen_lt : c.stdin.length < 2 ^ 32 := hsb.2.1 hnw_tag
  have hbody_lt : body.length < 2 ^ 32 := by rw [hstdin, List.length_cons] at hlen_lt; omega
  have hpm_b : EligibleForSessionPromotion rec_ (_root_.CryptoVerification.E2E.wirePrekey :: body) :=
    hstdin ▸ hpm
  by_cases hfm : _root_.DY.Libsignal.Composed.Refinement.Cli.PqFieldsMatch x g_st q
  · have hobs := hp.recvPrekeyMatching stB x g_st body q rc hwfB hsess hbody_lt hq hfm
      (hstdin ▸ heq_recv)
    rcases exited_eq_pqObserve_iff.mp hobs with
        ⟨_, h01, _, _⟩ | ⟨st', out', hok_mod, _, rfl, _⟩
    · cases h01
    · have hlen_rec : rec_.length < 2 ^ 31 := hrec_eq ▸ (hwfB.1 x g_st hsess).2.2
      have hlen_rec_bound : rec_.length < 2 ^ 32 - 2 ^ 20 := Nat.lt_trans hlen_rec (by decide)
      have hleak_bob : t.leakRecords r r.bob = some rec_ := by
        rw [leakRecords_eq_records_of_bobOff_false r hoff, hrec_bob]
      have hbinv : BobPromDirInv interp' P r stB rec_ :=
        bobPromDirInv_of_pqPartyInv hwf hagree' hinvB hfb_bob hrec_bob
      have hsver : g_st.session.sessionVersion = 4#32 :=
        Symbolic.Swarm.CREF.Cli.pqSession_sessionVersion_of_wfPq hwfB hsess
      have hq_ver : q.version = 4 := by
        have hv := hfm.2; rw [hsver] at hv; exact hv.symm
      exact ⟨hext', rfl, hleak_bob, hlen_rec_bound, hq_ver, body, stB, st', x, g_st,
        hstdin, hq, hmb, hbinv, hsess, hrec_eq, hok_mod⟩
  · have hno_fm : ∀ x₀ g₀, stB.session = some (x₀, g₀) →
        ¬ _root_.DY.Libsignal.Composed.Refinement.Cli.PqFieldsMatch x₀ g₀ q := by
      intro x₀ g₀ hs₀
      rw [hsess] at hs₀
      rcases Prod.mk.inj (Option.some.inj hs₀) with ⟨rfl, rfl⟩
      exact hfm
    cases hm : _root_.DY.Libsignal.Composed.Refinement.Cli.preKeyOfBody? body with
    | none =>
      have hobs := hp.recvPrekeyUntyped stB body q rc hwfB hbody_lt hq hm hno_fm
        (hstdin ▸ heq_recv)
      injection hobs with h01 _ _
      cases h01
    | some m =>
      obtain ⟨q₁, hq₁, hv4, _⟩ := preKeyOfBody?_some_inv hm
      cases Option.some.inj (hq.symm.trans hq₁)
      exact absurd (pqFieldsMatch_of_promoteMatch_v4 hwfB hsess hq hv4 (hrec_eq ▸ hpm_b)) hfm

set_option maxHeartbeats 400000 in
/-- Bob's matching-session promote `recv` slot preserves `PqTurnSim1A` and `UAInv`, parameterized
over `XlateInvSpec` and `XlateExcWSpec`. -/
theorem slot_rpk_prom_ua_of_xlate (hInv : XlateInvSpec) (hExcW : XlateExcWSpec) :
    UASlotRpkPromSpec := by
  intro interp P r hext hagree hwf t t_clean c i rec_ q code out files accepted evs_pre
    hsim hbob hcmd hbun hcoins hsb hfb hbca hrec_bob hq_wire hpm hpqh hin hRel
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  have hSem : SemReady interp' r S := compSemOf_ready interp' r hwf
  obtain ⟨t_clean', accepted', hsim', hstep_cli⟩ :=
    Symbolic.Swarm.Coinsplit.Lift.L11.slot_rpk_prom_cli_gen
      Symbolic.Swarm.Coinsplit.Lift.L02.outcomeFaithfulCli_of_goodExit0Cut
      Symbolic.Swarm.Coinsplit.Lift.L04.bridgeB_quiet_fail
      Symbolic.Swarm.Coinsplit.Lift.L05.bridgeC_caseA
      Symbolic.Swarm.Coinsplit.Lift.L06.bridgeC_caseB
      interp P r hext hagree hwf hsim hbob hcmd hbun hcoins hsb hfb hbca hrec_bob hq_wire hpm hpqh
      hin hRel (σ_pre := flatEvents evs_pre)
  refine ⟨t_clean', accepted', hsim', fun who ok hsched hua => ?_⟩
  let ev := runEventOf c (some (code, out))
  obtain ⟨hsched_pre, hwho_k, hok_k, hflat_eq⟩ :=
    Symbolic.Proofs.Swarm.UA.SlotRpkNOHelpers.schedFits_recv_call hcmd hsched
  rcases hua with hcol_pre | ⟨hlive_pre, hpend_pre, ⟨g₀, ss₀, vis₀, hex₀, hnrc₀⟩⟩
  · exact Or.inl (collisionAtCli_append [.run ev] hcol_pre)
  · by_cases hcol : CollisionAfterExplainedPrefixClassical interp' r S (evs_pre ++ [.run ev])
    · exact Or.inl hcol
    · have hpend_post := aliceRecordPendingInSession_bob_recv hwf hbob hcmd hsim hsim' hpend_pre
      by_cases hcode0 : code = 0
      · subst hcode0
        obtain ⟨hext', htc_eq, hleak_bob, hlen_rec_bound, hq_ver, body, stB, st', x, g_st,
            hstdin, hq, hmb, hbinv, hsess, hrec_eq, hok_mod⟩ :=
          prom_accept_contract_local hext hagree hwf hsim hbob hcmd hbun hcoins hsb hfb hbca
            hrec_bob hq_wire hpm hin hRel
        subst t_clean
        have hpm_b : EligibleForSessionPromotion rec_ (_root_.CryptoVerification.E2E.wirePrekey :: body) :=
          hstdin ▸ hpm
        have hpqh_b : ∀ q₀,
            parsePreKeyWire (_root_.CryptoVerification.E2E.wirePrekey :: body) = some q₀ →
            PqFromHonest t.sent q₀.message := hstdin ▸ hpqh
        have hev_cmd : ev.cmd = .recv (peerOf r r.bob) := by
          dsimp only [ev]; simp [runEventOf, hcmd]
        have hev_in : ev.input = _root_.CryptoVerification.E2E.wirePrekey :: body := by
          dsimp only [ev]
          simp [runEventOf, _root_.DY.Libsignal.Composed.Refinement.Cli.runInput, hcmd, hstdin]
        have hev_coins : ev.coins = c.coins := rfl
        obtain ⟨τ₀, ms₀, hex₀_cli, hnrc₀_cli, htr₀, _, _, _⟩ :=
          hInv hwf hSem hsched_pre hex₀ hnrc₀
        have hc₀ := Symbolic.Swarm.Coinsplit.Lift.explainsCli_toClean hex₀_cli hnrc₀_cli
        obtain ⟨hrel₀, hopk₀⟩ := hlive_pre.cutRel τ₀ ⟨g₀, ms₀, hex₀_cli, hnrc₀_cli⟩
        have hwho₀ : who[(_root_.DY.Libsignal.Composed.Refinement.callStarts τ₀).length]? =
            some r.bob := by
          rw [coinSplit_callStarts_length_eq hex₀_cli.1, ← hbob]
          exact hwho_k
        obtain ⟨s', _, coins_out, sess, sess', _, _, _, _, hhon_wire, hout⟩ :=
          pqRecvMatchingFieldsModel_accept_eval hmb hbinv hsess hrec_eq hleak_bob
            hrel₀.oooAll hrel₀.bkn hcoins hq hok_mod
        have hq_ik : q.identityKey.take 33 = ecKey (pubBytes interp' (secretBytes r 0)) :=
          hhon_wire q hout.hpf
        let mid := Symbolic.Swarm.CREF.Cli.rpkPromMid interp' x g_st q.inner c.coins
        have hC₀ := prom_make_acceptCall_local hwf hwho₀ hleak_bob hlen_rec_bound hpm_b hhon_wire
          hpqh_b ⟨g₀, ms₀, hc₀⟩ hrel₀ hopk₀ hout
        have hkb₀_mv := Symbolic.Swarm.CREF.CliPure.promXpl_knownBaseKey_of_acceptCallBy₂ hC₀ hc₀
        have hkb₀ : KnownBaseKeyOn interp' S g₀ (runTrace r ss₀) q :=
          (knownBaseKey_iff_of_trace htr₀).mp hkb₀_mv
        obtain ⟨t₀, ht₀_mv⟩ :=
          Symbolic.Swarm.CREF.prom_recvRepresentations_nonempty_of_parsePreKeyWire
            interp' r S g₀ ms₀ hout.hpf
        have ht₀ : t₀ ∈ recvRepresentationsOn interp' S g₀ (runTrace r ss₀) q.message := by
          rwa [← recvRepresentations_eq_of_trace htr₀]
        refine Or.inr ⟨?_, hpend_post, ?_⟩
        ·
          rw [hflat_eq]
          refine hstep_cli who ok hwho_k hlive_pre (fun _ τ₁ g ms hex₁ hnrc₁ => ?_) hok_k
          have hnw := hExcW hwf hSem hsched hlive_pre hex₀ hnrc₀ hev_cmd rfl
            (hev_coins ▸ hcoins) ⟨t₀, ht₀⟩
            (Or.inr ⟨q, hev_in ▸ hout.hpf, rfl, hq_ver, hq_ik, hkb₀⟩) hcol τ₁ g ms hex₁ hnrc₁
          rwa [hev_in, hev_coins, ← hstdin] at hnw
        ·
          have hnexc : ¬ SignalMsgAcceptedOnlyViaCollisionClassical interp' r S g₀ ss₀ evs_pre ev q.message := by
            intro hexc
            apply hcol
            refine ⟨evs_pre, ev, [], g₀, ss₀, vis₀, rfl, hex₀, ?_⟩
            dsimp only [NextEventCollidesClassical]
            rw [hev_cmd, hev_in]
            exact ⟨⟨out, rfl⟩, Or.inr ⟨q, hout.hpf, Or.inl ⟨hkb₀, hq_ver, hq_ik, hexc⟩⟩⟩
          have hex_clean_w : ∃ g' ss' vis',
              ExplainsClassical interp' r S g' ss' vis' evs_pre ∧
              ¬ ReadCollisionCliClassical interp' r S g' ss' evs_pre ∧
              (∃ t' ∈ recvRepresentationsOn interp' S g' (runTrace r ss') q.message,
                ¬ RecvCollisionOn interp' r S g' (runTrace r ss') vis' (honestSaltsOf r ss') t' ∧
                ¬ ReselectCollisionOn interp' r S g' (runTrace r ss') vis'
                    (honestSaltsOf r ss') t') ∧
              ¬ ((∃ t ∈ recvRepresentationsOn interp' S g' (runTrace r ss') q.message,
                    ModelAcceptsTermAfterAttackerSendsClassical interp' r S g' ss' evs_pre ev t) ∧
                  ∀ t ∈ recvRepresentationsOn interp' S g' (runTrace r ss') q.message,
                    ModelAcceptsTermAfterAttackerSendsClassical interp' r S g' ss' evs_pre ev t →
                    RecvCollisionOn interp' r S g' (runTrace r ss') vis'
                      (honestSaltsOf r ss') t) := by
            by_contra hno_w
            apply hnexc
            refine ⟨⟨t₀, ht₀⟩, fun g' ss' vis' hex' hnrc' => ?_⟩
            by_contra hneither
            have hnot1 : ¬ (∀ t ∈ recvRepresentationsOn interp' S g' (runTrace r ss') q.message,
                RecvCollisionOn interp' r S g' (runTrace r ss') vis' (honestSaltsOf r ss') t ∨
                ReselectCollisionOn interp' r S g' (runTrace r ss') vis'
                  (honestSaltsOf r ss') t) := fun h1 => hneither (Or.inl h1)
            have hnot2 := fun h2 => hneither (Or.inr h2)
            have hex_t' : ∃ t' ∈ recvRepresentationsOn interp' S g' (runTrace r ss') q.message,
                ¬ RecvCollisionOn interp' r S g' (runTrace r ss') vis' (honestSaltsOf r ss') t' ∧
                ¬ ReselectCollisionOn interp' r S g' (runTrace r ss') vis'
                    (honestSaltsOf r ss') t' := by
              by_contra hno_t'
              apply hnot1
              intro t' ht'
              by_cases hrc_t' : RecvCollisionOn interp' r S g' (runTrace r ss') vis'
                  (honestSaltsOf r ss') t'
              · exact Or.inl hrc_t'
              · refine Or.inr ?_
                by_contra hnrs_t'
                exact hno_t' ⟨t', ht', hrc_t', hnrs_t'⟩
            exact hno_w ⟨g', ss', vis', hex', hnrc', hex_t', hnot2⟩
          obtain ⟨g', ss', vis', hex', hnrc', ⟨t', ht'_on, hnrc_t', hnrs_t'⟩, hnot_ac_cli⟩ :=
            hex_clean_w
          obtain ⟨τ', ms', hex'_cli, hnrc'_cli, htr', hsalts', hpref', hpt'⟩ :=
            hInv hwf hSem hsched_pre hex' hnrc'
          have hc' := Symbolic.Swarm.Coinsplit.Lift.explainsCli_toClean hex'_cli hnrc'_cli
          obtain ⟨hrel', hopk'⟩ := hlive_pre.cutRel τ' ⟨g', ms', hex'_cli, hnrc'_cli⟩
          have hwho' : who[(_root_.DY.Libsignal.Composed.Refinement.callStarts τ').length]? =
              some r.bob := by
            rw [coinSplit_callStarts_length_eq hex'_cli.1, ← hbob]
            exact hwho_k
          have hok' : ok (_root_.DY.Libsignal.Composed.Refinement.callStarts τ').length = true := by
            rw [coinSplit_callStarts_length_eq hex'_cli.1]
            simpa using hok_k
          have hC' := prom_make_acceptCall_local hwf hwho' hleak_bob hlen_rec_bound hpm_b hhon_wire
            hpqh_b ⟨g', ms', hc'⟩ hrel' hopk' hout
          have hkb' : KnownBaseKeyOn interp' S g' (runTrace r ss') q :=
            (knownBaseKey_iff_of_trace htr').mp
              (Symbolic.Swarm.CREF.CliPure.promXpl_knownBaseKey_of_acceptCallBy₂ hC' hc')
          have hmid_cases := rpkPromMid_cases_local interp' x g_st q.inner c.coins
          have hmid_ex : mid = [] ∨ ∃ d : HwBytes, mid = [.rng d] := by
            rcases hmid_cases with h0 | h1
            · exact Or.inl h0
            · exact Or.inr ⟨c.coins, h1⟩
          have hex_acc_mv : ∃ t_m ∈ _root_.DY.Libsignal.Composed.Refinement.recvRepresentations
              interp' r S g' ms' q.message,
              _root_.DY.Libsignal.Composed.Refinement.ModelAcceptsTermAfterCoinSplit interp' r S who ok g' ms' τ'
                (.recv (_root_.CryptoVerification.E2E.wirePrekey :: body))
                (mid ++ [.accept out]) t_m := by
            by_contra hno_acc
            have hnac_mv : ¬ Symbolic.Swarm.CREF.AcceptCollision interp' r S who ok g' ms' τ'
                (.recv (_root_.CryptoVerification.E2E.wirePrekey :: body))
                (mid ++ [.accept out]) q.message := fun ⟨hex_a, _⟩ => hno_acc hex_a
            have ht'_mv : t' ∈ _root_.DY.Libsignal.Composed.Refinement.recvRepresentations
                interp' r S g' ms' q.message := by
              rwa [recvRepresentations_eq_of_trace htr']
            have hnrc_mv : ¬ _root_.DY.Libsignal.Composed.Refinement.RecvCollision interp' r S
                g' ms' t' :=
              fun h => hnrc_t' ((recvCollision_iff_of_terms htr' hsalts' hpref'
                hpt').mp h)
            have hnrs_mv : ¬ _root_.DY.Libsignal.Composed.Refinement.ReselectCollision interp' r S
                g' ms' t' :=
              fun h => hnrs_t' ((reselectCollision_iff_of_terms htr' hsalts' hpref'
                hpt').mp h)
            have href' : Symbolic.Swarm.CREF.RecvExcuseFree interp' r S who ok g' ms' τ'
                (.recv (_root_.CryptoVerification.E2E.wirePrekey :: body))
                (mid ++ [.accept out]) q.message t' := ⟨hnrs_mv, hnac_mv⟩
            obtain ⟨g₁_w, _stIdx, _spqrIdx, pqSalt, t_m, m_step,
                hfr_w, ht_m, hpq_kn, _hcur_w, hm_step, hraw⟩ :=
              Symbolic.Swarm.Coinsplit.Lift.L11.prom_rawKnWitness_at_clean hext' hwf rfl hC' hc'
                ht'_mv hnrc_mv href'
            have hc₁' := Symbolic.Swarm.CREF.CliPure.cbadG2_cleanBy_transfer hfr_w hc'
            have htag_ne :=
              Symbolic.Swarm.Coinsplit.Lift.L11.prom_tag_ne_wireWhisperTag_of_parsePreKeyWire
                hout.hpf
            have hacc_tm := Symbolic.Swarm.CREF.CliPure.acceptsVia_of_rawWitness hc' hfr_w ht_m
              hpq_kn hwho' hok' hm_step hmid_ex
              (Or.inr ⟨htag_ne, q, hout.hpf, rfl,
                Symbolic.Swarm.CREF.CliPure.promXpl_hbka_of_acceptCallBy₂ hC' hc₁'⟩) hraw
            exact hno_acc ⟨t_m, ht_m, hacc_tm⟩
          obtain ⟨t_m, ht_m_mv, hacc_tm⟩ := hex_acc_mv
          have ht_m_on : t_m ∈ recvRepresentationsOn interp' S g' (runTrace r ss') q.message := by
            rwa [← recvRepresentations_eq_of_trace htr']
          have hacc_cli_tm : ModelAcceptsTermAfterAttackerSendsClassical interp' r S g' ss' evs_pre ev t_m :=
            acceptsViaCli_of_acceptsVia_prom hex' hc'.1 htr' hwho' hbob hcmd hstdin hcoins
              hout.hpf hq_ver hq_ik hkb' hmid_cases ht_m_on hacc_tm
          have hex_good : ∃ t_good ∈ recvRepresentationsOn interp' S g' (runTrace r ss') q.message,
              ModelAcceptsTermAfterAttackerSendsClassical interp' r S g' ss' evs_pre ev t_good ∧
              ¬ RecvCollisionOn interp' r S g' (runTrace r ss') vis'
                  (honestSaltsOf r ss') t_good := by
            by_contra hno_good
            exact hnot_ac_cli ⟨⟨t_m, ht_m_on, hacc_cli_tm⟩, fun t_a ht_a hacc_a => by
              by_contra hnc_a
              exact hno_good ⟨t_a, ht_a, hacc_a, hnc_a⟩⟩
          obtain ⟨t_good, _, ⟨ext_g, m_g, msgIdx_g, g₁_g, vis₁_g,
              hext_g, hm_g, haddr_g, hσ_g, hget_g, hex₁_g⟩, hnc_good⟩ := hex_good
          have hnrc₁_g := not_readCollisionCli_of_acceptsViaCli (ev := ev) hInv hwf hSem hsched_pre
            hex' hnrc' hext_g hm_g haddr_g hσ_g hget_g hnc_good
          exact ⟨g₁_g, ss' ++ ext_g.map Step.network ++ [m_g], vis₁_g, hex₁_g, hnrc₁_g⟩
      ·
        refine Or.inr ⟨?_, hpend_post, ?_⟩
        · rw [hflat_eq]
          exact hstep_cli who ok hwho_k hlive_pre (fun hc => absurd hc hcode0) hok_k
        · have hrej : RunRejected ev := by
            intro out' hexit
            change some (code, out) = some (0, out') at hexit
            injection hexit with h1
            injection h1 with hc0 _
            exact hcode0 hc0
          exact ⟨g₀, ss₀, vis₀, explains_snoc_rejected hrej hex₀,
            not_readCollisionCli_snoc_rejected hrej hnrc₀⟩

end PromAcceptExtract

/-- Bob's matching-session promote `recv` slot preserves `PqTurnSim1A` and `UAInv`, parameterized
over `XlateExcWSpec`. -/
theorem slot_rpk_prom_ua_of_exc_w (hExcW : XlateExcWSpec) : UASlotRpkPromSpec :=
  slot_rpk_prom_ua_of_xlate xlate_inv hExcW

end Symbolic.Proofs.Swarm.UA.SlotRpkProm
