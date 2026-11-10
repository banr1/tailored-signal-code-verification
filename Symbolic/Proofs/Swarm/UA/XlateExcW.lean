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
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.UA.Defs
import Symbolic.Proofs.Swarm.COMPOSED.CompLineage
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPureA
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.StateFaithfulMoves
import Symbolic.Proofs.Swarm.CREF.TR.MessageKeyCurrentInv
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.SlotInitTransfer
import Symbolic.Proofs.Swarm.UA.XlateInv
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Whisper-Path Excuse Reduction

Lowers `ModelAcceptsTermAfterAttackerSendsClassical` extensions on accepted 32-byte-coins `recv`
runs to `ModelAcceptsTermAfterAttackerSendsMoves` extensions, and proves
`xlate_exc_w_of_movesToCli : AcceptsViaMovesToCliSpec → XlateExcWSpec` by combining that converse
bridge with `XlateInv.xlate_inv` and the forward acceptance bridge hypothesis.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.XlateExcW

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Traceful)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent CliEvent)
open _root_.DY.Libsignal.PQXDH (BobKeyHandles PreKeyMsgHandles)
open _root_.DY.Libsignal.TripleRatchet (TRState TREvent SessionInfo KeyDir isCurrentSnapshot)
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession (Address)
open Symbolic.Swarm.COMPOSED.CompTrace (Preserves)
open Symbolic.Swarm.COMPOSED.CompRatchet (InertOnPQXDH)
open Symbolic.Swarm.CREF (SemReady CBadSigmaFrame stateFaithful_snoc_of_isCurrentSnapshot
  rpkT_bobDoneBaseKeys_append_other rpkT_bobDoneBaseKeys_append_pq
  rpkT_logSkippedKeys_bobDoneBaseKeys)
open Symbolic.Swarm.CREF.CliPure (cbadG2_explains_transfer)
open Symbolic.Swarm.CREF.CliPure.IniPure (bobDoneBaseKeys_next_aliceStart)
open Symbolic.Swarm.CREF.TR (isCurrentSnapshot_of_decrypt_accept
  isCurrentSnapshot_of_decryptSkipped_accept)
open Symbolic.Proofs.Swarm.UA.Defs (XlateExcWSpec runOk failedSend flatEntry flatExit
  callsOf flatEvents SchedFits)
open Symbolic.Proofs.Swarm.UA.SlotInitTransfer (matchesEvents_snoc_run_inv stepsWF_append_iff)
open Symbolic.Proofs.Swarm.UA.XlateSteps (recvRepresentations_eq recvCollision_iff
  reselectCollision_iff stepIn_next stepIn_ok step_reachable runSteps_reachable
  network_preCond attackerSend_next_eq_network eventMatchesEntry_of_bytesMatchEntry
  run_bind_pure_isSome run_bind_pure_snd callStarts_eq_of_coinSplit)
open Symbolic.Proofs.Swarm.UA.XlateInv (xlate_inv schedFits_prefix
  forall₂_rng_of_bytesMatchEntry forall₂_append_join)

/-! ## `bobDoneBaseKeys` Preservation on Zero-Call Move Suffixes -/

section NoBobDone

open scoped _root_.DY.Libsignal.Composed

private abbrev bdInv (L : List _root_.DY.Bytes) (tr : ExecTrace) : Prop :=
  bobDoneBaseKeys tr = L

private theorem bd_inert (L : List _root_.DY.Bytes) : InertOnPQXDH (bdInv L) where
  append_net tr _ h := (rpkT_bobDoneBaseKeys_append_other tr _ rfl).trans h
  append_rnd tr _ h := (rpkT_bobDoneBaseKeys_append_other tr _ rfl).trans h
  append_pqxSt tr _ _ h := (rpkT_bobDoneBaseKeys_append_other tr _ rfl).trans h
  append_pqxEv_nonDone tr ev hne h := by
    dsimp only [bdInv] at h ⊢
    rw [rpkT_bobDoneBaseKeys_append_pq]
    cases ev with
    | BobDone b a ikB ikA spk pqpk opk ek ct keys =>
      exact absurd rfl (hne b a ikB ikA spk pqpk opk ek ct keys).2
    | _ => simpa using h

private theorem bd_pres_genRand {L : List _root_.DY.Bytes} (n : Nat) :
    Preserves (bdInv L) (_root_.DY.Random.genRand n) :=
  (bd_inert L).preserves_genRand n

private theorem bd_pres_sendMessage {L : List _root_.DY.Bytes} (m : _root_.DY.Bytes) :
    Preserves (bdInv L) (_root_.DY.Network.sendMessage m) :=
  (bd_inert L).preserves_sendMessage m

private theorem bd_pres_storeTR {L : List _root_.DY.Bytes} (p : Participant) (st : TRState) :
    Preserves (bdInv L) (_root_.DY.PersistentLocalState.storeLocalState p st) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact (rpkT_bobDoneBaseKeys_append_other tr _ rfl).trans h

private theorem bd_pres_logTR {L : List _root_.DY.Bytes} (ev : TREvent) :
    Preserves (bdInv L) (_root_.DY.ProtocolEvent.logEvent ev) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  dsimp only
  rw [Traceful.run_pure]
  exact (rpkT_bobDoneBaseKeys_append_other tr _ rfl).trans h

private theorem bd_pres_prodCasesOn {L : List _root_.DY.Bytes} {α β γ : Type} (p : α × β)
    (f : α → β → Traceful γ) (hf : ∀ a b, Preserves (bdInv L) (f a b)) :
    Preserves (bdInv L) (Prod.casesOn p f) := by
  rcases p with ⟨a, b⟩; exact hf a b

private theorem bd_pres_optionCasesOn {L : List _root_.DY.Bytes} {α β : Type} (o : Option α)
    (fn : Traceful β) (fs : α → Traceful β)
    (hn : Preserves (bdInv L) fn) (hs : ∀ a, Preserves (bdInv L) (fs a)) :
    Preserves (bdInv L) (Option.casesOn o fn fs) := by
  rcases o with _ | a; exact hn; exact hs a

private theorem bd_pres_dhRatchetStep {L : List _root_.DY.Bytes} (st : TRState)
    (pk : _root_.DY.Bytes) :
    Preserves (bdInv L) (_root_.DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind (bd_pres_genRand 32) fun _ => Preserves.pure _

private theorem bd_pres_ensureReceiverChain {L : List _root_.DY.Bytes} (st : TRState)
    (pk : _root_.DY.Bytes) :
    Preserves (bdInv L) (_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact Preserves.pure _
  · exact Preserves.bind (bd_pres_dhRatchetStep st pk) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem bd_pres_logMessageKeyAndStore {L : List _root_.DY.Bytes} (me : Participant)
    (s : SessionInfo) (dir : KeyDir) (seed pqSalt : _root_.DY.Bytes) (n : UInt32)
    (rIdx par : Nat) (st : TRState) :
    Preserves (bdInv L)
      (_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
        me s dir seed pqSalt n rIdx par st) := by
  unfold _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact Preserves.bind (bd_pres_logTR _) fun _ => bd_pres_storeTR me st

local macro "bd_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply bd_pres_prodCasesOn
  | with_reducible apply bd_pres_optionCasesOn
  | with_reducible apply Preserves.pure | with_reducible apply Preserves.failure
  | with_reducible apply bd_pres_genRand | with_reducible apply bd_pres_storeTR
  | with_reducible apply bd_pres_sendMessage | with_reducible apply Preserves.getLocalState_tr
  | with_reducible apply Preserves.getLocalState_pq | with_reducible apply Preserves.receiveMessage
  | with_reducible apply Preserves.getEntry | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt | with_reducible apply bd_pres_dhRatchetStep
  | with_reducible apply bd_pres_ensureReceiverChain
  | with_reducible apply rpkT_logSkippedKeys_bobDoneBaseKeys
  | with_reducible apply Preserves.guardP | with_reducible apply Preserves.monadLiftErr
  | with_reducible apply Preserves.guardTrace | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength
  | with_reducible apply bd_pres_logMessageKeyAndStore
  | with_reducible apply bd_pres_logTR
  | split | with_reducible intro))

private theorem noBobDone_move (tr : ExecTrace) (m : Move) (hm : m.isSetup = false)
    (hnot_bob : ∀ b a kh regA mh pqIdx spqrMsgIdx shown,
      m ≠ .bobStart b a kh regA mh pqIdx spqrMsgIdx shown) :
    bobDoneBaseKeys (m.next tr) = bobDoneBaseKeys tr := by
  cases m with
  | setup a b withOpk => cases hm
  | aliceStart a b idStateIdx regIdxB bh shown =>
    exact bobDoneBaseKeys_next_aliceStart tr a b idStateIdx regIdxB bh shown
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
    exact absurd rfl (hnot_bob b a kh regIdxA mh pqIdx spqrMsgIdx shown)
  | encrypt me stateIdx coinsLen pqIdx wrap =>
    unfold Move.next Move.act _root_.DY.Libsignal.TripleRatchet.messageEncrypt
    exact (by bd_tac : Preserves (bdInv (bobDoneBaseKeys tr)) _) tr rfl
  | encryptAbort me stateIdx =>
    unfold Move.next Move.act _root_.DY.Libsignal.TripleRatchet.messageEncryptAbort
    exact (by bd_tac : Preserves (bdInv (bobDoneBaseKeys tr)) _) tr rfl
  | encryptFail me stateIdx coinsLen =>
    unfold Move.next Move.act _root_.DY.Libsignal.TripleRatchet.messageEncrypt
    exact (by bd_tac : Preserves (bdInv (bobDoneBaseKeys tr)) _) tr rfl
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    unfold Move.next Move.act; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
    exact (by bd_tac : Preserves (bdInv (bobDoneBaseKeys tr)) _) tr rfl
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx wrapped =>
    unfold Move.next Move.act _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
    exact (by bd_tac : Preserves (bdInv (bobDoneBaseKeys tr)) _) tr rfl
  | reject draws =>
    unfold Move.next Move.act
    rw [Traceful.run_pure]
  | compromiseIK p stateIdx =>
    unfold Move.next Move.act
    exact (Preserves.bind ((bd_inert (bobDoneBaseKeys tr)).preserves_compromiseIK p stateIdx)
      fun _ => Preserves.pure _) tr rfl
  | compromiseSPK p stateIdx =>
    unfold Move.next Move.act
    exact (Preserves.bind ((bd_inert (bobDoneBaseKeys tr)).preserves_compromiseSPK p stateIdx)
      fun _ => Preserves.pure _) tr rfl
  | compromisePQSPK p stateIdx =>
    unfold Move.next Move.act
    exact (Preserves.bind ((bd_inert (bobDoneBaseKeys tr)).preserves_compromisePQSPK p stateIdx)
      fun _ => Preserves.pure _) tr rfl
  | compromiseOPK p stateIdx =>
    unfold Move.next Move.act
    exact (Preserves.bind ((bd_inert (bobDoneBaseKeys tr)).preserves_compromiseOPK p stateIdx)
      fun _ => Preserves.pure _) tr rfl
  | exposeKey me stateIdx k =>
    unfold Move.next Move.act _root_.DY.Libsignal.TripleRatchet.exposeKey
    exact (by bd_tac : Preserves (bdInv (bobDoneBaseKeys tr)) _) tr rfl
  | exposeSpqr me stateIdx =>
    unfold Move.next Move.act _root_.DY.Libsignal.TripleRatchet.exposeSpqr
    exact (by bd_tac : Preserves (bdInv (bobDoneBaseKeys tr)) _) tr rfl
  | exposeSkipped skippedKeyEventIdx =>
    unfold Move.next Move.act _root_.DY.Libsignal.TripleRatchet.exposeSkipped
    exact (by bd_tac : Preserves (bdInv (bobDoneBaseKeys tr)) _) tr rfl
  | attackerSend msg =>
    unfold Move.next Move.act
    exact (Preserves.bind (bd_pres_sendMessage msg) fun _ => Preserves.pure _) tr rfl
  | brkDH =>
    exact (bd_inert (bobDoneBaseKeys tr)).preserves_breakDH tr rfl
  | brkKEM =>
    exact (bd_inert (bobDoneBaseKeys tr)).preserves_breakKEM tr rfl

private theorem callCount_bobStart_pos_local {b a : Participant} {kh : BobKeyHandles}
    {regA : Nat} {mh : PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    {tr : ExecTrace} (ha : (Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).LogsSessionCompletion tr) :
    0 < callCount ((Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).vis tr) := by
  obtain ⟨hsh, -⟩ := ha
  obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by omega⟩
  unfold Move.vis
  rw [callCount_append]
  dsimp only [bobVis]
  unfold callCount
  rw [List.cons_append, List.take_succ_cons, List.filter_cons_of_pos rfl, List.length_cons]
  omega

private theorem bobDoneBaseKeys_eq_of_callCount_zero_local :
    ∀ (L : List Move) (tr : ExecTrace),
      (∀ m ∈ L, m.isSetup = false) →
      MovesAnchored L tr →
      callCount (runMoves L tr).2 = 0 →
      bobDoneBaseKeys (runMoves L tr).1 = bobDoneBaseKeys tr ∧
        ∀ m ∈ L, ∀ promote, m.prekeyPath? = some promote → promote = true
  | [], _, _, _, _ => ⟨rfl, fun _ hm => nomatch hm⟩
  | m :: L, tr, hns, ⟨ha, hancL⟩, hcc => by
    simp only [runMoves, callCount_append] at hcc
    have hcc_m : callCount (m.vis tr) = 0 := by omega
    have hcc_L : callCount (runMoves L (m.next tr)).2 = 0 := by omega
    have hnot_bob : ∀ b a kh regA mh pqIdx spqrMsgIdx shown,
        m ≠ .bobStart b a kh regA mh pqIdx spqrMsgIdx shown := by
      rintro b a kh regA mh pqIdx spqrMsgIdx shown rfl
      have hpos := callCount_bobStart_pos_local ha
      omega
    have hm_ns : m.isSetup = false := hns m (List.mem_cons_self ..)
    obtain ⟨ih_bd, ih_pr⟩ := bobDoneBaseKeys_eq_of_callCount_zero_local L (m.next tr)
      (fun m' hm' => hns m' (List.mem_cons_of_mem _ hm')) hancL hcc_L
    have hm_bd : bobDoneBaseKeys (m.next tr) = bobDoneBaseKeys tr :=
      noBobDone_move tr m hm_ns hnot_bob
    refine ⟨ih_bd.trans hm_bd, fun m' hm' promote hp => ?_⟩
    rcases List.mem_cons.mp hm' with rfl | hm'
    · cases m' <;> simp only [Move.prekeyPath?] at hp
      case bobStart b a kh regA mh pqIdx spqrMsgIdx shown =>
        exact absurd rfl (hnot_bob b a kh regA mh pqIdx spqrMsgIdx shown)
      case decrypt _ _ _ _ _ w =>
        cases w <;> simp at hp; exact hp
      case decryptSkipped _ _ _ _ _ _ w =>
        cases w <;> simp at hp; exact hp
      all_goals cases hp
    · exact ih_pr m' hm' promote hp

end NoBobDone

cref_hide_foreign_instances

/-! ## Converse Acceptance Bridge and Excuse Transfer -/

private theorem post_nil_of_snoc_party {xs ys post : List Step} {s₀ s : Step}
    (hs₀ : s₀.cls = .party) (hpost : ∀ x ∈ post, x.cls = .invisible)
    (heq : xs ++ [s₀] = ys ++ [s] ++ post) :
    post = [] ∧ s = s₀ ∧ ys = xs := by
  cases post with
  | nil =>
    simp only [List.append_nil] at heq
    have hlen : [s₀].length = [s].length := rfl
    exact ⟨rfl,
      (List.singleton_inj.mp (List.append_inj_right' heq hlen)).symm,
      (List.append_inj_left' heq hlen).symm⟩
  | cons p₀ ps =>
    have hne : p₀ :: ps ≠ [] := List.cons_ne_nil p₀ ps
    have hne0 : [s₀] ≠ [] := List.cons_ne_nil s₀ []
    have hlast := congrArg List.getLast? heq
    rw [List.getLast?_append_of_ne_nil _ hne0, List.getLast?_singleton,
      List.getLast?_append_of_ne_nil _ hne, List.getLast?_eq_some_getLast hne,
      Option.some.injEq] at hlast
    have hinv := hpost _ (List.getLast_mem hne)
    rw [← hlast, hs₀] at hinv
    cases hinv

private theorem explains_attackerSend_list {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {τ : List MachineEvent} :
    ∀ (ext : List _root_.DY.Bytes) {ms : List Move}
      (_hkn : ∀ x ∈ ext, x.AttackerKnows (runTraceMoves r ms))
      (_hex : ExplainsMoves interp r S who ok g ms τ),
      ExplainsMoves interp r S who ok g (ms ++ ext.map .attackerSend) τ ∧
        runTraceMoves r (ms ++ ext.map .attackerSend) =
          runSteps (ext.map .network) (runTraceMoves r ms) ∧
        runVis r (ms ++ ext.map .attackerSend) = runVis r ms
  | [], _, _, hex => ⟨by simpa using hex, by simp [runSteps], by simp⟩
  | x :: ext, ms, hkn, hex => by
    have hx_kn : x.AttackerKnows (runTraceMoves r ms) := hkn x (List.mem_cons_self ..)
    have hpre : (Step.network x).PreCond (runTraceMoves r ms) := by
      rwa [network_preCond]
    have hreach_ms : (runTraceMoves r ms).Reachable reachability := hex.1.2.1.2.2.1.1
    have hreach1 : (runTraceMoves r (ms ++ [.attackerSend x])).Reachable reachability := by
      rw [runTrace_snoc, attackerSend_next_eq_network]
      exact step_reachable hreach_ms hpre
    have hex1 : ExplainsMoves interp r S who ok g (ms ++ [.attackerSend x]) τ :=
      explains_attackerSend hex hreach1
    have htr1 : runTraceMoves r (ms ++ [.attackerSend x]) =
        (Step.network x).next (runTraceMoves r ms) := by
      rw [runTrace_snoc, attackerSend_next_eq_network]
    have hvis_nil : (Move.attackerSend x).vis (runTraceMoves r ms) = [] := by
      have hlen1 := hex.1.2.2.2.2.2.length_eq
      have hlen2 := hex1.1.2.2.2.2.2.length_eq
      rw [runVis_snoc, List.length_append] at hlen2
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hvis1 : runVis r (ms ++ [.attackerSend x]) = runVis r ms := by
      rw [runVis_snoc, hvis_nil, List.append_nil]
    have hkn' : ∀ y ∈ ext, y.AttackerKnows (runTraceMoves r (ms ++ [.attackerSend x])) :=
      fun y hy => attackerKnows_append [Move.attackerSend x]
        (hkn y (List.mem_cons_of_mem _ hy))
    obtain ⟨hex_all, htr_all, hvis_all⟩ := explains_attackerSend_list ext hkn' hex1
    refine ⟨?_, ?_, ?_⟩
    · simpa [List.append_assoc] using hex_all
    · change runTraceMoves r (ms ++ (Move.attackerSend x :: ext.map Move.attackerSend)) =
        runSteps (ext.map Step.network) ((Step.network x).next (runTraceMoves r ms))
      rw [← htr1, ← htr_all]
      simp [List.append_assoc]
    · rw [← hvis1, ← hvis_all]
      simp [List.append_assoc]

private theorem mem_snd_of_mem_zip_local {α β : Type} :
    ∀ {xs : List α} {ys : List β} {p : α × β}, p ∈ xs.zip ys → p.2 ∈ ys
  | [], _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | _ :: _, _ :: _, _, h =>
    (List.mem_cons.mp h).elim (fun heq => heq ▸ List.mem_cons_self ..)
      (fun h' => List.mem_cons_of_mem _ (mem_snd_of_mem_zip_local h'))

private theorem readOKWith_of_readsFaithfully_local {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {tr : ExecTrace} (htr : runTraceMoves r ms = tr)
    {e : MachineEvent} {v : VisEntry} {b : HwBytes} (heb : eventBytes e = b)
    (h : ReadsFaithfully interp r S g tr v b) :
    ReadOKWith (recvRepresentations interp r S g ms) (preKeyRepresentations interp r S g ms) e v := by
  subst htr; subst heb; revert h
  unfold ReadOKWith ReadsFaithfully
  cases v.layout <;> exact id

private theorem all_rng_map :
    ∀ (ps : List HwBytes), (ps.map MachineEvent.rng).all (fun ev => eventKind ev == .rng) = true
  | [] => rfl
  | _ :: ps => all_rng_map ps

private theorem callStarts_rng_map_local :
    ∀ (ps : List HwBytes) (τ : List MachineEvent),
      callStarts (ps.map MachineEvent.rng ++ τ) = callStarts τ
  | [], _ => rfl
  | _ :: ps, τ => callStarts_rng_map_local ps τ

private theorem decrypt_step_to_move {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {s : Step} {ev : RunEvent} {v : List VisEntry}
    {msgIdx : Nat} {vo : VisEntry}
    (hs_dec : s.decryptMsgIdx? = some msgIdx)
    (hs_party : s.party? = some ev.party)
    (hs_ok : s.ok tr = true)
    (hv_eq : v = stepView s tr (runWrapped ev))
    (hreach_next : (s.next tr).Reachable reachability)
    (hvo_mem_v : vo ∈ v) (hvo_kind : vo.kind = .accept)
    (hpath_at : PathFaithfulAt interp S g tr s ev.input) :
    ∃ m : Move,
      m.decryptMsgIdx? = some msgIdx ∧
      m.next tr = s.next tr ∧
      m.vis tr = v ∧
      MoveOK r m tr ∧
      m.party? = some ev.party ∧
      (∀ ds, m ≠ .reject ds) ∧
      (∀ p k b, m.stateLoad? = some (p, k, b) → isCurrentSnapshot tr k = true) ∧
      (∀ p, parsePreKeyWire ev.input = some p →
        ∃ ek ∈ bobDoneBaseKeys tr, ecKey (gamma interp S g ek) = p.baseKey.take 33) ∧
      (∀ promote, m.prekeyPath? = some promote → promote = true) := by
  cases s with
  | messageDecrypt me stateIdx msgIdx' pqIdx spqrMsgIdx =>
    simp only [Step.decryptMsgIdx?, Option.some.injEq] at hs_dec
    subst msgIdx'
    let s0 := Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx
    let m : Move := .decrypt me stateIdx msgIdx pqIdx spqrMsgIdx (runWrapped ev)
    have hnxt : m.next tr = s0.next tr := by
      dsimp only [m, s0, Move.next, Move.act, Step.next, Step.toInput]
      erw [stepIn_next]; exact run_bind_pure_snd _ tr
    have hvis : m.vis tr = v := by
      rw [hv_eq]
      change decVis tr (m.next tr) stateIdx msgIdx (runWrapped ev) ++
          exposures tr (m.next tr) = stepView s0 tr (runWrapped ev)
      rw [hnxt]; dsimp only [s0, stepView]; simp only [hs_ok, ↓reduceIte]
    have hreach_m : (m.next tr).Reachable reachability := hnxt ▸ hreach_next
    have hvo_m : vo ∈ m.vis tr := hvis ▸ hvo_mem_v
    have hcur_st : isCurrentSnapshot tr stateIdx = true :=
      isCurrentSnapshot_of_decrypt_accept hreach_m ⟨vo, hvo_m, hvo_kind⟩
    refine ⟨m, rfl, hnxt, hvis, ⟨rfl, trivial, trivial, trivial, trivial⟩, hs_party,
      (fun _ h => nomatch h), ?_, fun p hp => hpath_at p hp, fun promote hp => ?_⟩
    · intro p k b hld
      dsimp only [m, Move.stateLoad?] at hld
      have hk : stateIdx = k := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hld)).2).1
      subst hk; exact hcur_st
    · dsimp only [m, Move.prekeyPath?] at hp
      cases hw : runWrapped ev <;> simp [hw] at hp
      exact hp
  | messageDecryptSkipped me stateIdx msgIdx' skIdx pqIdx spqrMsgIdx =>
    simp only [Step.decryptMsgIdx?, Option.some.injEq] at hs_dec
    subst msgIdx'
    let s0 := Step.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx
    let m : Move := .decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx (runWrapped ev)
    have hnxt : m.next tr = s0.next tr := by
      dsimp only [m, s0, Move.next, Move.act, Step.next, Step.toInput]
      erw [stepIn_next]; exact run_bind_pure_snd _ tr
    have hvis : m.vis tr = v := by
      rw [hv_eq]
      change decVis tr (m.next tr) stateIdx msgIdx (runWrapped ev) ++
          exposures tr (m.next tr) = stepView s0 tr (runWrapped ev)
      rw [hnxt]; dsimp only [s0, stepView]; simp only [hs_ok, ↓reduceIte]
    have hreach_m : (m.next tr).Reachable reachability := hnxt ▸ hreach_next
    have hvo_m : vo ∈ m.vis tr := hvis ▸ hvo_mem_v
    have hcur_st : isCurrentSnapshot tr stateIdx = true :=
      isCurrentSnapshot_of_decryptSkipped_accept hreach_m ⟨vo, hvo_m, hvo_kind⟩
    refine ⟨m, rfl, hnxt, hvis, ⟨rfl, trivial, trivial, trivial, trivial⟩, hs_party,
      (fun _ h => nomatch h), ?_, fun p hp => hpath_at p hp, fun promote hp => ?_⟩
    · intro p k b hld
      dsimp only [m, Move.stateLoad?] at hld
      have hk : stateIdx = k := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hld)).2).1
      subst hk; exact hcur_st
    · dsimp only [m, Move.prekeyPath?] at hp
      cases hw : runWrapped ev <;> simp [hw] at hp
      exact hp
  | _ => cases hs_dec

private theorem movesAnchored_append_right :
    ∀ (l₁ l₂ : List Move) (tr : ExecTrace),
      MovesAnchored (l₁ ++ l₂) tr → MovesAnchored l₂ (runMoves l₁ tr).1
  | [], _, _, h => h
  | m :: l₁, l₂, tr, ⟨_, h⟩ => movesAnchored_append_right l₁ l₂ (m.next tr) h

/-- Forward acceptance bridge: on an accepted 32-byte-coins `recv` run `ev`, any
`ModelAcceptsTermAfterAttackerSendsMoves` extension of `(τ₁', g', ms')` lifts to a `Step`-level
`ModelAcceptsTermAfterAttackerSendsClassical` extension of `(g', ss')`. -/
abbrev AcceptsViaMovesToCliSpec : Prop :=
  ∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {ok : Nat → Bool} {evs : List CliEvent} {ev : RunEvent} {g' : Ghost} {ss' : List Step}
    {vis' : List VisEntry} {τ₁' : List MachineEvent} {ms' : List Move}
    {peer : Address} {out : HwBytes} {σ_rest : List MachineEvent} {t : _root_.DY.Bytes},
    ProtocolSetupWF r → SemReady interp' r S →
    SchedFits (callsOf (evs ++ [.run ev])) who ok →
    ExplainsClassical interp' r S g' ss' vis' evs →
    ExplainsCli interp' r S who ok (flatEvents evs) τ₁' g' ms' →
    runTraceMoves r ms' = runTrace r ss' →
    ev.cmd = .recv peer → ev.exit = some (0, out) → ev.coins.length = 32 →
    (∀ p, parsePreKeyWire ev.input = some p →
      p.version = 4 ∧ p.identityKey.take 33 = ecKey (pubBytes interp' (secretBytes r 0))) →
    ModelAcceptsTermAfterAttackerSendsMoves interp' r S who ok g' ms' τ₁' (.recv ev.input)
      (.rng ev.coins :: .accept out :: σ_rest) t →
    ModelAcceptsTermAfterAttackerSendsClassical interp' r S g' ss' evs ev t

private theorem acceptsViaCli_to_acceptsViaCliMoves
    {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {ok : Nat → Bool} {evs : List CliEvent} {ev : RunEvent} {g' : Ghost} {ss' : List Step}
    {τ₁' : List MachineEvent} {ms' : List Move}
    {peer : Address} {out : HwBytes} {t : _root_.DY.Bytes}
    (hsched : SchedFits (callsOf (evs ++ [.run ev])) who ok)
    (hexp_c' : ExplainsCli interp' r S who ok (flatEvents evs) τ₁' g' ms')
    (htr' : runTraceMoves r ms' = runTrace r ss')
    (hcmd : ev.cmd = .recv peer) (hexit : ev.exit = some (0, out))
    (hacc_u : ModelAcceptsTermAfterAttackerSendsClassical interp' r S g' ss' evs ev t) :
    ModelAcceptsTermAfterAttackerSendsMoves interp' r S who ok g' ms' τ₁' (.recv ev.input)
      [.rng ev.coins, .accept out] t := by
  obtain ⟨ext, s_dec, msgIdx, g₁, vis₁, hkn, hs_dec, hg₁_addr, hg₁_σ, hmsg, hexp₁⟩ := hacc_u
  have hs_dec_cls : s_dec.cls = .party := by
    cases s_dec <;> simp [Step.decryptMsgIdx?, Step.cls] at hs_dec ⊢
  have hnotRej : ¬ RunRejected ev := fun hrej => hrej out hexit
  obtain ⟨ss₁, pre, s, post, _, v, hss_eq, _, _, _, hrm_raw, hpost_inv⟩ :=
    matchesEvents_snoc_run_inv hnotRej evs hexp₁.2.2.2
  obtain ⟨rfl, hs_eq, hpre_eq⟩ := post_nil_of_snoc_party hs_dec_cls hpost_inv hss_eq
  subst s
  let tr_net := runTrace r (ss' ++ ext.map .network)
  have hrm : RunMatches interp' r S g₁ tr_net s_dec ev v (activeBundleIds evs) := by
    have htr_eq : runSteps pre (runSteps ss₁ (setupTrace r)) = tr_net := by
      change runSteps pre (runTrace r ss₁) = tr_net
      rw [← Symbolic.Proofs.Swarm.UA.Base.runTrace_append, hpre_eq]
    rwa [htr_eq] at hrm_raw
  have hfr : CBadSigmaFrame g' g₁ (runTrace r ss').length :=
    ⟨fun ts hts len => congrFun (hg₁_σ ts hts) len, hg₁_addr⟩
  have hex_ms' : ExplainsMoves interp' r S who ok g₁ ms' τ₁' :=
    cbadG2_explains_transfer hfr (by rw [htr']) ⟨hexp_c'.2.1, hexp_c'.2.2.1.1⟩
  have hkn_m : ∀ x ∈ ext, x.AttackerKnows (runTraceMoves r ms') := by rwa [htr']
  obtain ⟨hex_net, htr_net_raw, hvis_net⟩ := explains_attackerSend_list ext hkn_m hex_ms'
  let ms_net := ms' ++ ext.map .attackerSend
  have htr_net : runTraceMoves r ms_net = tr_net := by
    dsimp only [ms_net, tr_net]
    rw [htr_net_raw, htr', ← Symbolic.Proofs.Swarm.UA.Base.runTrace_append]
  have hswf_s : StepsWF [s_dec] tr_net :=
    ((stepsWF_append_iff (ss' ++ ext.map Step.network) [s_dec] (setupTrace r)).mp
      hexp₁.2.2.1.2.2.1).2
  have hreach_net : tr_net.Reachable reachability := by
    rw [← htr_net]; exact hex_net.1.2.1.2.2.1.1
  have hreach_next : (s_dec.next tr_net).Reachable reachability :=
    step_reachable hreach_net hswf_s.1
  obtain ⟨_, hs_party, _, _, hs_ok, _, hv_eq, inp, drs, outs, hv_split,
    hinp_bme, ⟨pieces, hpieces_ne, hpieces_pref, hdrs_f2⟩, houts_om, hread_inp, hpath_at⟩ := hrm
  unfold OutputsMatch at houts_om
  simp only [hexit, hcmd] at houts_om
  obtain ⟨vo, rfl, hvo_bme⟩ := houts_om
  have hvo_mem_v : vo ∈ v := by rw [hv_split]; simp
  obtain ⟨m_dec, hm_dec, hnxt, hvis_m, hmok, hparty, hnot_rej, hcur, hpath_ek, hprom_true⟩ :=
    decrypt_step_to_move hs_dec hs_party hs_ok hv_eq hreach_next hvo_mem_v hvo_bme.1.symm hpath_at
  have hsf' : StateFaithful r (ms_net ++ [m_dec]) :=
    stateFaithful_snoc_of_isCurrentSnapshot hex_net.1.2.1.2.2.2.2.2.2 (by rw [htr_net]; exact hcur)
  have hreach_all : (runTraceMoves r (ms_net ++ [m_dec])).Reachable reachability := by
    rw [runTrace_snoc, htr_net, hnxt]; exact hreach_next
  have hrun' : ModelRun r (ms_net ++ [m_dec]) :=
    modelRun_snoc hex_net.1.2.1 (by rw [htr_net]; exact hmok) hreach_all
      (fun j mj p k b hmj hld hact hml => by
        have hlt_j : j < ms_net.length := (List.getElem?_eq_some_iff.mp hmj).1
        exact hsf' j ms_net.length mj m_dec p k b hlt_j
          (by rw [List.getElem?_append_left hlt_j]; exact hmj)
          (by simp)
          hld
          (by rw [List.take_append_of_le_length (Nat.le_of_lt hlt_j)]; exact hact)
          hml)
  let τ₂ : List MachineEvent := pieces.map .rng ++ [.accept out]
  let k : Nat := pieces.length
  have hcs₂ : CoinSplit [.rng ev.coins, .accept out] τ₂ :=
    .split hpieces_ne hpieces_pref (.keep (fun _ h => nomatch h) .nil)
  have hτ₂_k : τ₂[k]? = some (.accept out) := by
    dsimp only [τ₂, k]
    have hlen_map : (pieces.map MachineEvent.rng).length = pieces.length := List.length_map _
    rw [← hlen_map, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero]
  have hτ₂_take_k : τ₂.take k = pieces.map .rng := by
    dsimp only [τ₂, k]
    have hlen_map : (pieces.map MachineEvent.rng).length = pieces.length := List.length_map _
    rw [← hlen_map, List.take_left]
  have hτ₂_all : (τ₂.take k).all (fun e => eventKind e == .rng) = true := by
    rw [hτ₂_take_k]; exact all_rng_map pieces
  have hτ₂_take_succ : τ₂.take (k + 1) = τ₂ := by
    apply List.take_of_length_le
    simp [τ₂, k]
  let blk : List MachineEvent := .recv ev.input :: τ₂
  have hcs_blk_starts : callStarts blk = [.recv ev.input] := by
    have h1 : blk = [.recv ev.input] ++ (pieces.map .rng ++ [.accept out]) := rfl
    rw [h1, callStarts_append, callStarts_rng_map_local]
    rfl
  have hrok : runOk ev = true := by simp [runOk, hexit]
  have hfs : failedSend ev = false := by simp [failedSend, hcmd]
  have hcalls_at : (callsOf (evs ++ [.run ev]))[(callsOf evs).length]? = some (ev.party, true) := by
    rw [Symbolic.Proofs.Swarm.UA.Base.callsOf_append]
    simp [callsOf, hfs, hrok]
  have hcc_net : callCount (runVis r ms_net) = (callStarts τ₁').length :=
    matchedPrefix_callCount_eq hex_net.1
  have hcs_len : (callStarts τ₁').length = (callsOf evs).length := by
    rw [callStarts_eq_of_coinSplit hexp_c'.1,
      Symbolic.Proofs.Swarm.UA.Base.callStarts_flatEvents_length]
  have hwho_k : who[callCount (runVis r ms_net)]? = some ev.party := by
    rw [hcc_net, hcs_len]
    obtain ⟨w_rest, hw_eq⟩ := hsched.1
    have hmap_at : ((callsOf (evs ++ [.run ev])).map Prod.fst)[(callsOf evs).length]? =
        some ev.party := by simp [hcalls_at]
    have hlt_map : (callsOf evs).length <
        ((callsOf (evs ++ [.run ev])).map Prod.fst).length :=
      (List.getElem?_eq_some_iff.mp hmap_at).1
    rw [← hw_eq, List.getElem?_append_left hlt_map]
    exact hmap_at
  have hok_k : ok (callCount (runVis r ms_net)) = true := by
    rw [hcc_net, hcs_len]
    exact hsched.2 _ _ _ hcalls_at
  have hinp_eme : EventMatchesEntry interp' r S g₁ (.recv ev.input) inp := by
    refine eventMatchesEntry_of_bytesMatchEntry (e := .recv ev.input) (initIds := none) ?_
    dsimp only [eventKind, eventBytes]
    have hik : inputKind ev = .recv := by unfold inputKind; rw [hcmd]
    rwa [hik] at hinp_bme
  obtain ⟨hdrs_eme, hdrs_kind⟩ := forall₂_rng_of_bytesMatchEntry hdrs_f2
  have hvo_eme : EventMatchesEntry interp' r S g₁ (.accept out) vo :=
    eventMatchesEntry_of_bytesMatchEntry (e := .accept out) hvo_bme
  have hvis_m_net : m_dec.vis (runTraceMoves r ms_net) = v := by rw [htr_net, hvis_m]
  have hF_blk : List.Forall₂ (EventMatchesEntry interp' r S g₁) blk
      (runMoves [m_dec] (runTraceMoves r ms_net)).2 := by
    simp only [runMoves, List.append_nil, hvis_m_net, hv_split, blk, τ₂]
    exact .cons hinp_eme (forall₂_append_join hdrs_eme (.cons hvo_eme .nil))
  have hpath' : PathFaithful interp' r S g₁ (ms_net ++ [m_dec]) (τ₁' ++ blk) := by
    intro i mi promote b p hmi hp hcs_i hpw
    by_cases hlt : i < ms_net.length
    · rw [List.getElem?_append_left hlt] at hmi
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at hcs_i ⊢
      have hsplit_net : ms_net = ms_net.take i ++ ms_net.drop i :=
        (List.take_append_drop i ms_net).symm
      have hvis_split : runVis r ms_net =
          runVis r (ms_net.take i) ++
            (runMoves (ms_net.drop i) (runTraceMoves r (ms_net.take i))).2 := by
        conv_lhs => rw [hsplit_net]
        exact runVis_append r (ms_net.take i) (ms_net.drop i)
      have hcc_le : callCount (runVis r (ms_net.take i)) ≤ (callStarts τ₁').length := by
        rw [← hcc_net, hvis_split, callCount_append]; omega
      rcases Nat.lt_or_eq_of_le hcc_le with hk_lt | hk_eq
      · rw [callStarts_append, List.getElem?_append_left hk_lt] at hcs_i
        exact hex_net.1.2.2.2.1 i mi promote b p hmi hp hcs_i hpw
      · rw [callStarts_append, hk_eq, hcs_blk_starts, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq,
          MachineEvent.recv.injEq] at hcs_i
        subst hcs_i
        have hcc_drop :
            callCount (runMoves (ms_net.drop i) (runTraceMoves r (ms_net.take i))).2 = 0 := by
          have h1 := congrArg callCount hvis_split
          rw [callCount_append, hcc_net, hk_eq] at h1
          omega
        have hanc_all : MovesAnchored ms_net (setupTrace r) := hex_net.1.2.1.2.2.1.2.1
        rw [hsplit_net] at hanc_all
        have hanc_drop : MovesAnchored (ms_net.drop i) (runTraceMoves r (ms_net.take i)) :=
          movesAnchored_append_right (ms_net.take i) (ms_net.drop i) (setupTrace r) hanc_all
        have hns_drop : ∀ m'' ∈ ms_net.drop i, m''.isSetup = false :=
          fun m'' hm'' => hex_net.1.2.1.2.1 m'' (List.mem_of_mem_drop hm'')
        obtain ⟨hbd_eq, hpr_true⟩ := bobDoneBaseKeys_eq_of_callCount_zero_local
          (ms_net.drop i) (runTraceMoves r (ms_net.take i)) hns_drop hanc_drop hcc_drop
        have htr_drop : (runMoves (ms_net.drop i) (runTraceMoves r (ms_net.take i))).1 =
            runTraceMoves r ms_net := by
          rw [← runTrace_append, ← hsplit_net]
        rw [htr_drop, htr_net] at hbd_eq
        have hmi_mem : mi ∈ ms_net.drop i := by
          have hdrop_eq : ms_net.drop i = mi :: ms_net.drop (i + 1) := by
            rw [← List.cons_getElem_drop_succ (h := hlt)]
            rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hmi
            rw [hmi]
          rw [hdrop_eq]
          exact List.mem_cons_self ..
        have hprom : promote = true := hpr_true mi hmi_mem promote hp
        rw [← hbd_eq]
        exact ⟨fun _ => hpath_ek p hpw, fun _ => hprom⟩
    · have hi_lt : i < (ms_net ++ [m_dec]).length := (List.getElem?_eq_some_iff.mp hmi).1
      simp only [List.length_append, List.length_singleton] at hi_lt
      have hi_eq : i = ms_net.length := by omega
      subst hi_eq
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hmi
      subst hmi
      have htkm : (ms_net ++ [m_dec]).take ms_net.length = ms_net := by simp
      rw [htkm] at hcs_i ⊢
      rw [hcc_net, callStarts_append, hcs_blk_starts, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq,
        MachineEvent.recv.injEq] at hcs_i
      subst hcs_i
      rw [htr_net]
      exact ⟨fun _ => hpath_ek p hpw, fun _ => hprom_true promote hp⟩
  have hread_blk : ∀ evz ∈ blk.zip (runMoves [m_dec] (runTraceMoves r ms_net)).2,
      evz.2.kind = .recv →
      ReadOKWith (recvRepresentations interp' r S g₁ (ms_net ++ [m_dec]))
        (preKeyRepresentations interp' r S g₁ (ms_net ++ [m_dec])) evz.1 evz.2 := by
    simp only [runMoves, List.append_nil, hvis_m_net, hv_split, blk, τ₂, List.zip_cons_cons]
    intro evz hevz hk
    rcases List.mem_cons.mp hevz with rfl | htail
    · exact ReadOKWith.mono (recvRepresentations_append_subset interp' r S g₁ ms_net [m_dec])
        (preKeyRepresentations_append_subset interp' r S g₁ ms_net [m_dec])
        (readOKWith_of_readsFaithfully_local htr_net rfl hread_inp)
    · rcases List.mem_append.mp (mem_snd_of_mem_zip_local htail) with hd | ho
      · rw [hdrs_kind _ hd] at hk; cases hk
      · rcases List.mem_singleton.mp ho with rfl
        rw [← hvo_bme.1] at hk; cases hk
  have hmp' : MatchedPrefix interp' r S who g₁ (ms_net ++ [m_dec]) (τ₁' ++ blk) :=
    matchedPrefix_append hex_net.1 hrun'
      (roleFaithful_snoc_party hex_net.1.2.2.1 hparty hwho_k)
      hpath' hread_blk hF_blk
  have hout' : OutcomeFaithful r ok (ms_net ++ [m_dec]) := by
    refine outcomeFaithful_append hex_net.2 fun j mj hj => ?_
    rcases j with _ | j
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
      simp only [List.take_zero, List.append_nil]
      exact ⟨fun ds hr => absurd hr (hnot_rej ds), fun _ => hok_k⟩
    · simp at hj
  refine ⟨τ₂, hcs₂, ext, m_dec, msgIdx, k, out, g₁, hkn_m, hm_dec, hg₁_addr,
    fun i hi => hg₁_σ i (htr' ▸ hi), ?_, hτ₂_k, hτ₂_all, ?_⟩
  · rwa [htr_net]
  · rw [hτ₂_take_succ]
    exact ⟨hmp', hout'⟩

/-- Transfers whisper-path collision excuses from move-level explanations to `Step`-level
explanations given `AcceptsViaMovesToCliSpec`. -/
theorem xlate_exc_w_of_movesToCli (h_m2c : AcceptsViaMovesToCliSpec) : XlateExcWSpec := by
  intro interp' r S who ok evs ev g₀ ss₀ vis₀ peer out b t_clean accepted
    hwf hS hsched _ hexp₀ _ hcmd hexit hcoins hrep₀ hpath hncol τ₁ g ms _ _ hexc_m
  have hsched₀ : SchedFits (callsOf evs) who ok := by
    rw [Symbolic.Proofs.Swarm.UA.Base.callsOf_append] at hsched
    exact schedFits_prefix hsched
  have hpath_hdr : ∀ p, parsePreKeyWire ev.input = some p →
      p.version = 4 ∧ p.identityKey.take 33 = ecKey (pubBytes interp' (secretBytes r 0)) := by
    intro q hq
    rcases hpath with ⟨body, hinp, _⟩ | ⟨p, hpw, _, hver, hik, _⟩
    · rw [hinp] at hq
      simp [parsePreKeyWire, _root_.DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag,
        _root_.DY.Libsignal.PQXDH.Refinement.wirePrekeyTag] at hq
    · injection (hpw.symm.trans hq) with hqp
      subst hqp
      exact ⟨hver, hik⟩
  have hexc_u : SignalMsgAcceptedOnlyViaCollisionClassical interp' r S g₀ ss₀ evs ev b := by
    refine ⟨hrep₀, fun g' ss' vis' hexp' hnrc' => ?_⟩
    obtain ⟨τ₁', ms', hexp_c', hnrc_c', htr', hsalts', hpre', hpt'⟩ :=
      xlate_inv hwf hS hsched₀ hexp' hnrc'
    rcases hexc_m.2 τ₁' g' ms' hexp_c' hnrc_c' with hall_col | ⟨⟨t₀, ht₀_m, hacc_m⟩, hall_acc⟩
    · refine Or.inl fun t ht => ?_
      have ht_m : t ∈ recvRepresentations interp' r S g' ms' b := by
        rwa [recvRepresentations_eq htr']
      rcases hall_col t ht_m with hrc | hrsc
      · exact Or.inl ((recvCollision_iff htr' hsalts' hpre' hpt').mp hrc)
      · exact Or.inr ((reselectCollision_iff htr' hsalts' hpre' hpt').mp hrsc)
    · refine Or.inr ⟨⟨t₀, ?_, ?_⟩, fun t ht hacc_u => ?_⟩
      · rwa [← recvRepresentations_eq htr']
      · exact h_m2c hwf hS hsched hexp' hexp_c' htr' hcmd hexit hcoins hpath_hdr hacc_m
      · have ht_m : t ∈ recvRepresentations interp' r S g' ms' b := by
          rwa [recvRepresentations_eq htr']
        have hacc_m' :=
          acceptsViaCli_to_acceptsViaCliMoves hsched hexp_c' htr' hcmd hexit hacc_u
        exact (recvCollision_iff htr' hsalts' hpre' hpt').mp (hall_acc t ht_m hacc_m')
  apply hncol
  refine ⟨evs, ev, [], g₀, ss₀, vis₀, rfl, hexp₀, ?_⟩
  simp only [NextEventCollidesClassical, hcmd]
  refine ⟨⟨out, hexit⟩, ?_⟩
  rcases hpath with ⟨body, hinp, rfl⟩ | ⟨p, hpw, rfl, hver, hik, hkb⟩
  · rw [hinp]
    exact Or.inl ⟨rfl, hexc_u⟩
  · cases hinp : ev.input with
    | nil => rw [hinp] at hpw; cases hpw
    | cons tag body =>
      have hpw' : parsePreKeyWire (tag :: body) = some p := by rwa [← hinp]
      exact Or.inr ⟨p, hpw', Or.inl ⟨hkb, hver, hik, hexc_u⟩⟩

end Symbolic.Proofs.Swarm.UA.XlateExcW
