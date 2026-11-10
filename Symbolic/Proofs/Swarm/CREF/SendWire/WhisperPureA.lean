/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvSend
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SkippedKeyRunInvPure
import Symbolic.Proofs.Swarm.CREF.Initiate.TransferPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.SendWire.ModelSteps
import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.DYBridge.DY.Bytes.Basic
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
# Whisper `SendWire` Block Shape, Quietness, and Encrypt Matching

Proves single-session `PureCRecRelH` reduction, failed-block quietness, `CHist` preservation across
encrypt blocks, and return-block visible-event matching (`snd_encrypt_vis_match`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.SndPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.CliPure.IniSndPure
open Symbolic.Swarm.CREF.SendWire
cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)

abbrev PureRecPending : HwBytes → Prop := TR.PureRecPending

/-- A `SingleSession` record (`rr.previous = []`) cannot satisfy `PureCPrevRel`, reducing
`PureCRecRelH` directly to `PureCRecRel`. -/
theorem pureCRecRelH_single {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {p : Participant} {rec : HwBytes}
    (h : PureCRecRelH interp r S g ms p rec)
    (hss : SingleSession rec) :
    PureCRecRel interp r S g ms p rec := by
  rcases h with h | ⟨rr', hrr', hprev_ne, _⟩
  · exact h
  · exfalso
    obtain ⟨rr, hrr, hprev_eq⟩ := hss
    have hprev := congrArg RecordRec.previous (TR.recordBytes_injective (hrr.symm.trans hrr'))
    dsimp only [TR.normPending] at hprev
    exact hprev_ne (hprev.symm.trans hprev_eq)

theorem snd_callStarts_ret (pt msg : HwBytes) {mid : List MachineEvent}
    (hmid : ∃ coins : HwBytes, (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) :
    callStarts ((MachineEvent.pt pt :: mid) ++ [.send msg]) = [.pt pt] := by
  obtain ⟨coins, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := hmid <;> rfl

theorem snd_ret_sendsFit (pt : HwBytes) {mid : List MachineEvent}
    (hmid : ∃ coins : HwBytes, (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins]))
    {msg : HwBytes} (hlt : msg.length < 2 ^ 64) :
    TR.SendsFit ((MachineEvent.pt pt :: mid) ++ [.send msg]) := by
  intro b hb
  obtain ⟨coins, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := hmid <;>
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      MachineEvent.send.injEq, reduceCtorEq, or_false, false_or] at hb <;>
    subst hb <;> omega

theorem not_aliceInitPending_of_not_recPending {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {rec : HwBytes}
    (hnpend : ¬ PureRecPending rec) :
    ¬ PureAliceInitPending interpretation r S g ms rec := by
  intro hp
  obtain ⟨sess, _sc, _remote, items, _kpk, _st, _stateIdx, _ekIdx, _ctIdx, _ek, _ct,
    hcanon, _h1, _h2, _h3, _h4, _h5, _h6, _h7, _h8, _h9, _h10, _h11, _h12, _h13, _h14,
    _h15, _h16, _h17, _h18, hppk, _⟩ := hp
  exact hnpend ⟨sess, hcanon, by rw [hppk]; rfl⟩

theorem snd_fail_blockHead (pt : HwBytes) (mid : List MachineEvent) :
    ∀ e ∈ (MachineEvent.pt pt :: mid).head?, eventKind e = .recv ∨ eventKind e = .pt := by
  intro e he
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
  subst he
  exact Or.inr rfl

theorem snd_ret_tail_kinds (msg : HwBytes) {mid : List MachineEvent}
    (hmid : ∃ coins : HwBytes, (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) :
    ∀ e ∈ mid ++ [MachineEvent.send msg],
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
  intro e he
  rcases hmid with ⟨coins, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩
  · simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; simp [eventKind]
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [eventKind]

theorem snd_coins_eq_of_mid {mid : List MachineEvent} {c₁ c₂ : HwBytes}
    (h₁ : (c₁ = [] ∧ mid = []) ∨ (c₁ ≠ [] ∧ mid = [.rng c₁]))
    (h₂ : (c₂ = [] ∧ mid = []) ∨ (c₂ ≠ [] ∧ mid = [.rng c₂])) : c₁ = c₂ := by
  rcases h₁ with ⟨rfl, rfl⟩ | ⟨_, rfl⟩ <;> rcases h₂ with ⟨rfl, h⟩ | ⟨_, h⟩
  · rfl
  · cases h
  · cases h
  · injection h with h; injection h

theorem snd_roleSnapshots_quiet {r : ProtocolSetup} {ms₀ δ : List Move}
    (hq : MovesFrom NoSessionEffect (runTraceMoves r ms₀) δ)
    (hrole : RoleSnapshots r (runTraceMoves r ms₀)) :
    RoleSnapshots r (runTraceMoves r (ms₀ ++ δ)) := by
  rw [runTrace_append]
  exact roleSnapshots_of_movesFrom_noSessionEffect hq hrole

section SndQuiet
open XplSteps
open TripleRatchet (TRState)

theorem xquiet_messageEncryptAbort (me : Participant) (si : Nat) :
    XQuiet (TripleRatchet.messageEncryptAbort me si) := by
  unfold TripleRatchet.messageEncryptAbort
  exact xquiet_bind (xquiet_of_fix (xfix_getLocalState _ _)) fun _ =>
    xquiet_bind (xquiet_genRand _) fun _ => xquiet_of_fix xfix_failure

def XLastSent (n : Nat) (t : ExecTrace) : Prop :=
  n < t.length ∧ ∃ w, t.getMessageSentAt (t.length - 1) = some w

theorem xlastSent_anti : QAnti XLastSent :=
  fun _ _ _ hle ⟨hlt, h⟩ => ⟨Nat.lt_of_le_of_lt hle hlt, h⟩

theorem xest_sendMessage (b : DY.Bytes) : XEst XLastSent (DY.Network.sendMessage b) := by
  intro tr
  have hrun : ((DY.Network.sendMessage b).run tr).2.val = tr.append (⟨b⟩ : DY.Network.ExecEntryT) := by
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  dsimp only [XEst, XLastSent]
  rw [hrun]
  have hlen : (tr.append (⟨b⟩ : DY.Network.ExecEntryT)).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  refine ⟨by omega, b, ?_⟩
  rw [hlen, Nat.add_sub_cancel, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1,
    DY.Trace.at?_append tr (⟨b⟩ : DY.Network.ExecEntryT)]

theorem xtotal_storeLocalState (me : Participant) (st : TRState) :
    XTotal (PersistentLocalState.storeLocalState me st) := fun tr =>
  ⟨tr.length, by
    simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]⟩

theorem xtotal_logMessageKeyAndStore (me : Participant) (s : TripleRatchet.SessionInfo)
    (dir : TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (r p : Nat)
    (st : TRState) :
    XTotal (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r p st) := by
  unfold TripleRatchet.logMessageKeyAndStore
  exact xtotal_bind (xtotal_logEvent_tr _) fun _ => xtotal_storeLocalState _ _

theorem xmix_messageEncrypt (me : Participant) (si cl pq : Nat) :
    XMix XLastSent (TripleRatchet.messageEncrypt me si cl pq) := by
  have hA := xlastSent_anti
  unfold TripleRatchet.messageEncrypt
  refine xmix_bind_quiet hA (xquiet_of_fix (xfix_getLocalState _ _)) fun _ => ?_
  refine xmix_bind_quiet hA (xquiet_of_fix (xfix_guard _)) fun _ => ?_
  refine xmix_bind_quiet hA (xquiet_genRand _) fun _ => ?_
  refine xmix_bind_quiet hA (xquiet_genRand _) fun _ => ?_
  refine xmix_bind_quiet hA (xquiet_sendMessage _) fun _ => ?_
  refine xmix_bind_quiet hA (xquiet_of_fix (xfix_receiveMessage _)) fun _ => ?_
  refine xmix_of_est ?_
  refine xest_bind_total hA (xtotal_logEvent_tr _) fun _ => ?_
  refine xest_bind_total hA (xtotal_logMessageKeyAndStore _ _ _ _ _ _ _ _ _) fun _ => ?_
  exact xest_sendMessage _

theorem xmix_move_encrypt (tr : ExecTrace) {me : Participant} {si cl pq : Nat}
    {w : Option (Nat × Nat)} :
    XQuietFrom tr.length ((Move.encrypt me si cl pq w).next tr) ∨
      XLastSent tr.length ((Move.encrypt me si cl pq w).next tr) :=
  xmix_bind_fix (xmix_messageEncrypt me si cl pq) (fun _ => xfix_pure _) tr

theorem xquiet_move_encryptFail (me : Participant) (si cl : Nat) :
    XQuiet (Move.encryptFail me si cl).act := by
  intro tr
  rcases encryptFail_next_cases me si cl tr with h | ⟨st, h⟩
  · change XQuietFrom tr.length ((Move.encryptFail me si cl).next tr)
    rw [h]
    exact xquietFrom_self tr
  · change XQuietFrom tr.length ((Move.encryptFail me si cl).next tr)
    rw [h]
    have h1 : XQuietFrom tr.length (tr.append (⟨32⟩ : DY.Random.ExecEntryT)) :=
      xquietFrom_append tr _ rfl rfl rfl rfl
    have h2 : XQuietFrom (tr.append (⟨32⟩ : DY.Random.ExecEntryT)).length
        ((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨cl⟩ : DY.Random.ExecEntryT)) :=
      xquietFrom_append _ _ rfl rfl rfl rfl
    have h3 : XQuietFrom ((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
        (⟨cl⟩ : DY.Random.ExecEntryT)).length
        (((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
          (⟨cl⟩ : DY.Random.ExecEntryT)).append
          (⟨(DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1⟩ : DY.Network.ExecEntryT)) :=
      xquietFrom_append _ _ rfl rfl rfl rfl
    exact xquietFrom_trans (DY.Trace.append_le _ _)
      (xquietFrom_trans (DY.Trace.append_le _ _) h1 h2) h3

end SndQuiet

theorem noSessionEffect_of_no_send {m : Move} {tr : ExecTrace} (hk : SendKind m)
    (_ha : m.LogsSessionCompletion tr) (hnosend : ∀ v ∈ m.vis tr, v.kind ≠ .send) : NoSessionEffect tr m := by
  cases m
  case encryptAbort me si =>
    exact XplSteps.xpl_noEff_of_quietFrom
      (XplSteps.xquiet_bind (xquiet_messageEncryptAbort me si)
        (fun _ => XplSteps.xquiet_of_fix (XplSteps.xfix_pure _)) tr)
  case encryptFail me si cl =>
    exact XplSteps.xpl_noEff_of_quietFrom (xquiet_move_encryptFail me si cl tr)
  case encrypt me si cl pq w =>
    rcases xmix_move_encrypt tr (me := me) (si := si) (cl := cl) (pq := pq) (w := w)
      with hq | ⟨hlt, msg, hmsg⟩
    · exact XplSteps.xpl_noEff_of_quietFrom hq
    · exfalso
      have hls : lastSent tr ((Move.encrypt me si cl pq w).next tr) = some msg := by
        unfold lastSent; simp [hlt, hmsg]
      cases w with
      | none =>
        refine hnosend ⟨.send, [msg], .whisper, none⟩ ?_ rfl
        rw [xpl_vis_eq]
        refine List.mem_append_left _ ?_
        dsimp only [xpl_ownVis, encVis]
        refine List.mem_append_right _ ?_
        simp [encSend, hls]
      | some ec =>
        rcases ec with ⟨e, c⟩
        refine hnosend ⟨.send, received tr [e, c] ++ [msg], .preKeySend, none⟩ ?_ rfl
        rw [xpl_vis_eq]
        refine List.mem_append_left _ ?_
        dsimp only [xpl_ownVis, encVis]
        refine List.mem_append_right _ ?_
        simp [encSend, hls]
  all_goals cases hk

theorem snd_ret_blockHead (pt msg : HwBytes) (mid : List MachineEvent) :
    ∀ e ∈ (((MachineEvent.pt pt :: mid) ++ [MachineEvent.send msg]).head?),
      eventKind e = .recv ∨ eventKind e = .pt := by
  intro e he
  simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at he
  subst he
  exact Or.inr rfl

theorem snd_ret_blockShape (pt msg : HwBytes) (mid : List MachineEvent)
    (hmid : ∃ coins : HwBytes, (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) :
    SendBlockShape ((MachineEvent.pt pt :: mid) ++ [MachineEvent.send msg]) where
  head := ⟨pt, rfl⟩
  tail := by
    intro e he
    obtain ⟨coins, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := hmid
    · simp only [List.cons_append, List.nil_append, List.tail_cons, List.mem_singleton] at he
      subst he; exact Or.inr rfl
    · simp only [List.cons_append, List.nil_append, List.tail_cons, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem snd_ret_noAccept (pt msg : HwBytes) (mid : List MachineEvent)
    (hmid : ∃ coins : HwBytes, (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) :
    ∀ e ∈ ((MachineEvent.pt pt :: mid) ++ [MachineEvent.send msg]), eventKind e ≠ .accept := by
  intro e he
  obtain ⟨coins, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := hmid
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> nofun
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> nofun

theorem snd_cHist_encrypt (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (p : Participant) (stateIdx cLen pqIdx : Nat) (wrap : Option (Nat × Nat))
    (hH : CHist interpretation r S g ms) :
    CHist interpretation r S g (ms ++ [.encrypt p stateIdx cLen pqIdx wrap]) := by
  rcases hH with ⟨hrk, hlow, hskip, hinv⟩
  refine ⟨?_, ?_,
    RpkCli.Skr.skippedInstallByteFresh_encrypt' interpretation S g r ms p stateIdx cLen pqIdx wrap hskip,
    TR.RecvHistStep2.recvHistInvTR_encrypt p stateIdx cLen pqIdx wrap hinv⟩
  · intro st hst
    rw [TR.runTrace_snoc] at hst
    have hdet : TR.RecvHistStep2.RecvDetermined
        (fun st : TripleRatchet.TRState => ∀ c ∈ st.recv, (gamma interpretation S g c.ratchetKey).length = 32) := by
      intro st1 st2 hrecv h1 c hc
      exact h1 c (hrecv ▸ hc)
    have hts0 := TR.RecvHistStep2.traceStatesP_runTrace_of_forall r ms hrk
    have hts1 := TR.RecvHistStep2.traceStatesP_encrypt_next hdet p stateIdx cLen pqIdx wrap hts0
    exact TR.RecvHistStep2.forall_availableStates_of_traceStatesP r hts1 st hst
  · intro st hst
    rw [TR.runTrace_snoc] at hst
    have hdet := TR.recvDetermined_recvRkNotLowP interpretation S g
    have hts0 := TR.RecvHistStep2.traceStatesP_runTrace_of_forall r ms hlow
    have hts1 := TR.RecvHistStep2.traceStatesP_encrypt_next hdet p stateIdx cLen pqIdx wrap hts0
    exact TR.RecvHistStep2.forall_availableStates_of_traceStatesP r hts1 st hst

theorem snd_cHist_step (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ms₀ pre post : List Move)
    (p : Participant) (stateIdx cLen pqIdx : Nat) (wrap : Option (Nat × Nat))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.encrypt p stateIdx cLen pqIdx wrap).next (runTraceMoves r (ms₀ ++ pre))) post)
    (hH : CHist interpretation r S g ms₀) :
    CHist interpretation r S g (ms₀ ++ (pre ++ .encrypt p stateIdx cLen pqIdx wrap :: post)) := by
  have hq1 : XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runTrace_append]
    exact XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  have hH1 := XplQuiet.quiet_cHist hq1 hH
  have hH2 := snd_cHist_encrypt interpretation r S g (ms₀ ++ pre) p stateIdx cLen pqIdx wrap hH1
  have hpost' : MovesFrom InvisibleNoEffect
      (runTraceMoves r (ms₀ ++ pre ++ [.encrypt p stateIdx cLen pqIdx wrap])) post := by
    rwa [TR.runTrace_snoc]
  have hq2 : XplQuiet.QuietExt (runTraceMoves r (ms₀ ++ pre ++ [.encrypt p stateIdx cLen pqIdx wrap]))
      (runTraceMoves r (ms₀ ++ pre ++ [.encrypt p stateIdx cLen pqIdx wrap] ++ post)) := by
    rw [runTrace_append r (ms₀ ++ pre ++ [Move.encrypt p stateIdx cLen pqIdx wrap]) post]
    exact XplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost')
  rw [show ms₀ ++ (pre ++ .encrypt p stateIdx cLen pqIdx wrap :: post) =
      ms₀ ++ pre ++ [.encrypt p stateIdx cLen pqIdx wrap] ++ post by simp]
  exact XplQuiet.quiet_cHist hq2 hH2

theorem snd_ownSaltsFrom_append (tr : ExecTrace) (ms₁ ms₂ : List Move) :
    ownSaltsFrom tr (ms₁ ++ ms₂) =
      (ownSaltsFrom tr ms₁ && ownSaltsFrom (runMoves ms₁ tr).1 ms₂) := by
  induction ms₁ generalizing tr with
  | nil => simp [ownSaltsFrom, runMoves]
  | cons m ms₁ ih =>
    simp only [List.cons_append, ownSaltsFrom, runMoves, ih, Bool.and_assoc]

theorem snd_encrypt_pqIdx {r : ProtocolSetup} {ms₀ pre post : List Move}
    {p : Participant} {stateIdx cLen pqIdx : Nat} {wrap : Option (Nat × Nat)}
    (h : ownSaltsFrom (setupTrace r) (ms₀ ++ (pre ++ .encrypt p stateIdx cLen pqIdx wrap :: post)) = true) :
    pqIdx = (runTraceMoves r (ms₀ ++ pre)).length + 2 := by
  rw [← List.append_assoc, snd_ownSaltsFrom_append] at h
  have h2 := (Bool.and_eq_true _ _).mp h |>.2
  simp only [ownSaltsFrom, Bool.and_eq_true] at h2
  exact beq_iff_eq.mp h2.1

def wrapVisEntry (tr : ExecTrace) (wrap : Option (Nat × Nat)) (v : VisEntry) : VisEntry :=
  match v.kind, wrap with
  | .send, some (e, c) => ⟨.send, received tr [e, c] ++ v.terms, .preKeySend, none⟩
  | _, _ => v

theorem visOf_encrypt_wrap_eq (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (wrap : Option (Nat × Nat)) (tr : ExecTrace) :
    (Move.encrypt me stateIdx coinsLen pqIdx wrap).vis tr =
      ((Move.encrypt me stateIdx coinsLen pqIdx none).vis tr).map (wrapVisEntry tr wrap) := by
  have hnext : (Move.encrypt me stateIdx coinsLen pqIdx wrap).next tr =
      (Move.encrypt me stateIdx coinsLen pqIdx none).next tr := rfl
  rw [xpl_vis_eq, xpl_vis_eq]
  dsimp only [xpl_ownVis, encVis]
  rw [hnext]
  set tr' := (Move.encrypt me stateIdx coinsLen pqIdx none).next tr
  simp only [↓reduceIte, List.map_append]
  have henc : ∀ r, (encDraws r).map (wrapVisEntry tr wrap) = encDraws r := by
    intro r
    match r with
    | [] => rfl
    | [(_, _)] => rfl
    | (_, _) :: (_, cl) :: _ =>
      simp [encDraws, wrapVisEntry, rngEntry]
  have hsend : (encSend tr tr' none).map (wrapVisEntry tr wrap) = encSend tr tr' wrap := by
    unfold encSend wrapVisEntry
    cases wrap <;> cases lastSent tr tr' <;> rfl
  have hexp : ∀ l : List VisEntry, (∀ v ∈ l, v.kind = .leak) → l.map (wrapVisEntry tr wrap) = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons v tl ih =>
      have hv := hl v List.mem_cons_self
      simp [wrapVisEntry, hv, ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))]
  rw [henc, hsend, hexp _ (fun _ hv => xpl_exposures_kind hv)]

theorem snd_encrypt_next_eq_self_of_not {p : Participant} {stateIdx cLen pqIdx : Nat}
    {wrap : Option (Nat × Nat)} {tr : ExecTrace}
    (h : ∀ st,
      ((PersistentLocalState.getLocalState p stateIdx : Traceful TripleRatchet.TRState).run tr).1 = some st →
        st.ns = TripleRatchet.u32Max) :
    (Move.encrypt p stateIdx cLen pqIdx wrap).next tr = tr := by
  change ((TripleRatchet.messageEncrypt p stateIdx cLen pqIdx >>= fun _ => pure ()).run tr).2.val = tr
  unfold TripleRatchet.messageEncrypt
  rw [Traceful.run_bind, Traceful.run_bind]
  rcases hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TripleRatchet.TRState).run tr)
    with ⟨o, t, ht⟩
  have ht_eq : t = tr := by
    have h2 := TR.RecvDec.getLocalState_snd p stateIdx tr
    rw [hst] at h2
    exact h2
  subst ht_eq
  cases o with
  | none => rfl
  | some st =>
    have hns := h st (by rw [hst])
    dsimp only
    have hg : (_root_.guard (st.ns ≠ TripleRatchet.u32Max) : Traceful Unit) = failure := by
      simp [_root_.guard, hns]
    rw [hg]
    simp only [Traceful.run_bind, Traceful.run_failure]

unseal DY.Bytes in
instance subFunction_gRandom_whisper (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

theorem snd_encrypt_vis_match {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {p : Participant} {stateIdx cLen : Nat}
    {wrap : Option (Nat × Nat)} {pt msg coins : HwBytes} {mid : List MachineEvent}
    (hm : List.Forall₂ (EventMatchesEntry interpretation r S g)
      ((.pt pt :: mid) ++ [.send msg])
      ((Move.encrypt p stateIdx cLen (tr.length + 2) wrap).vis tr))
    (hmid : (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) :
    (∃ st,
      ((PersistentLocalState.getLocalState p stateIdx : Traceful TripleRatchet.TRState).run tr).1 = some st ∧
      st.ns ≠ TripleRatchet.u32Max) ∧
    gamma interpretation S g (randTerm tr.length 32) = pt ∧
    gamma interpretation S g (randTerm (tr.length + 1) cLen) = coins := by
  have hex : ∃ st,
      ((PersistentLocalState.getLocalState p stateIdx : Traceful TripleRatchet.TRState).run tr).1 = some st ∧
      st.ns ≠ TripleRatchet.u32Max := by
    by_contra hnot
    have hnext := snd_encrypt_next_eq_self_of_not (p := p) (stateIdx := stateIdx)
      (cLen := cLen) (pqIdx := tr.length + 2) (wrap := wrap) (tr := tr)
      (fun st hst => Decidable.of_not_not fun hns => hnot ⟨st, hst, hns⟩)
    rw [xpl_vis_eq] at hm
    dsimp only [xpl_ownVis, encVis] at hm
    rw [hnext] at hm
    have hni : newIndices tr tr = [] := by unfold newIndices; simp
    have hnr : newRandoms tr tr = [] := by unfold newRandoms; rw [hni]; rfl
    have hexp : exposures tr tr = [] := by unfold exposures; rw [hni]; rfl
    have hls : lastSent tr tr = none := by unfold lastSent; simp
    have hsnd : encSend tr tr wrap = [] := by unfold encSend; rw [hls]
    rw [hnr, hexp, hsnd] at hm
    simp [encDraws] at hm
  obtain ⟨st, hst, hns⟩ := hex
  refine ⟨⟨st, hst, hns⟩, ?_⟩
  rw [visOf_encrypt_wrap_eq] at hm
  by_cases hc0 : cLen = 0
  · subst hc0
    rw [visOf_encrypt_zero hst hns] at hm
    rcases hmid with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
    · simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil,
        List.forall₂_cons] at hm
      have hpt_eq : [gamma interpretation S g (randTerm tr.length 32)] = [pt] := hm.1.2
      have h0 : gamma interpretation S g (randTerm (tr.length + 1) 0) = [] := by
        unfold gamma gamma' randTerm
        rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]
        rfl
      exact ⟨List.head_eq_of_cons_eq hpt_eq, h0⟩
    · have hlen := hm.length_eq
      simp at hlen
  · rw [visOf_encrypt_ne_zero hst hns hc0] at hm
    rcases hmid with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
    · have hlen := hm.length_eq
      simp at hlen
    · simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil,
        List.forall₂_cons] at hm
      have hpt_eq : [gamma interpretation S g (randTerm tr.length 32)] = [pt] := hm.1.2
      have hcoins_eq : [gamma interpretation S g (randTerm (tr.length + 1) cLen)] = [coins] := hm.2.1.2
      exact ⟨List.head_eq_of_cons_eq hpt_eq, List.head_eq_of_cons_eq hcoins_eq⟩

end Symbolic.Swarm.CREF.CliPure.SndPure
