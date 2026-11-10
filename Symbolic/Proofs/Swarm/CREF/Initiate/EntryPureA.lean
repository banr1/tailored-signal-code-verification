/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Initiate.TransferPure
public import Symbolic.Proofs.Swarm.CREF.Initiate.PostBridgePure
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.Random
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import Symbolic.Proofs.Swarm.CREF.OooPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PureSessionBounds
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# `session_initiate` Frame and History Invariants

Proves `b2NsInv` and `b2Frame` preservation across `aliceStart`, `COooAll` updates on Alice's new
session record, and `NoSessionEffect` for `aliceStart` moves that do not log `AliceDone`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.IniPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.CliPure.IniSndPure
cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.TripleRatchet (SessionInfo TRState TREvent)
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Symbolic.Swarm.COMPOSED

theorem b2_quietPost {r : ProtocolSetup} {ms₀ pre post : List Move} {m : Move}
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post) :
    XplQuiet.QuietExt (runTraceMoves r (ms₀ ++ pre ++ [m])) (runTraceMoves r (ms₀ ++ (pre ++ m :: post))) := by
  rw [show ms₀ ++ (pre ++ m :: post) = ms₀ ++ pre ++ [m] ++ post by simp,
    TR.runTrace_append (ms₁ := ms₀ ++ pre ++ [m]), TR.runTrace_snoc, TR.runTrace_append]
  exact XplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost)

theorem b2_quietPre {r : ProtocolSetup} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre) :
    XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
  rw [TR.runTrace_append]
  exact XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)

def b2NsInv (n : Nat) (tr : ExecTrace) : Prop :=
  ∀ (p : Participant) (stateIdx : Nat) (st : TRState),
    ((DY.PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st →
    st.ns.toNat ≤ n

theorem b2NsInv_iff (n : Nat) (tr : ExecTrace) :
    b2NsInv n tr ↔ ∀ (i : Nat) (e : CompTrace.TRStEntry),
      (tr.at? i : Option CompTrace.TRStEntry) = some e → e.st.state.ns.toNat ≤ n := by
  constructor
  · intro h i ⟨⟨p, st⟩⟩ he
    refine h p i st ?_
    rw [CompTrace.getLocalState_tr_fst, he]; simp
  · intro h p i st hget
    rw [CompTrace.getLocalState_tr_fst] at hget
    rcases he : (tr.at? i : Option CompTrace.TRStEntry) with _ | ⟨⟨q, st'⟩⟩
    · rw [he] at hget; cases hget
    · rw [he] at hget; dsimp only at hget; split_ifs at hget; cases hget; exact h i _ he

theorem b2NsInv_append {E : Type} [DY.ExecTraceTypes.Has E] {n : Nat} {tr : ExecTrace} {x : E}
    (hx : ∀ e : CompTrace.TRStEntry,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
        Option CompTrace.TRStEntry) = some e → e.st.state.ns.toNat ≤ n)
    (h : b2NsInv n tr) : b2NsInv n (tr.append x) := by
  rw [b2NsInv_iff] at h ⊢
  intro i e he
  rcases CompTrace.at?_append_cases he with ⟨_, he'⟩ | ⟨_, hp⟩
  · exact h i e he'
  · exact hx e hp

theorem b2NsInv_append_other {E : Type} [DY.ExecTraceTypes.Has E] {n : Nat} {tr : ExecTrace} {x : E}
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option CompTrace.TRStEntry) = none)
    (h : b2NsInv n tr) : b2NsInv n (tr.append x) :=
  b2NsInv_append (fun _ hp => by rw [hnone] at hp; cases hp) h

theorem b2NsInv_quiet {n : Nat} {tr tr' : ExecTrace} (h : XplQuiet.QuietExt tr tr')
    (hI : b2NsInv n tr) : b2NsInv n tr' := by
  intro p i st hget; rw [XplQuiet.quiet_getLocalState h] at hget; exact hI p i st hget

theorem b2_store {n : Nat} (p : Participant) (st : TRState) (hst : st.ns.toNat ≤ n) :
    CompTrace.Preserves (b2NsInv n) (DY.PersistentLocalState.storeLocalState p st) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact b2NsInv_append (fun _ hp => by rw [CompTrace.proj_inj_eq] at hp; cases hp; exact hst) h

def b2BobEv (b : Participant) : TREvent → Prop
  | .SkippedKeyUsed _ _ => False
  | .MessageKey s _ _ _ _ _ _ => s.me = b
  | .SkippedKeyStored s _ _ _ _ _ => s.me = b
  | _ => True

def b2Frame (b : Participant) (tr₀ tr : ExecTrace) : Prop :=
  tr₀ ≤ tr ∧ ∀ i, tr₀.length ≤ i →
    (∀ e : CompTrace.TRStEntry, (tr.at? i : Option CompTrace.TRStEntry) = some e →
      e.st.participant = b) ∧
    (∀ e : CompTrace.TREntry, (tr.at? i : Option CompTrace.TREntry) = some e → b2BobEv b e.ev)

theorem b2Frame_refl (b : Participant) (tr : ExecTrace) : b2Frame b tr tr := by
  refine ⟨Trace.le_refl tr, fun _ hi => ⟨fun _ he => ?_, fun _ he => ?_⟩⟩ <;>
    (rw [XplQuiet.at?_none_of_ge hi] at he; cases he)

theorem b2Frame_append {E : Type} [DY.ExecTraceTypes.Has E] {b : Participant}
    {tr₀ tr : ExecTrace} {x : E}
    (hst : ∀ e : CompTrace.TRStEntry,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
        Option CompTrace.TRStEntry) = some e → e.st.participant = b)
    (hev : ∀ e : CompTrace.TREntry,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
        Option CompTrace.TREntry) = some e → b2BobEv b e.ev)
    (h : b2Frame b tr₀ tr) : b2Frame b tr₀ (tr.append x) := by
  refine ⟨Trace.le_trans _ _ _ h.1 (Trace.append_le tr x), fun i hi => ⟨fun e he => ?_, fun e he => ?_⟩⟩
  · rcases CompTrace.at?_append_cases he with ⟨_, he'⟩ | ⟨_, hp⟩
    · exact (h.2 i hi).1 e he'
    · exact hst e hp
  · rcases CompTrace.at?_append_cases he with ⟨_, he'⟩ | ⟨_, hp⟩
    · exact (h.2 i hi).2 e he'
    · exact hev e hp

theorem b2Frame_append_other {E : Type} [DY.ExecTraceTypes.Has E] {b : Participant}
    {tr₀ tr : ExecTrace} {x : E}
    (h1 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option CompTrace.TRStEntry) = none)
    (h2 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option CompTrace.TREntry) = none)
    (h : b2Frame b tr₀ tr) : b2Frame b tr₀ (tr.append x) :=
  b2Frame_append (fun _ hp => by rw [h1] at hp; cases hp)
    (fun _ hp => by rw [h2] at hp; cases hp) h

theorem b2_at?_lt {EntryT : Type} [DY.TraceEntryHas EntryT ExecTrace.Entry] {tr₀ tr : ExecTrace}
    (hle : tr₀ ≤ tr) {j : Nat} (hj : j < tr₀.length) :
    (tr.at? j : Option EntryT) = tr₀.at? j := by
  have hj' : j < tr.length := Nat.lt_of_lt_of_le hj (Trace.length_le tr₀ tr hle)
  simp only [Trace.at?, hj, hj', dite_true, Trace.at_le tr₀ tr j hj hle]

theorem b2Frame_getLocalState {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    {p : Participant} {i : Nat} {st : TRState}
    (hget : ((DY.PersistentLocalState.getLocalState p i : Traceful TRState).run tr₀).1 = some st) :
    ((DY.PersistentLocalState.getLocalState p i : Traceful TRState).run tr).1 = some st := by
  rw [CompTrace.getLocalState_tr_fst] at hget ⊢
  rcases he : (tr₀.at? i : Option CompTrace.TRStEntry) with _ | e
  · rw [he] at hget; cases hget
  · rw [he] at hget; rw [CompTrace.at?_le_some h.1 he]; exact hget

theorem b2Frame_isCurrentSnapshot {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    {p : Participant} (hp : p ≠ b) {i : Nat} {st : TRState}
    (hget : ((DY.PersistentLocalState.getLocalState p i : Traceful TRState).run tr₀).1 = some st)
    (hcur : TripleRatchet.isCurrentSnapshot tr₀ i = true) :
    TripleRatchet.isCurrentSnapshot tr i = true := by
  rw [CompTrace.getLocalState_tr_fst] at hget
  rcases he : (tr₀.at? i : Option CompTrace.TRStEntry) with _ | ⟨⟨q, st'⟩⟩
  · rw [he] at hget; cases hget
  rw [he] at hget
  have hq : q = p := by dsimp only at hget; split_ifs at hget with hq; exact hq
  have hlt : i < tr₀.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := CompTrace.TRStEntry) tr₀ i
    rw [he] at this; exact this
  have hlen := Trace.length_le tr₀ tr h.1
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
  rw [CompTrace.at?_le_some h.1 he]; rw [he] at hcur; dsimp only at hcur ⊢
  rw [show tr.length - (i + 1) = (tr₀.length - (i + 1)) + (tr.length - tr₀.length) by omega,
    ← List.range'_append_1, List.all_append, Bool.and_eq_true]
  simp only [show i + 1 + (tr₀.length - (i + 1)) = tr₀.length by omega]
  refine ⟨Eq.trans (XplQuiet.q_all_congr_mem fun j hj => ?_) hcur, ?_⟩
  · rw [List.mem_range'_1] at hj; rw [b2_at?_lt h.1 (by omega : j < tr₀.length)]
  · rw [List.all_eq_true]; intro j hj; rw [List.mem_range'_1] at hj; try dsimp only
    rcases hj' : (tr.at? j : Option CompTrace.TRStEntry) with _ | e'
    · rfl
    · have hb := (h.2 j (by omega)).1 e' hj'
      simp only [hb, Bool.or_eq_true, bne_iff_ne, ne_eq]
      exact Or.inl fun h' => hp (h'.trans hq).symm

theorem b2Frame_eventLoggedAt {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    {ev : TREvent} {i : Nat} (hl : tr₀.EventLoggedAt ev i) : tr.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hl ⊢
  exact CompTrace.at?_le_some h.1 hl

theorem b2Frame_someEventOnTraceB {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    (P : TREvent → Bool) (hP : ∀ ev, b2BobEv b ev → P ev = false)
    (h0 : (TripleRatchet.anyEventOnTrace TripleRatchet.TREvent) tr₀ P = false) :
    (TripleRatchet.anyEventOnTrace TripleRatchet.TREvent) tr P = false := by
  simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h0 ⊢
  rw [List.any_eq_false] at h0 ⊢
  intro j hj hfj; rw [List.mem_range] at hj; try dsimp only at hfj
  by_cases hlt : j < tr₀.length
  · rw [b2_at?_lt h.1 hlt] at hfj; exact h0 j (List.mem_range.mpr hlt) hfj
  · rcases he : (tr.at? j : Option CompTrace.TREntry) with _ | e
    · rw [he] at hfj; dsimp only at hfj; cases hfj
    · rw [he] at hfj; dsimp only at hfj; rw [hP e.ev ((h.2 j (by omega)).2 e he)] at hfj; cases hfj

theorem b2Frame_skippedKeyUsedB {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    {k : Nat} (hsu : (!TripleRatchet.skippedKeyUsedB tr₀ k) = true) :
    (!TripleRatchet.skippedKeyUsedB tr k) = true := by
  have h0 : TripleRatchet.skippedKeyUsedB tr₀ k = false := by simpa using hsu
  have h1 : TripleRatchet.skippedKeyUsedB tr k = false :=
    b2Frame_someEventOnTraceB h _ (fun ev hev => by cases ev <;> first | rfl | exact False.elim hev) h0
  simp [h1]

theorem b2Frame_receiverKeyUsedB {b : Participant} {tr₀ tr : ExecTrace} (h : b2Frame b tr₀ tr)
    {p : Participant} (hp : p ≠ b) {st : TRState} {seed : DY.Bytes} {n : UInt32} {rIdx : Nat}
    (hru : (!TripleRatchet.receiverKeyUsedB tr₀ (st.sessionInfo p) seed n rIdx) = true) :
    (!TripleRatchet.receiverKeyUsedB tr (st.sessionInfo p) seed n rIdx) = true := by
  have h0 : TripleRatchet.receiverKeyUsedB tr₀ (st.sessionInfo p) seed n rIdx = false := by simpa using hru
  have h1 : TripleRatchet.receiverKeyUsedB tr (st.sessionInfo p) seed n rIdx = false := by
    refine b2Frame_someEventOnTraceB h _ (fun ev hev => ?_) h0
    cases ev
    case MessageKey s' dir _ _ _ _ _ =>
      cases dir
      · rfl
      · exact decide_eq_false fun hc => hp ((congrArg SessionInfo.me hc.1).symm.trans hev)
    all_goals rfl
  simp [h1]

theorem b2Frame_trRecordStateInv {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {Z : TR.PureTRSlots} {g : Ghost} {ms ms' : List Move} {records : Participant → Option HwBytes}
    {b : Participant} (h : b2Frame b (runTraceMoves r ms) (runTraceMoves r ms'))
    (hrec : ∀ q bs, records q = some bs → q ≠ b)
    (hrsi : TR.PureTRRecordStateInv interpretation r S Z g ms records) :
    TR.PureTRRecordStateInv interpretation r S Z g ms' records := by
  intro q bs hqb
  have hqb' := hrec q bs hqb
  obtain ⟨hq_mem, rec, st, stateIdx, hb, hget, hcur, hrel, hsk, hcanon, hks, hnd⟩ := hrsi q bs hqb
  refine ⟨hq_mem, rec, st, stateIdx, hb, b2Frame_getLocalState h hget,
    b2Frame_isCurrentSnapshot h hqb' hget hcur, hrel, ?_, hcanon, hks, hnd⟩
  intro c hc k hk
  obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsu, hru, hgam, hsrk, hfind⟩ := hsk c hc k hk
  exact ⟨pk, rIdx, srcIdx, skIdx, seed, b2Frame_eventLoggedAt h hlog,
    b2Frame_skippedKeyUsedB h hsu, b2Frame_receiverKeyUsedB h hqb' hru, hgam, hsrk, hfind⟩

theorem ini_no_accept_in_blk (bundle : HwBytes) (ds : List HwBytes) :
    ∀ e ∈ (MachineEvent.recv bundle :: ds.map MachineEvent.rng), eventKind e ≠ .accept := by
  intro e hmem
  simp only [List.mem_cons, List.mem_map] at hmem
  rcases hmem with rfl | ⟨_, _, rfl⟩ <;> simp [eventKind]

theorem ini_sentBodies_nil (bundle : HwBytes) (ds : List HwBytes) :
    TR.sentBodies (MachineEvent.recv bundle :: ds.map MachineEvent.rng) = [] := by
  simp only [TR.sentBodies, List.filterMap_cons, List.filterMap_map]
  induction ds <;> simp_all

theorem ini_sendsFit (bundle : HwBytes) (ds : List HwBytes) :
    TR.SendsFit (MachineEvent.recv bundle :: ds.map MachineEvent.rng) := by
  intro m hm
  simp only [List.mem_cons, List.mem_map, reduceCtorEq, false_or] at hm
  rcases hm with ⟨_, _, h⟩
  cases h

theorem ini_prefix_reachable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {acc : List MachineEvent} :
    ∀ g ms, MatchedPrefix interpretation r S who g ms acc →
      ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable reachability :=
  fun _ _ h => matchedPrefix_prefix_reachable h

theorem pqStateOf_of_pureRecordCanonical_Q {Q : HwBytes → Prop} {bs : HwBytes}
    {s : Session HwBytes} (hc : TR.Pure.slots_RecordCanonical_Q Q bs s) :
    pqStateOf bs = s.state.pqRatchetState := by
  obtain ⟨henc_eq, _, _, _, hchains_sc, halice_lt, _, hpq_lt, hsess_lt⟩ := hc
  have hsess_lt' : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 62 := hsess_lt
  have hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63 := by
    intro rc hrc mk hmk; have := (hchains_sc rc hrc).2 mk hmk; omega
  have hrc_len : ∀ rc ∈ s.state.receiverChains,
      (CryptoVerification.E2E.Record.encReceiverChain rc).length < 2 ^ 64 := by
    intro rc hrc
    have h1 := TR.Pure.lenField_encReceiverChain_length_le rc (hchains_sc rc hrc).1 (hchains_sc rc hrc).2
    unfold CryptoVerification.E2E.Record.lenField at h1
    simp only [List.length_append] at h1; omega
  have hrec := recordBytes_sessionToRecordRecPending_eq_encodeRecord s
    (by omega) (by omega) hseeds hrc_len (by omega)
  rw [henc_eq, ← hrec, pqStateOf_recordBytes, sessionToRecordRecPending_pqRatchetState]

theorem ini_ok_spqrOooBounded (interpretation : ExternInterpretation)
    (r : ProtocolSetup) (bundle : HwBytes) (ds : List HwBytes) (recState : HwBytes)
    (hV1 : AliceInitiatedV1PostPure interpretation r bundle ds recState) :
    SpqrOooBounded (pqStateOf recState) := by
  let g0 : Ghost := ⟨fun _ _ => [], fun _ => []⟩
  let S0 : OpaqueSymbolSemantics := compSemOf interpretation r
  let agr0 := aliceLitAgreement r bundle ds
  let pqr0 := gamma interpretation S0 g0 agr0.2.pqr
  obtain ⟨ourIdentity, theirIdentity, theirRatchetKey, baseKey, rk1, ck0,
    sendingKeyPair, ck1, opkId?, spkId, kyberPreKeyId, remoteRegId,
    hcanon, _⟩ := hV1
  rw [pqStateOf_of_pureRecordCanonical_Q hcanon]
  have hpqr_len : pqr0.length = 32 :=
    (length_gamma_pqxdhKdf interpretation S0 g0 _).2.2
  exact (spqrOooBounded_spqrInitOf_a2b interpretation pqr0 (by omega)).1

theorem ini_ok_cOOO (interpretation : ExternInterpretation) (r : ProtocolSetup)
    {records : Participant → Option HwBytes}
    (bundle : HwBytes) (ds : List HwBytes) (recState : HwBytes)
    (hV1 : AliceInitiatedV1PostPure interpretation r bundle ds recState)
    (hooo : COooAll records) :
    COooAll (fun q => if q = r.alice then some recState else records q) :=
  cOOO_step_update hooo (ini_ok_spqrOooBounded interpretation r bundle ds recState hV1)

def LogsAliceDone (tr : ExecTrace) (m : Move) : Prop :=
  (eventIdx isAliceDone tr (m.next tr)).isSome

theorem noSessionEffect_aliceStart_of_not_logsAliceDone {tr : ExecTrace}
    {a b : Participant} {idStateIdx regIdxB : Nat} {bh : PQXDH.BundleHandles} {shown : Nat}
    (hno : ¬LogsAliceDone tr (.aliceStart a b idStateIdx regIdxB bh shown)) :
    NoSessionEffect tr (.aliceStart a b idStateIdx regIdxB bh shown) := by
  rcases XplSteps.xmix_move_aliceStart tr (a := a) (b := b) (i := idStateIdx) (r := regIdxB)
    (h := bh) (shown := shown) with hq | hq
  · exact XplSteps.xpl_noEff_of_quietFrom hq
  · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (XplSteps.xpl_eventIdx_ne_none hq)
    exact False.elim (hno (by simp [LogsAliceDone, hj]))

theorem ini_invisible_nil :
    ∀ (δ : List Move) (tr : ExecTrace),
      MovesFrom InvisibleNoEffect tr δ → (runMoves δ tr).2 = []
  | [], _, _ => rfl
  | m :: δ, tr, ⟨⟨hv, _⟩, hδ⟩ => by
    simp only [runMoves, hv, List.nil_append]
    exact ini_invisible_nil δ (m.next tr) hδ

theorem b2NsInv_aliceStartTrOfOut {n : Nat} {tr : ExecTrace} (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) (h : b2NsInv n tr) :
    b2NsInv n (aliceStartTrOfOut tr a b o) := by
  unfold aliceStartTrOfOut
  refine b2NsInv_append
    (fun _ hp => by rw [CompTrace.proj_inj_eq] at hp; cases hp; simp [aliceStartState]) ?_
  refine b2NsInv_append_other rfl ?_
  refine b2NsInv_append_other rfl ?_
  refine b2NsInv_append_other rfl ?_
  refine b2NsInv_append_other rfl ?_
  refine b2NsInv_append_other rfl ?_
  refine b2NsInv_append_other rfl ?_
  refine b2NsInv_append_other rfl ?_
  exact b2NsInv_append_other rfl h

theorem b2NsInv_next_aliceStart {n : Nat} {tr : ExecTrace}
    (a b : DY.Participant) (idStateIdx regIdxB : Nat)
    (bh : PQXDH.BundleHandles) (shown : Nat) (h : b2NsInv n tr) :
    b2NsInv n ((Move.aliceStart a b idStateIdx regIdxB bh shown).next tr) := by
  rcases aliceStart_next_cases a b idStateIdx regIdxB bh shown tr with h_id | h_rnd |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_ok⟩
  · rw [h_id]; exact h
  · rw [h_rnd]; exact b2NsInv_append_other rfl h
  · rw [h_ok]; exact b2NsInv_aliceStartTrOfOut a b _ h

theorem b2Frame_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    b2Frame a tr (aliceStartTrOfOut tr a b o) := by
  unfold aliceStartTrOfOut
  refine b2Frame_append
    (fun _ hp => by rw [CompTrace.proj_inj_eq] at hp; cases hp; rfl)
    (fun _ hp => by cases hp) ?_
  refine b2Frame_append_other rfl rfl ?_
  refine b2Frame_append (fun _ hp => by cases hp)
    (fun _ hp => by rw [CompTrace.proj_inj_eq] at hp; cases hp; trivial) ?_
  refine b2Frame_append_other rfl rfl ?_
  refine b2Frame_append_other rfl rfl ?_
  refine b2Frame_append_other rfl rfl ?_
  refine b2Frame_append_other rfl rfl ?_
  refine b2Frame_append_other rfl rfl ?_
  exact b2Frame_append_other rfl rfl (b2Frame_refl a tr)

theorem b2Frame_next_aliceStart (tr : ExecTrace) (a b : DY.Participant)
    (idStateIdx regIdxB : Nat) (bh : PQXDH.BundleHandles) (shown : Nat) :
    b2Frame a tr ((Move.aliceStart a b idStateIdx regIdxB bh shown).next tr) := by
  rcases aliceStart_next_cases a b idStateIdx regIdxB bh shown tr with h_id | h_rnd |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_ok⟩
  · rw [h_id]; exact b2Frame_refl a tr
  · rw [h_rnd]; exact b2Frame_append_other rfl rfl (b2Frame_refl a tr)
  · rw [h_ok]; exact b2Frame_aliceStartTrOfOut tr a b _

theorem b2Frame_pureCRecRel_alice {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms ms' : List Move} {p : Participant} {bs : HwBytes}
    (h : b2Frame r.alice (runTraceMoves r ms) (runTraceMoves r ms')) (hp : p ≠ r.alice)
    (hc : PureCRecRel interpretation r S g ms p bs) :
    PureCRecRel interpretation r S g ms' p bs := by
  rcases hc with hc | ⟨hpa, _⟩
  · refine Or.inl (b2Frame_trRecordStateInv h (fun q _ hq => ?_) hc)
    by_cases hqp : q = p
    · subst hqp; exact hp
    · simp [hqp] at hq
  · exact absurd hpa hp

private def rpkT_bdKey (tr : ExecTrace) (i : Nat) : Option DY.Bytes :=
  match tr.getEventAt PQXDH.PQXDHEvent i with
  | some (.BobDone _ _ _ _ _ _ _ ek _ _) => some ek | _ => none

private theorem rpkT_bobDoneBaseKeys_append {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace)
    (x : E) : bobDoneBaseKeys (tr.append x) =
      bobDoneBaseKeys tr ++ (rpkT_bdKey (tr.append x) tr.length).toList := by
  unfold bobDoneBaseKeys
  have hlen : (tr.append x).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [hlen]
  change (List.range (tr.length + 1)).filterMap (rpkT_bdKey (tr.append x)) =
    (List.range tr.length).filterMap (rpkT_bdKey tr) ++ _
  rw [List.range_succ, List.filterMap_append]; congr 1
  refine List.filterMap_congr fun i hi => ?_
  (unfold rpkT_bdKey; simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]); rw [CompTrace.at?_append_of_lt tr x (List.mem_range.mp hi)]

private theorem rpkT_bobDoneBaseKeys_append_other {E : Type} [DY.ExecTraceTypes.Has E]
    (tr : ExecTrace) (x : E) (hx : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none) :
    bobDoneBaseKeys (tr.append x) = bobDoneBaseKeys tr := by
  have hhere : ((tr.append x).at? tr.length :
      Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by
    cases h : ((tr.append x).at? tr.length : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) with
    | none => rfl
    | some _ => exact False.elim (CompTrace.at?_disjoint hx (CompTrace.at?_append_here tr x) h)
  rw [rpkT_bobDoneBaseKeys_append, show rpkT_bdKey (tr.append x) tr.length = none by
    (unfold rpkT_bdKey; simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]); rw [hhere], Option.toList_none, List.append_nil]

private theorem rpkT_bobDoneBaseKeys_append_pq (tr : ExecTrace) (ev : PQXDH.PQXDHEvent) :
    bobDoneBaseKeys (tr.append (TR.EvE ev)) = bobDoneBaseKeys tr ++
      (match ev with | .BobDone _ _ _ _ _ _ _ ek _ _ => [ek] | _ => []) := by
  rw [rpkT_bobDoneBaseKeys_append]; congr 1
  (unfold rpkT_bdKey; simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]); rw [CompTrace.at?_append_here tr (TR.EvE ev)]; cases ev <;> rfl

theorem bobDoneBaseKeys_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    bobDoneBaseKeys (aliceStartTrOfOut tr a b o) = bobDoneBaseKeys tr := by
  unfold aliceStartTrOfOut
  dsimp only
  rw [rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_pq, List.append_nil,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl]

theorem bobDoneBaseKeys_next_aliceStart (tr : ExecTrace) (a b : DY.Participant)
    (idStateIdx regIdxB : Nat) (bh : PQXDH.BundleHandles) (shown : Nat) :
    bobDoneBaseKeys ((Move.aliceStart a b idStateIdx regIdxB bh shown).next tr) =
      bobDoneBaseKeys tr := by
  rcases aliceStart_next_cases a b idStateIdx regIdxB bh shown tr with h_id | h_rnd |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_ok⟩
  · rw [h_id]
  · rw [h_rnd]; exact rpkT_bobDoneBaseKeys_append_other _ _ rfl
  · rw [h_ok]; exact bobDoneBaseKeys_aliceStartTrOfOut tr a b _

theorem traceStatesP_aliceStartTrOfOut {P : TripleRatchet.TRState → Prop}
    {tr : ExecTrace} (a b : DY.Participant) (o : PQXDH.AliceHandshakeOut)
    (h_new : P (aliceStartState tr b o))
    (htr : TR.RecvHistStep2.TraceStatesP P tr) :
    TR.RecvHistStep2.TraceStatesP P (aliceStartTrOfOut tr a b o) := by
  unfold aliceStartTrOfOut
  dsimp only
  refine TR.RecvHistStep2.traceStatesP_append ?_ ?_
  · intro e he
    rw [CompTrace.proj_inj_eq] at he
    injection he with he
    subst he
    exact h_new
  · refine TR.RecvHistStep2.traceStatesP_append (fun _ h => by cases h) ?_
    refine TR.RecvHistStep2.traceStatesP_append (fun _ h => by cases h) ?_
    refine TR.RecvHistStep2.traceStatesP_append (fun _ h => by cases h) ?_
    refine TR.RecvHistStep2.traceStatesP_append (fun _ h => by cases h) ?_
    refine TR.RecvHistStep2.traceStatesP_append (fun _ h => by cases h) ?_
    refine TR.RecvHistStep2.traceStatesP_append (fun _ h => by cases h) ?_
    refine TR.RecvHistStep2.traceStatesP_append (fun _ h => by cases h) ?_
    exact TR.RecvHistStep2.traceStatesP_append (fun _ h => by cases h) htr

theorem availableStates_aliceStartTrOfOut_forall {P : TripleRatchet.TRState → Prop}
    {r : ProtocolSetup} {tr : ExecTrace} (a b : DY.Participant) (o : PQXDH.AliceHandshakeOut)
    (h_new : P (aliceStartState tr b o))
    (htr : TR.RecvHistStep2.TraceStatesP P tr) :
    ∀ st ∈ availableStates r (aliceStartTrOfOut tr a b o), P st :=
    TR.RecvHistStep2.forall_availableStates_of_traceStatesP r
      (traceStatesP_aliceStartTrOfOut a b o h_new htr)

end Symbolic.Swarm.CREF.CliPure.IniPure
