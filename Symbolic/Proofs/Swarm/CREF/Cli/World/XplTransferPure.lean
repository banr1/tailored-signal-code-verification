/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.World.CallCountPure
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.PersistentGlobalState
import DY.Actions.PersistentLocalState
import DY.Actions.ProtocolEvent
import DY.Actions.Network
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyFrame
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Quiet Trace Transfer for `PureCRel` and `CoinSplit` Combinators

Transfers `PureCRel` across call-boundary blocks whose explanations satisfy `NoSessionEffect` and
emit no `.send` events, and proves `CoinSplit` combinators for CLI entry and leak event lists.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (TREvent TRState)
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed.Refinement.Cli (CliCall CoinSplit cliEntryEvents)

namespace PureXplQuiet

open TripleRatchet (TREvent TRState)
open PQXDH (PQXDHEvent)

abbrev QStE := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev QTrE := ProtocolEvent.ExecEntryT TREvent
abbrev QPqE := ProtocolEvent.ExecEntryT PQXDHEvent
abbrev QCE := ProtocolEvent.ExecEntryT ComposedEvent

/-- `tr'` extends `tr` by entries that are no state, PQXDH, TR or composed event. -/
def QuietExt (tr tr' : ExecTrace) : Prop :=
  tr ≤ tr' ∧ ∀ i, tr.length ≤ i → i < tr'.length →
    (tr'.at? i : Option QStE) = none ∧ Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.NonSessionPQAt tr' i ∧
      (tr'.at? i : Option QTrE) = none ∧ (tr'.at? i : Option QCE) = none

theorem quietExt_len {tr tr' : ExecTrace} (h : QuietExt tr tr') : tr.length ≤ tr'.length :=
  Trace.length_le tr tr' h.1

theorem quietExt_at?_lt {EntryT : Type} [TraceEntryHas EntryT ExecTrace.Entry] {tr tr' : ExecTrace}
    (h : QuietExt tr tr') {j : Nat} (hj : j < tr.length) :
    (tr'.at? j : Option EntryT) = tr.at? j := by
  have hj' : j < tr'.length := Nat.lt_of_lt_of_le hj (quietExt_len h)
  simp only [Trace.at?, hj, hj', dite_true, Trace.at_le tr tr' j hj h.1]

theorem at?_none_of_ge {EntryT : Type} [TraceEntryHas EntryT ExecTrace.Entry]
    {tr : ExecTrace} {j : Nat} (hj : tr.length ≤ j) : (tr.at? j : Option EntryT) = none := by
  simp only [Trace.at?, show ¬ j < tr.length by omega, dite_false]

theorem quietExt_refl (tr : ExecTrace) : QuietExt tr tr :=
  ⟨Trace.le_refl tr, fun _ h1 h2 => absurd h2 (by omega)⟩

theorem quietExt_trans {tr₁ tr₂ tr₃ : ExecTrace} (h₁ : QuietExt tr₁ tr₂) (h₂ : QuietExt tr₂ tr₃) :
    QuietExt tr₁ tr₃ := by
  refine ⟨Trace.le_trans _ _ _ h₁.1 h₂.1, fun i hi1 hi3 => ?_⟩
  by_cases hi2 : i < tr₂.length
  · obtain ⟨a, b, c, d⟩ := h₁.2 i hi1 hi2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [quietExt_at?_lt h₂ hi2]; exact a
    · exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_le h₂.1 hi2 b
    · rw [quietExt_at?_lt h₂ hi2]; exact c
    · rw [quietExt_at?_lt h₂ hi2]; exact d
  · exact h₂.2 i (by omega) hi3

theorem quietExt_of_noSessionEffect {tr : ExecTrace} {m : Move} (h : NoSessionEffect tr m) :
    QuietExt tr (m.next tr) := by
  refine ⟨((Move.act m).run tr).2.property, fun i hi1 hi2 => h i ?_⟩
  simp only [newIndices, List.mem_range'_1]; omega

theorem quietExt_of_movesFrom :
    ∀ (tr : ExecTrace) (δ : List Move), MovesFrom (fun tr m => NoSessionEffect tr m) tr δ →
      QuietExt tr (runMoves δ tr).1
  | tr, [], _ => by simpa [runMoves] using quietExt_refl tr
  | tr, m :: δ, ⟨h, hδ⟩ => by
    simp only [runMoves]
    exact quietExt_trans (quietExt_of_noSessionEffect h) (quietExt_of_movesFrom (m.next tr) δ hδ)

theorem quietExt_st {tr tr' : ExecTrace} (h : QuietExt tr tr') (j : Nat) :
    (tr'.at? j : Option QStE) = tr.at? j := by
  by_cases hj : j < tr.length
  · exact quietExt_at?_lt h hj
  · rw [at?_none_of_ge (by omega : tr.length ≤ j)]
    by_cases hj' : j < tr'.length
    · exact (h.2 j (by omega) hj').1
    · exact at?_none_of_ge (by omega)

theorem quietExt_tr {tr tr' : ExecTrace} (h : QuietExt tr tr') (j : Nat) :
    (tr'.at? j : Option QTrE) = tr.at? j := by
  by_cases hj : j < tr.length
  · exact quietExt_at?_lt h hj
  · rw [at?_none_of_ge (by omega : tr.length ≤ j)]
    by_cases hj' : j < tr'.length
    · exact (h.2 j (by omega) hj').2.2.1
    · exact at?_none_of_ge (by omega)

theorem q_run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem q_getGlobalState_fst (stateIdx : Nat) (tr : ExecTrace) :
    ((PersistentGlobalState.getGlobalState stateIdx :
      Traceful (PersistentLocalState.LocalState TRState)).run tr).1 =
      (tr.at? stateIdx : Option QStE).map (·.st) := by
  simp only [Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [q_run_bind_fst]; simp only [Traceful.run_mk, Traceful.run_pure]
  rcases (tr.at? stateIdx : Option QStE) with _ | e <;> rfl

theorem quiet_getLocalState {tr tr' : ExecTrace} (h : QuietExt tr tr') (p : Participant)
    (stateIdx : Nat) :
    ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr').1 =
      ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1]
  rw [q_run_bind_fst, q_run_bind_fst, q_getGlobalState_fst, q_getGlobalState_fst, quietExt_st h]
  rcases (tr.at? stateIdx : Option QStE) with _ | ⟨⟨q, st⟩⟩
  · rfl
  · simp only [Option.map, q_run_bind_fst]
    unfold _root_.guard; split_ifs <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

theorem q_all_congr_mem {l : List Nat} {f g : Nat → Bool} (h : ∀ j ∈ l, f j = g j) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih (fun j hj => h j (List.mem_cons_of_mem a hj))]

theorem q_any_congr_mem {l : List Nat} {f g : Nat → Bool} (h : ∀ j ∈ l, f j = g j) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a List.mem_cons_self,
      ih (fun j hj => h j (List.mem_cons_of_mem a hj))]

theorem quiet_isCurrentSnapshot {tr tr' : ExecTrace} (h : QuietExt tr tr') (stateIdx : Nat) :
    TripleRatchet.isCurrentSnapshot tr' stateIdx = TripleRatchet.isCurrentSnapshot tr stateIdx := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  simp only [quietExt_st h]
  rcases hs : (tr.at? stateIdx : Option QStE) with _ | e
  · rfl
  · dsimp only
    have hlt : stateIdx < tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := QStE) tr stateIdx
      rw [hs] at this; exact this
    have hlen := quietExt_len h
    rw [show tr'.length - (stateIdx + 1) =
        (tr.length - (stateIdx + 1)) + (tr'.length - tr.length) by omega,
      ← List.range'_append_1, List.all_append]
    simp only [show stateIdx + 1 + (tr.length - (stateIdx + 1)) = tr.length by omega]
    rw [q_all_congr_mem (l := List.range' tr.length (tr'.length - tr.length))
      (g := fun _ => true) (fun j hj => by
        rw [List.mem_range'_1] at hj
        rw [at?_none_of_ge (by omega : tr.length ≤ j)])]
    simp

theorem quiet_someEventOnTraceB {tr tr' : ExecTrace} (h : QuietExt tr tr') (P : TREvent → Bool) :
    (TripleRatchet.anyEventOnTrace TripleRatchet.TREvent) tr' P = (TripleRatchet.anyEventOnTrace TripleRatchet.TREvent) tr P := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  simp only [quietExt_tr h]
  have hlen := quietExt_len h
  rw [show tr'.length = tr.length + (tr'.length - tr.length) by omega, List.range_add,
    List.any_append, List.any_map]
  rw [q_any_congr_mem (l := List.range (tr'.length - tr.length)) (g := fun _ => false)
    (fun j _ => by
      simp only [Function.comp_apply]
      rw [at?_none_of_ge (by omega : tr.length ≤ tr.length + j)])]
  simp

theorem quiet_eventLoggedAt {tr tr' : ExecTrace} (h : QuietExt tr tr') (ev : TREvent) (i : Nat) :
    tr'.EventLoggedAt ev i ↔ tr.EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  rw [quietExt_tr h]

theorem quiet_getMessageSentAt {tr tr' : ExecTrace} (h : QuietExt tr tr') {i : Nat} {x : DY.Bytes}
    (hi : tr.getMessageSentAt i = some x) : tr'.getMessageSentAt i = some x := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at hi ⊢
  have hlt : i < tr.length := by
    by_contra hge
    rw [at?_none_of_ge (EntryT := DY.Network.ExecEntryT) (by omega : tr.length ≤ i)] at hi
    cases hi
  rw [quietExt_at?_lt (EntryT := DY.Network.ExecEntryT) h hlt]; exact hi

theorem quiet_bobDoneBaseKeys {tr tr' : ExecTrace} (h : QuietExt tr tr') :
    bobDoneBaseKeys tr' = bobDoneBaseKeys tr := by
  exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.bobDoneBaseKeys_eq_of_nonSessionPQExt h.1
    fun i h1 h2 => (h.2 i h1 h2).2.1

theorem quiet_trNsBound {r : ProtocolSetup} {ms ms' : List Move} {sent : List HwBytes}
    (h : QuietExt (runTraceMoves r ms) (runTraceMoves r ms')) (hns : TR.TRNsBound r ms sent) :
    TR.TRNsBound r ms' sent := by
  intro q stateIdx st hget
  rw [quiet_getLocalState h] at hget
  exact hns q stateIdx st hget

theorem quiet_trRecordStateInv {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {Z : TR.PureTRSlots} {g : Ghost} {ms ms' : List Move} {records : Participant → Option HwBytes}
    (h : QuietExt (runTraceMoves r ms) (runTraceMoves r ms'))
    (hrsi : TR.PureTRRecordStateInv interpretation r S Z g ms records) :
    TR.PureTRRecordStateInv interpretation r S Z g ms' records := by
  intro q b hqb
  obtain ⟨hq_mem, rec, st, stateIdx, hb, hget, hcur, hrel, hsk, hcanon, hks, hnd⟩ := hrsi q b hqb
  refine ⟨hq_mem, rec, st, stateIdx, hb, ?_, ?_, hrel, ?_, hcanon, hks, hnd⟩
  · rw [quiet_getLocalState h]; exact hget
  · rw [quiet_isCurrentSnapshot h]; exact hcur
  · intro c hc k hk
    obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsu, hru, hgam, hsrk, hfind⟩ := hsk c hc k hk
    refine ⟨pk, rIdx, srcIdx, skIdx, seed, (quiet_eventLoggedAt h _ _).mpr hlog, ?_, ?_, hgam, hsrk, hfind⟩
    · unfold TripleRatchet.skippedKeyUsedB at hsu ⊢; rw [quiet_someEventOnTraceB h]; exact hsu
    · unfold TripleRatchet.receiverKeyUsedB at hru ⊢; rw [quiet_someEventOnTraceB h]; exact hru

theorem quiet_roleSnapshots {r : ProtocolSetup} {tr tr' : ExecTrace} (h : QuietExt tr tr')
    (hr : RoleSnapshots r tr) : RoleSnapshots r tr' :=
  fun p st i hget => hr p st i ((quietExt_st h i).symm.trans hget)

theorem quiet_pureAliceInitPending {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms ms' : List Move} {b : HwBytes}
    (h : QuietExt (runTraceMoves r ms) (runTraceMoves r ms'))
    (hp : PureAliceInitPending interp r S g ms b) :
    PureAliceInitPending interp r S g ms' b := by
  obtain ⟨sess, sc, remote, items, kpk, st, stateIdx, ekIdx, ctIdx, ek, ct,
    h1, h2, h3, hget, hcur, h6, h7, hek, hct, rest⟩ := hp
  exact ⟨sess, sc, remote, items, kpk, st, stateIdx, ekIdx, ctIdx, ek, ct,
    h1, h2, h3, by rw [quiet_getLocalState h]; exact hget,
    by rw [quiet_isCurrentSnapshot h]; exact hcur, h6, h7,
    quiet_getMessageSentAt h hek, quiet_getMessageSentAt h hct, rest⟩

theorem quiet_pureCRecRel {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms ms' : List Move} {p : Participant} {b : HwBytes}
    (h : QuietExt (runTraceMoves r ms) (runTraceMoves r ms'))
    (hc : PureCRecRel interp r S g ms p b) : PureCRecRel interp r S g ms' p b := by
  rcases hc with hc | ⟨hpa, hc⟩
  · exact Or.inl (quiet_trRecordStateInv h hc)
  · exact Or.inr ⟨hpa, quiet_pureAliceInitPending h hc⟩

theorem quiet_availableStates {r : ProtocolSetup} {tr tr' : ExecTrace} (h : QuietExt tr tr')
    {st : TRState}
    (hst : st ∈ DY.Libsignal.Composed.Refinement.availableStates r tr') :
    st ∈ DY.Libsignal.Composed.Refinement.availableStates r tr := by
  unfold DY.Libsignal.Composed.Refinement.availableStates
    DY.Libsignal.Composed.Refinement.storedStates
    DY.Libsignal.Composed.Refinement.newIndices
    DY.ExecTrace.getLocalStateAt at hst ⊢
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst
  obtain ⟨i, hi, hget⟩ := List.mem_filterMap.mp hls
  rw [List.mem_range'_1] at hi
  rw [quietExt_st h i] at hget
  have hlt : i < tr.length := by
    by_contra hge
    rw [at?_none_of_ge (by omega : tr.length ≤ i)] at hget
    simp at hget
  exact List.mem_map.mpr ⟨ls, List.mem_filterMap.mpr
    ⟨i, List.mem_range'_1.mpr ⟨hi.1, by omega⟩, hget⟩, rfl⟩

theorem quiet_cHist {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms ms' : List Move} (h : QuietExt (runTraceMoves r ms) (runTraceMoves r ms'))
    (hc : CHist interp r S g ms) : CHist interp r S g ms' := by
  obtain ⟨hlen, hlow, hfresh, hnd⟩ := hc
  refine ⟨fun st hst => hlen st (quiet_availableStates h hst),
    fun st hst => hlow st (quiet_availableStates h hst), ?_,
    fun st hst => hnd st (quiet_availableStates h hst)⟩
  intro s pk n seed rIdx src i p₀ st₀ c₀ hlog hstored hfor
  exact hfresh s pk n seed rIdx src i p₀ st₀ c₀ ((quiet_eventLoggedAt h _ _).mp hlog)
    ((quietExt_st h src).symm.trans hstored) hfor

end PureXplQuiet

theorem pureCRelAt_quiet {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {records : Participant → Option HwBytes}
    {sent accepted : List HwBytes}
    {acc blk : List MachineEvent} {g : Ghost} {ms₀ δ : List Move}
    (_hB : XplBlock interp r S who g ms₀ δ acc blk)
    (hquiet : MovesFrom (fun tr m => NoSessionEffect tr m) (runTraceMoves r ms₀) δ)
    (hsent : TR.sentBodies (acc ++ blk) = TR.sentBodies acc)
    (hrel : PureCRelAt interp r S g ms₀ records sent accepted acc) :
    PureCRelAt interp r S g (ms₀ ++ δ) records sent accepted (acc ++ blk) := by
  have hq : PureXplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ δ)) := by
    rw [TR.runTrace_append]; exact PureXplQuiet.quietExt_of_movesFrom _ δ hquiet
  have hbd := PureXplQuiet.quiet_bobDoneBaseKeys hq
  obtain ⟨hrec, ⟨hs, hns, hacc1, hacc2⟩, hhist, hrole⟩ := hrel
  refine ⟨fun p b hpb => ?_, ⟨hs.trans hsent.symm, PureXplQuiet.quiet_trNsBound hq hns, ?_, ?_⟩,
    PureXplQuiet.quiet_cHist hq hhist, PureXplQuiet.quiet_roleSnapshots hq hrole⟩
  · obtain ⟨hmem, hne, hc⟩ := hrec p b hpb
    exact ⟨hmem, hne, pureCRecRelH_mono (fun _ => PureXplQuiet.quiet_pureCRecRel hq) hc⟩
  · rw [hbd]; exact hacc1
  · rw [hbd]; exact hacc2

theorem bks_quiet {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {records : Participant → Option HwBytes} {g : Ghost} {ms₀ δ : List Move}
    (hquiet : MovesFrom (fun tr m => NoSessionEffect tr m) (runTraceMoves r ms₀) δ)
    (hbks : BobRecordBaseKeyInSession interp r S g ms₀ records) :
    BobRecordBaseKeyInSession interp r S g (ms₀ ++ δ) records := by
  have hq : PureXplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ δ)) := by
    rw [TR.runTrace_append]; exact PureXplQuiet.quietExt_of_movesFrom _ δ hquiet
  refine bks_of_ext (newBobSinfo_of_noNewSt fun j hj => ?_) (bks_rec_of_eq rfl) hbks
  rw [PureXplQuiet.quietExt_st hq j]
  exact PureXplQuiet.at?_none_of_ge hj

/-- Full `PureCRel` transfer across any call-boundary block `blk` whose explanations add no session
effect (`NoSessionEffect`), emit no `.send` events, and start with `.recv` or `.pt`. -/
theorem pureCRel_transfer_quiet {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
    {acc blk : List MachineEvent}
    (hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (hnosend : ∀ b, MachineEvent.send b ∉ blk)
    (hquiet_all : ∀ g ms₀ δ,
      XplBlock interp r S who g ms₀ δ acc blk →
      MovesFrom (fun tr m => NoSessionEffect tr m) (runTraceMoves r ms₀) δ)
    (hrel : PureCRel interp r S who ok records sent accepted acc) :
    PureCRel interp r S who ok records sent accepted (acc ++ blk) where
  oooAll := hrel.oooAll
  sendsFit := TR.sendsFit_append hrel.sendsFit fun b hb => absurd hb (hnosend b)
  bka := hrel.bka
  bkn := hrel.bkn
  clean := fun g ms hc => by
    have hmp := hc.matched
    obtain ⟨ms₀, δ, rfl, hpre_mp, hmatch⟩ :=
      matchedPrefix_split hmp hhead (matchedPrefix_prefix_reachable hmp)
    have hc₀ : Clean interp r S who ok g ms₀ acc :=
      clean_prefix hpre_mp.2.2.2.2.2.length_eq hc
    have hB : XplBlock interp r S who g ms₀ δ acc blk := ⟨hpre_mp, hmp.2.1, hmatch⟩
    have hq := hquiet_all g ms₀ δ hB
    have hsb_nil : TR.sentBodies blk = [] := by
      unfold TR.sentBodies
      refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
      cases e with
      | send b => exact absurd he (hnosend b)
      | _ => rfl
    have hsent : TR.sentBodies (acc ++ blk) = TR.sentBodies acc := by
      rw [TR.sentBodies_append, hsb_nil, List.append_nil]
    obtain ⟨hat₀, hbks₀⟩ := hrel.clean g ms₀ hc₀
    exact ⟨pureCRelAt_quiet hB hq hsent hat₀, bks_quiet hq hbks₀⟩

/-! ## `CoinSplit` Event-List Algebra -/

theorem coinSplit_append {τ₁ τ₁' τ₂ τ₂' : List MachineEvent}
    (h₁ : CoinSplit τ₁ τ₁') (h₂ : CoinSplit τ₂ τ₂') :
    CoinSplit (τ₁ ++ τ₂) (τ₁' ++ τ₂') := by
  induction h₁ with
  | nil => exact h₂
  | keep hne _ ih => exact .keep hne ih
  | split hne hpref _ ih =>
    rw [List.append_assoc]
    exact .split hne hpref ih

theorem coinSplit_refl_of_no_rng {evs : List MachineEvent}
    (hno : ∀ e ∈ evs, ∀ b, e ≠ .rng b) :
    CoinSplit evs evs := by
  induction evs with
  | nil => exact .nil
  | cons e tl ih =>
    exact .keep (hno e (List.mem_cons_self ..))
      (ih fun e' he' => hno e' (List.mem_cons_of_mem _ he'))

theorem coinSplit_leaks {leaks : List MachineEvent}
    (hleaks : ∀ e ∈ leaks, ∃ k, e = .leak k) :
    CoinSplit leaks leaks :=
  coinSplit_refl_of_no_rng fun e he _ => by
    obtain ⟨_, rfl⟩ := hleaks e he; rintro ⟨⟩

theorem coinSplit_cliEntry_pieces (c : CliCall) {pieces : List HwBytes}
    (hne : ∀ p ∈ pieces, p ≠ []) (hpref : pieces.flatten <+: c.coins) :
    CoinSplit (cliEntryEvents c) ([cliInputEvent c] ++ pieces.map MachineEvent.rng) := by
  rw [cliEntryEvents_eq]
  refine .keep ?_ (by simpa using CoinSplit.split hne hpref CoinSplit.nil)
  rcases c with ⟨_, _ | _ | _, _ | _, _, _⟩ <;> rintro _ ⟨⟩

theorem coinSplit_cliEntry_drop_rng (c : CliCall) :
    CoinSplit (cliEntryEvents c) [cliInputEvent c] := by
  simpa using coinSplit_cliEntry_pieces c (pieces := []) (fun _ h => nomatch h) List.nil_prefix

theorem coinSplit_cliEntry_one_piece (c : CliCall) {d : HwBytes}
    (hne : d ≠ []) (hpref : d <+: c.coins) :
    CoinSplit (cliEntryEvents c) [cliInputEvent c, .rng d] := by
  refine coinSplit_cliEntry_pieces c (pieces := [d])
    (fun p hp => by rcases List.mem_singleton.mp hp with rfl; exact hne) ?_
  simpa using hpref

end Symbolic.Swarm.CREF.CliPure
