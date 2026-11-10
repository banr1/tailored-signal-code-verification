/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatement
import all DY.Bytes.Basic
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.ALaCarte.Basic
import all DY.Actions.PersistentGlobalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
import all DY.Trace.Manipulation
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2

/-!
# `send` Move Classification and Coin-Cut Determinism

Classifies model moves whose visible entries contain `.pt` (`encrypt`, `encryptAbort`,
`encryptFail`) and proves that an exit-`0` `send` block cut `blk_hw` of
`[.pt stdin, .rng coins, .send out]` has the form `sendCutOfLen stdin coins out n` for some
`n ≤ coins.length`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.S3

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli

/-- Canonical `blk_hw` cut of `[.pt stdin, .rng coins, .send out]` for a given `coinsLen`. -/
def sendCutOfLen (stdin coins out : HwBytes) (coinsLen : Nat) : List MachineEvent :=
  if coinsLen = 0 then
    [.pt stdin, .send out]
  else
    [.pt stdin, .rng (coins.take coinsLen), .send out]

private theorem exposures_kind_leak {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') : v.kind = .leak := by
  unfold exposures at hv
  rw [List.mem_append] at hv
  rcases hv with hv | hv
  · rw [List.mem_filterMap] at hv
    rcases hv with ⟨j, _, hj⟩
    unfold pqExposureAt at hj
    split at hj <;> simp at hj <;> cases hj <;> rfl
  · rw [List.mem_filterMap] at hv
    rcases hv with ⟨j, _, hj⟩
    unfold trExposureAt at hj
    split at hj <;> simp at hj <;> cases hj <;> rfl

private theorem aliceDraws_kind_rng {done : Option Nat} {rs : List DY.Bytes} {v : VisEntry}
    (hv : v ∈ aliceDraws done rs) : v.kind = .rng := by
  match rs with
  | [] => simp [aliceDraws] at hv
  | [ek] =>
    simp [aliceDraws, rngEntry] at hv
    subst hv
    rfl
  | ek :: entropy :: rest =>
    simp only [aliceDraws, kyberCoinEntries, rngEntry, List.mem_cons, List.mem_append,
      List.mem_map] at hv
    rcases hv with (rfl | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> rfl

private theorem aliceVis_kind_ne_pt {tr tr' : ExecTrace} {h : PQXDH.BundleHandles} {v : VisEntry}
    (hv : v ∈ aliceVis tr tr' h) : v.kind ≠ .pt := by
  simp only [aliceVis, List.mem_cons] at hv
  rcases hv with rfl | hv
  · intro hc; cases hc
  · rw [aliceDraws_kind_rng hv]; decide

private theorem bobVis_kind_ne_pt {tr tr' : ExecTrace} {mh : PQXDH.PreKeyMsgHandles}
    {opk : Option DY.Bytes} {v : VisEntry}
    (hv : v ∈ bobVis tr tr' mh opk) : v.kind ≠ .pt := by
  unfold bobVis at hv
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
    Option.mem_toList, Option.map_eq_some_iff] at hv
  rcases hv with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · intro hc; cases hc
  · simp [rngEntry]
  · intro hc; cases hc

private theorem decVis_kind_ne_pt {tr tr' : ExecTrace} {stateIdx msgIdx : Nat} {wrapped : Bool}
    {v : VisEntry} (hv : v ∈ decVis tr tr' stateIdx msgIdx wrapped) : v.kind ≠ .pt := by
  unfold decVis at hv
  simp only [List.append_assoc, List.mem_append, Option.mem_toList, Option.map_eq_some_iff,
    List.mem_map] at hv
  rcases hv with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · intro hc; cases hc
  · simp [rngEntry]
  · intro hc; cases hc

/-- Any `Move` whose visible entries contain a `.pt` entry is `encrypt`, `encryptAbort`, or
`encryptFail`. -/
theorem move_of_vis_has_pt {m : Move} {tr : ExecTrace} {v : VisEntry}
    (hv : v ∈ m.vis tr) (hk : v.kind = .pt) :
    (∃ me sIdx cLen pqIdx wrap, m = .encrypt me sIdx cLen pqIdx wrap) ∨
      (∃ me sIdx, m = .encryptAbort me sIdx) ∨
      (∃ me sIdx cLen, m = .encryptFail me sIdx cLen) := by
  unfold Move.vis at hv
  rw [List.mem_append] at hv
  rcases hv with hv | hv
  · cases m with
    | encrypt me sIdx cLen pqIdx wrap => exact Or.inl ⟨me, sIdx, cLen, pqIdx, wrap, rfl⟩
    | encryptAbort me sIdx => exact Or.inr (Or.inl ⟨me, sIdx, rfl⟩)
    | encryptFail me sIdx cLen => exact Or.inr (Or.inr ⟨me, sIdx, cLen, rfl⟩)
    | aliceStart _ _ _ _ h shown =>
      exact absurd hk (aliceVis_kind_ne_pt (List.mem_of_mem_take hv))
    | bobStart b _ kh _ mh _ _ shown =>
      exact absurd hk (bobVis_kind_ne_pt (List.mem_of_mem_take hv))
    | decrypt _ stateIdx msgIdx _ _ wrapped =>
      exact absurd hk (decVis_kind_ne_pt hv)
    | decryptSkipped _ stateIdx msgIdx _ _ _ wrapped =>
      exact absurd hk (decVis_kind_ne_pt hv)
    | reject draws =>
      simp only [List.mem_cons, List.mem_map] at hv
      rcases hv with rfl | ⟨_, _, rfl⟩ <;> simp at hk
    | _ => simp only [List.not_mem_nil] at hv
  · have hleak := exposures_kind_leak hv
    rw [hk] at hleak
    cases hleak

private abbrev StEntry :=
  DY.PersistentGlobalState.State.ExecEntryT
    (DY.PersistentLocalState.LocalState TripleRatchet.TRState)

private theorem run_bind_fst {α β : Type} (x : DY.Traceful α) (f : α → DY.Traceful β)
    (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [DY.Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem run_bind_snd {α β : Type} (x : DY.Traceful α) (f : α → DY.Traceful β)
    (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [DY.Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem getLocalState_run_eq_self (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((DY.PersistentLocalState.getLocalState me stH : DY.Traceful TripleRatchet.TRState).run tr).2.val =
      tr := by
  unfold DY.PersistentLocalState.getLocalState DY.PersistentGlobalState.getGlobalState
    DY.getEntry _root_.guard
  rw [run_bind_snd, run_bind_fst, run_bind_snd, DY.Traceful.run_mk]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · change (((if p = me then pure () else failure : DY.Traceful Unit) >>= fun _ => pure st).run tr).2.val = tr
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h]; rfl
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp]; rfl

private def Runs {α : Type} (x : DY.Traceful α) (tr : ExecTrace) (a : α) (tr' : ExecTrace) : Prop :=
  (x.run tr).1 = some a ∧ (x.run tr).2.val = tr'

private def Fails {α : Type} (x : DY.Traceful α) (tr tr' : ExecTrace) : Prop :=
  (x.run tr).1 = none ∧ (x.run tr).2.val = tr'

private theorem Fails.bind_left {α β : Type} {x : DY.Traceful α} {f : α → DY.Traceful β}
    {tr tr' : ExecTrace} (h : Fails x tr tr') : Fails (x >>= f) tr tr' := by
  obtain ⟨h1, h2⟩ := h
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1 h2; cases h1; cases h2
  refine ⟨?_, ?_⟩ <;> rw [DY.Traceful.run_bind, hx]

private theorem Fails.bind_right {α β : Type} {x : DY.Traceful α} {f : α → DY.Traceful β}
    {tr tr1 tr2 : ExecTrace} {a : α} (h1 : Runs x tr a tr1) (h2 : Fails (f a) tr1 tr2) :
    Fails (x >>= f) tr tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1a h1b; cases h1a; cases h1b
  rcases hf : (f a).run t with ⟨o', t', ht'⟩
  rw [hf] at h2a h2b; cases h2a; cases h2b
  refine ⟨?_, ?_⟩ <;> rw [DY.Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem Runs.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : p) :
    Runs (_root_.guard p : DY.Traceful Unit) tr () tr := by
  simp only [_root_.guard, h, ↓reduceIte]; exact ⟨rfl, rfl⟩

private theorem Fails.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : ¬ p) :
    Fails (_root_.guard p : DY.Traceful Unit) tr tr := by
  simp only [_root_.guard, h, ↓reduceIte]; exact ⟨rfl, rfl⟩

private theorem Runs.traceLength (tr : ExecTrace) :
    Runs TripleRatchet.traceLength tr tr.length tr := ⟨rfl, rfl⟩

private theorem Runs.getLocalState {me : Participant} {stH : Nat} {tr : ExecTrace}
    {st : TripleRatchet.TRState}
    (h : ((DY.PersistentLocalState.getLocalState me stH :
      DY.Traceful TripleRatchet.TRState).run tr).1 = some st) :
    Runs (DY.PersistentLocalState.getLocalState me stH : DY.Traceful TripleRatchet.TRState)
      tr st tr :=
  ⟨h, getLocalState_run_eq_self me stH tr⟩

private theorem Fails.getLocalState {me : Participant} {stH : Nat} {tr : ExecTrace}
    (h : ((DY.PersistentLocalState.getLocalState me stH :
      DY.Traceful TripleRatchet.TRState).run tr).1 = none) :
    Fails (DY.PersistentLocalState.getLocalState me stH : DY.Traceful TripleRatchet.TRState)
      tr tr :=
  ⟨h, getLocalState_run_eq_self me stH tr⟩

private theorem Runs.genRand (n : Nat) (tr : ExecTrace) :
    Runs (DY.Random.genRand n : DY.Traceful DY.Bytes) tr (randTerm tr.length n)
      (tr.append (⟨n⟩ : DY.Random.ExecEntryT)) := ⟨rfl, rfl⟩

private theorem Runs.sendMessage (m : DY.Bytes) (tr : ExecTrace) :
    Runs (DY.Network.sendMessage m : DY.Traceful Nat) tr tr.length
      (tr.append (⟨m⟩ : DY.Network.ExecEntryT)) := ⟨rfl, rfl⟩

private theorem Fails.receiveMessage {idx : Nat} {tr : ExecTrace}
    (h : (tr.at? idx : Option DY.Network.ExecEntryT) = none) :
    Fails (DY.Network.receiveMessage idx : DY.Traceful DY.Bytes) tr tr := by
  unfold DY.Network.receiveMessage DY.getEntry
  refine ⟨?_, ?_⟩
  · rw [run_bind_fst, DY.Traceful.run_mk, h]
  · rw [run_bind_snd, DY.Traceful.run_mk, h]

private abbrev TREntry := DY.ProtocolEvent.ExecEntryT TripleRatchet.TREvent

private theorem Runs.bind {α β : Type} {x : DY.Traceful α} {f : α → DY.Traceful β}
    {tr tr1 tr2 : ExecTrace} {a : α} {b : β}
    (h1 : Runs x tr a tr1) (h2 : Runs (f a) tr1 b tr2) :
    Runs (x >>= f) tr b tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1a h1b; cases h1a; cases h1b
  rcases hf : (f a).run t with ⟨o', t', ht'⟩
  rw [hf] at h2a h2b; cases h2a; cases h2b
  refine ⟨?_, ?_⟩ <;> rw [DY.Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem Runs.pure {α : Type} (a : α) (tr : ExecTrace) :
    Runs (pure a : DY.Traceful α) tr a tr := ⟨rfl, rfl⟩

private theorem Runs.receiveMessage {idx : Nat} {tr : ExecTrace} {m : DY.Bytes}
    (h : (tr.at? idx : Option DY.Network.ExecEntryT) = some ⟨m⟩) :
    Runs (DY.Network.receiveMessage idx : DY.Traceful DY.Bytes) tr m tr := by
  unfold DY.Network.receiveMessage DY.getEntry
  refine ⟨?_, ?_⟩
  · rw [run_bind_fst, DY.Traceful.run_mk, h]; rfl
  · rw [run_bind_snd, DY.Traceful.run_mk, h]; rfl

private theorem Runs.logEvent (ev : TripleRatchet.TREvent) (tr : ExecTrace) :
    Runs (DY.ProtocolEvent.logEvent ev : DY.Traceful Unit) tr ()
      (tr.append (⟨ev⟩ : TREntry)) := ⟨rfl, rfl⟩

private theorem Runs.storeLocalState (me : Participant) (st : TripleRatchet.TRState)
    (tr : ExecTrace) :
    Runs (DY.PersistentLocalState.storeLocalState me st : DY.Traceful Nat) tr tr.length
      (tr.append (⟨⟨me, st⟩⟩ : StEntry)) := ⟨rfl, rfl⟩

private theorem Runs.logMessageKeyAndStore (me : Participant) (s : TripleRatchet.SessionInfo)
    (dir : TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32)
    (rIdx parentStateIdx : Nat) (st : TripleRatchet.TRState) (tr : ExecTrace) :
    Runs (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx
        parentStateIdx st)
      tr (tr.length + 1)
      ((tr.append (⟨TripleRatchet.TREvent.MessageKey s dir seed pqSalt n rIdx
        parentStateIdx⟩ : TREntry)).append (⟨⟨me, st⟩⟩ : StEntry)) := by
  unfold TripleRatchet.logMessageKeyAndStore
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact Runs.storeLocalState _ _ _

private theorem at?_append_of_lt {E1 E2 : Type} [DY.ExecTraceTypes.Has E1]
    [DY.ExecTraceTypes.Has E2] (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by change i < tr.length + 1; omega
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr (tr.append e) i hi (DY.Trace.append_le tr e)]

private theorem at?_append_eq_none {E1 E2 : Type} [DY.ExecTraceTypes.Has E1]
    [DY.ExecTraceTypes.Has E2] (tr : ExecTrace) (e : E1)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) =
      none) :
    ((tr.append e).at? tr.length : Option E2) = none := by
  simp [DY.Trace.at?, DY.Trace.append, DY.Trace.at, DY.Trace.length, hnone]

private theorem newRandoms_append_rnd (tr0 tr : ExecTrace) (hle : tr0.length ≤ tr.length)
    (n : Nat) :
    newRandoms tr0 (tr.append (⟨n⟩ : DY.Random.ExecEntryT)) =
      newRandoms tr0 tr ++ [(randTerm tr.length n, n)] := by
  unfold newRandoms newIndices
  have hlen : (tr.append (⟨n⟩ : DY.Random.ExecEntryT)).length = tr.length + 1 := rfl
  rw [hlen, show tr.length + 1 - tr0.length = (tr.length - tr0.length) + 1 by omega,
    ← List.range'_append_1, List.filterMap_append]
  have hcongr :
      List.filterMap (fun i =>
        (((tr.append (⟨n⟩ : DY.Random.ExecEntryT)).at? i : Option DY.Random.ExecEntryT)).map
          fun e => (randTerm i e.length, e.length))
        (List.range' tr0.length (tr.length - tr0.length)) =
      List.filterMap (fun i =>
        ((tr.at? i : Option DY.Random.ExecEntryT)).map
          fun e => (randTerm i e.length, e.length))
        (List.range' tr0.length (tr.length - tr0.length)) := by
    refine List.filterMap_congr fun i hi => ?_
    rw [List.mem_range'_1] at hi
    rw [at?_append_of_lt tr _ (by omega)]
  have hlast :
      (((tr.append (⟨n⟩ : DY.Random.ExecEntryT)).at? tr.length :
        Option DY.Random.ExecEntryT)) = some ⟨n⟩ :=
    DY.Trace.at?_append tr _
  rw [hcongr, show tr0.length + (tr.length - tr0.length) = tr.length by omega,
    List.range'_one, List.filterMap_cons, List.filterMap_nil, hlast]
  rfl

private theorem newRandoms_append_non_rnd {E : Type} [DY.ExecTraceTypes.Has E]
    (tr0 tr : ExecTrace) (hle : tr0.length ≤ tr.length) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none) :
    newRandoms tr0 (tr.append e) = newRandoms tr0 tr := by
  unfold newRandoms newIndices
  have hlen : (tr.append e).length = tr.length + 1 := rfl
  rw [hlen, show tr.length + 1 - tr0.length = (tr.length - tr0.length) + 1 by omega,
    ← List.range'_append_1, List.filterMap_append]
  have hcongr :
      List.filterMap (fun i =>
        (((tr.append e).at? i : Option DY.Random.ExecEntryT)).map
          fun r => (randTerm i r.length, r.length))
        (List.range' tr0.length (tr.length - tr0.length)) =
      List.filterMap (fun i =>
        ((tr.at? i : Option DY.Random.ExecEntryT)).map
          fun r => (randTerm i r.length, r.length))
        (List.range' tr0.length (tr.length - tr0.length)) := by
    refine List.filterMap_congr fun i hi => ?_
    rw [List.mem_range'_1] at hi
    rw [at?_append_of_lt tr _ (by omega)]
  have hlast :
      (((tr.append e).at? tr.length :
        Option DY.Random.ExecEntryT)) = none :=
    at?_append_eq_none tr e hnone
  rw [hcongr, show tr0.length + (tr.length - tr0.length) = tr.length by omega,
    List.range'_one, List.filterMap_cons, List.filterMap_nil, hlast]
  simp

private theorem encrypt_next_or_newRandoms (me : Participant) (sIdx cLen pqIdx : Nat)
    (wrap : Option (Nat × Nat)) (tr : ExecTrace) :
    (Move.encrypt me sIdx cLen pqIdx wrap).next tr = tr ∨
      newRandoms tr ((Move.encrypt me sIdx cLen pqIdx wrap).next tr) =
        [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) cLen, cLen)] := by
  rcases hst :
      ((DY.PersistentLocalState.getLocalState me sIdx :
        DY.Traceful TripleRatchet.TRState).run tr).1 with _ | st
  · have hf : Fails (Move.encrypt me sIdx cLen pqIdx wrap).act tr tr := by
      unfold Move.act TripleRatchet.messageEncrypt
      exact Fails.bind_left (Fails.bind_left (Fails.getLocalState hst))
    exact Or.inl hf.2
  · by_cases hns : st.ns = TripleRatchet.u32Max
    · have hf : Fails (Move.encrypt me sIdx cLen pqIdx wrap).act tr tr := by
        unfold Move.act TripleRatchet.messageEncrypt
        exact Fails.bind_left (Fails.bind_right (Runs.getLocalState hst)
          (Fails.bind_left (Fails.guard _ (fun h => h hns))))
      exact Or.inl hf.2
    · let tr3 := ((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
        (⟨cLen⟩ : DY.Random.ExecEntryT)).append
        (⟨(DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cLen)).2.1⟩ :
          DY.Network.ExecEntryT)
      have hr3 : newRandoms tr tr3 =
          [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) cLen, cLen)] := by
        dsimp only [tr3]
        rw [newRandoms_append_non_rnd tr _ (by change tr.length ≤ tr.length + 2; omega) _ rfl,
          newRandoms_append_rnd tr _ (by change tr.length ≤ tr.length + 1; omega),
          newRandoms_append_rnd tr _ (Nat.le_refl _)]
        have h0 : newRandoms tr tr = [] := by simp [newRandoms, newIndices]
        rw [h0]; rfl
      cases hat : (tr3.at? pqIdx : Option DY.Network.ExecEntryT) with
      | none =>
        have hf : Fails (Move.encrypt me sIdx cLen pqIdx wrap).act tr tr3 := by
          show Fails (TripleRatchet.messageEncrypt me sIdx cLen pqIdx >>= fun _ => pure ()) tr tr3
          refine Fails.bind_left ?_
          unfold TripleRatchet.messageEncrypt
          refine Fails.bind_right (Runs.getLocalState hst) ?_
          refine Fails.bind_right (Runs.guard _ hns) ?_
          refine Fails.bind_right (Runs.genRand 32 tr) ?_
          refine Fails.bind_right (Runs.genRand cLen _) ?_
          refine Fails.bind_right (Runs.sendMessage _ _) ?_
          exact Fails.bind_left (Fails.receiveMessage hat)
        exact Or.inr (by rw [Move.next, hf.2, hr3])
      | some pqSaltEnt =>
        rcases pqSaltEnt with ⟨pqSalt⟩
        have henc : ∃ msgIdx tr7,
            Runs (TripleRatchet.messageEncrypt me sIdx cLen pqIdx) tr msgIdx tr7 ∧
            newRandoms tr tr7 = newRandoms tr tr3 := by
          unfold TripleRatchet.messageEncrypt
          apply Exists.intro
          apply Exists.intro
          constructor
          · apply Runs.bind (Runs.getLocalState hst)
            apply Runs.bind (Runs.guard _ hns)
            apply Runs.bind (Runs.genRand 32 tr)
            apply Runs.bind (Runs.genRand cLen _)
            apply Runs.bind (Runs.sendMessage _ _)
            apply Runs.bind (Runs.receiveMessage hat)
            apply Runs.bind (Runs.logEvent _ _)
            apply Runs.bind (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _)
            exact Runs.sendMessage _ _
          · conv_lhs =>
              rw [newRandoms_append_non_rnd tr _ (by change tr.length ≤ tr.length + 6; omega) _ rfl,
                newRandoms_append_non_rnd tr _ (by change tr.length ≤ tr.length + 5; omega) _ rfl,
                newRandoms_append_non_rnd tr _ (by change tr.length ≤ tr.length + 4; omega) _ rfl,
                newRandoms_append_non_rnd tr _ (by change tr.length ≤ tr.length + 3; omega) _ rfl]
        obtain ⟨_, tr7, hrun7, hr7⟩ := henc
        have hact : Runs (Move.encrypt me sIdx cLen pqIdx wrap).act tr () tr7 :=
          Runs.bind hrun7 (Runs.pure () tr7)
        exact Or.inr (by rw [Move.next, hact.2, hr7, hr3])

private theorem coinSplit_send_block {stdin coins out : HwBytes} {blk_hw : List MachineEvent}
    (hcs : CoinSplit [.pt stdin, .rng coins, .send out] blk_hw) :
    ∃ pieces : List HwBytes,
      (∀ p ∈ pieces, p ≠ []) ∧
      pieces.flatten <+: coins ∧
      blk_hw = .pt stdin :: pieces.map MachineEvent.rng ++ [.send out] := by
  cases hcs with
  | keep _ hcs1 =>
    cases hcs1 with
    | keep hne _ => exact absurd rfl (hne coins)
    | split hne hpref hcs2 =>
      cases hcs2 with
      | keep _ hcs3 =>
        cases hcs3 with
        | nil => exact ⟨_, hne, hpref, rfl⟩

private theorem encDraws_kind_ne_send {rs : List (DY.Bytes × Nat)} {v : VisEntry}
    (hv : v ∈ encDraws rs) : v.kind ≠ .send := by
  match rs with
  | [] => simp [encDraws] at hv
  | (_, _) :: rest =>
    simp [encDraws, rngEntry] at hv
    rcases hv with rfl | ⟨_, _, rfl⟩
    · intro h; cases h
    · intro h; cases h

private theorem vis_encrypt_eq (me : Participant) (sIdx cLen pqIdx : Nat)
    (wrap : Option (Nat × Nat)) (tr : ExecTrace) :
    (Move.encrypt me sIdx cLen pqIdx wrap).vis tr =
      encDraws (newRandoms tr ((Move.encrypt me sIdx cLen pqIdx wrap).next tr)) ++
        encSend tr ((Move.encrypt me sIdx cLen pqIdx wrap).next tr) wrap ++
        exposures tr ((Move.encrypt me sIdx cLen pqIdx wrap).next tr) := by
  simp [Move.vis, encVis, List.append_assoc]

private theorem forall2_mem_kind {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {es : List MachineEvent} {vs : List VisEntry}
    (h : List.Forall₂ (EventMatchesEntry interp r S g) es vs) :
    (∀ e ∈ es, ∃ v ∈ vs, eventKind e = v.kind) ∧
      (∀ v ∈ vs, ∃ e ∈ es, eventKind e = v.kind) := by
  induction h with
  | nil => exact ⟨by simp, by simp⟩
  | @cons e v es vs hev _ ih =>
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨v, List.Mem.head _, hev.1⟩
      · obtain ⟨w, hw, hk⟩ := ih.1 x hx
        exact ⟨w, List.Mem.tail _ hw, hk⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨e, List.Mem.head _, hev.1⟩
      · obtain ⟨x, hx, hk⟩ := ih.2 w hw
        exact ⟨x, List.Mem.tail _ hx, hk⟩

unseal DY.Bytes in
private local instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩

private theorem gamma_randTerm (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (i n : Nat) :
    gamma interpretation S g (randTerm i n) = if n = 0 then [] else g.σ i n := by
  unfold gamma gamma' randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]
  unfold concretizeRandom node
  split <;> rfl

/-- Any single move `m` matching a `CoinSplit` cut `blk_hw` of `[.pt stdin, .rng coins, .send out]`
is `Move.encrypt` with some slice length `n ≤ coins.length` such that
`blk_hw = sendCutOfLen stdin coins out n`. -/
theorem send_exit0_cut_eq_of_move {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {m : Move} {stdin coins out : HwBytes}
    {blk_hw : List MachineEvent}
    (hcs : CoinSplit [.pt stdin, .rng coins, .send out] blk_hw)
    (hmatch : List.Forall₂ (EventMatchesEntry interp r S g) blk_hw (m.vis tr)) :
    ∃ me stateIdx coinsLen pqIdx wrap n,
      m = .encrypt me stateIdx coinsLen pqIdx wrap ∧
      n ≤ coins.length ∧
      (coinsLen = 0 ↔ n = 0) ∧
      (coinsLen ≠ 0 → g.σ (tr.length + 1) coinsLen = coins.take n) ∧
      blk_hw = sendCutOfLen stdin coins out n := by
  obtain ⟨pieces, hne, hpref, rfl⟩ := coinSplit_send_block hcs
  have hk := forall2_mem_kind hmatch
  obtain ⟨v_pt, hv_pt, hk_pt⟩ := hk.1 (.pt stdin) (by simp)
  obtain ⟨v_sd, hv_sd, hk_sd⟩ := hk.1 (.send out) (by simp)
  have hv_pt_k : v_pt.kind = .pt := hk_pt.symm
  have hv_sd_k : v_sd.kind = .send := hk_sd.symm
  have hm_enc : ∃ me sIdx cLen pqIdx wrap, m = .encrypt me sIdx cLen pqIdx wrap := by
    rcases move_of_vis_has_pt hv_pt hv_pt_k with h | ⟨me, sIdx, rfl⟩ | ⟨me, sIdx, cLen, rfl⟩
    · exact h
    · unfold Move.vis encVis at hv_sd
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_append] at hv_sd
      rcases hv_sd with hv_sd | hv_sd
      · exact absurd hv_sd_k (encDraws_kind_ne_send hv_sd)
      · have := exposures_kind_leak hv_sd; rw [hv_sd_k] at this; cases this
    · unfold Move.vis encVis at hv_sd
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_append] at hv_sd
      rcases hv_sd with hv_sd | hv_sd
      · exact absurd hv_sd_k (encDraws_kind_ne_send hv_sd)
      · have := exposures_kind_leak hv_sd; rw [hv_sd_k] at this; cases this
  obtain ⟨me, sIdx, cLen, pqIdx, wrap, rfl⟩ := hm_enc
  have hexp_nil : exposures tr ((Move.encrypt me sIdx cLen pqIdx wrap).next tr) = [] := by
    rcases hexp : exposures tr ((Move.encrypt me sIdx cLen pqIdx wrap).next tr) with _ | ⟨v, vs⟩
    · rfl
    · have hv_mem : v ∈ (Move.encrypt me sIdx cLen pqIdx wrap).vis tr := by
        rw [vis_encrypt_eq, hexp]; simp
      obtain ⟨e, he, hek⟩ := hk.2 v hv_mem
      have hvl : v.kind = .leak := exposures_kind_leak (by rw [hexp]; simp)
      rw [hvl] at hek
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map] at he
      rcases he with rfl | ⟨_, _, rfl⟩ | he
      · cases hek
      · cases hek
      · simp at he; subst he; cases hek
  rcases encrypt_next_or_newRandoms me sIdx cLen pqIdx wrap tr with htr_eq | hrnd
  · have hvis_nil : (Move.encrypt me sIdx cLen pqIdx wrap).vis tr = [] := by
      rw [vis_encrypt_eq, htr_eq]
      simp [newRandoms, newIndices, encDraws, encSend, lastSent, exposures]
    rw [hvis_nil] at hv_pt
    cases hv_pt
  · have hsend_one : ∃ vsd,
        encSend tr ((Move.encrypt me sIdx cLen pqIdx wrap).next tr) wrap = [vsd] := by
      unfold encSend
      cases hls : lastSent tr ((Move.encrypt me sIdx cLen pqIdx wrap).next tr) with
      | none =>
        exfalso
        rw [vis_encrypt_eq, hexp_nil, List.append_nil] at hv_sd
        simp only [encSend, hls, List.append_nil] at hv_sd
        exact encDraws_kind_ne_send hv_sd hv_sd_k
      | some w =>
        cases wrap with
        | none => exact ⟨_, rfl⟩
        | some ec => exact ⟨_, rfl⟩
    obtain ⟨vsd, hvsd⟩ := hsend_one
    have hvis_eq : (Move.encrypt me sIdx cLen pqIdx wrap).vis tr =
        encDraws [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) cLen, cLen)] ++ [vsd] := by
      rw [vis_encrypt_eq, hexp_nil, List.append_nil, hrnd, hvsd]
    rw [hvis_eq] at hmatch
    by_cases hc0 : cLen = 0
    · subst hc0
      simp only [encDraws, bne_self_eq_false, Bool.false_eq_true, not_false_eq_true,
        List.filter_cons_of_neg, List.filter_nil, List.map_nil, List.cons_append,
        List.nil_append] at hmatch
      have hlen := hmatch.length_eq
      simp at hlen
      subst hlen
      refine ⟨me, sIdx, 0, pqIdx, wrap, 0, rfl, Nat.zero_le _, ⟨fun _ => rfl, fun _ => rfl⟩,
        fun h => absurd rfl h, ?_⟩
      simp [sendCutOfLen]
    · have hc_bne : (cLen != 0) = true := bne_iff_ne.mpr hc0
      simp only [encDraws, hc_bne, List.filter_cons_of_pos, List.filter_nil, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append] at hmatch
      have hlen := hmatch.length_eq
      simp at hlen
      obtain ⟨p, hp_eq⟩ : ∃ p, pieces = [p] := by
        cases pieces with
        | nil => simp at hlen
        | cons p ps =>
          cases ps with
          | nil => exact ⟨p, rfl⟩
          | cons _ _ => simp at hlen
      subst hp_eq
      have hp_ne : p ≠ [] := hne p (by simp)
      have hp_len_ne : p.length ≠ 0 := by
        intro h0
        exact hp_ne (List.eq_nil_of_length_eq_zero h0)
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hpref
      obtain ⟨rest_c, hcoins_eq⟩ := hpref
      have hp_le : p.length ≤ coins.length := by rw [← hcoins_eq, List.length_append]; omega
      have htake : coins.take p.length = p := by
        rw [← hcoins_eq, List.take_left]
      cases hmatch with
      | cons _ hm1 =>
        cases hm1 with
        | cons hm_rng _ =>
          have hγ : gamma interp S g (randTerm (tr.length + 1) cLen) = p := by
            unfold EventMatchesEntry rngEntry eventBytes at hm_rng
            simpa using hm_rng.2
          simp only [gamma_randTerm, hc0, ↓reduceIte] at hγ
          refine ⟨me, sIdx, cLen, pqIdx, wrap, p.length, rfl, hp_le,
            ⟨fun h => absurd h hc0, fun h => absurd h hp_len_ne⟩,
            fun _ => by rw [hγ, htake], ?_⟩
          simp [sendCutOfLen, hp_len_ne, htake]

end Symbolic.Swarm.Coinsplit.S3
