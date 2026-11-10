/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.Leaks
public import Symbolic.Proofs.SpecLemmas.LeakableSecretProofDefs
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Actions.Network
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TRView
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# PQXDH Setup-Secret Compromise Simulation

Proves `setupLeak_step`: every `.leak k` event of a PQXDH setup secret (`SetupLeak`) on a composed
run is matched by one PQXDH compromise move (`compromiseIK`, `compromiseSPK`, `compromisePQSPK`, or
`compromiseOPK`), preserving `MatchedPrefix` and satisfying `AppendsOnlyExposure`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open
open DY.Libsignal.TripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.PQXDH (PQXDHEvent)

/-- The `leakPq` flag of a PQXDH compromise event (`none` if not a compromise). -/
def pqLeakKind : PQXDHEvent → Option Bool
  | .CompromisedIK .. | .CompromisedSPK .. | .CompromisedOPK .. => some false
  | .CompromisedPQSPK .. => some true
  | _ => none

theorem exposures_append_pq_pair (tr : ExecTrace) (ev : PQXDHEvent) (msg : DY.Bytes) (pq : Bool)
    (hk : pqLeakKind ev = some pq) :
    exposures tr ((tr.append (EvE ev)).append (NetE msg)) =
      [⟨.leak, [msg], .leakPq pq, some tr.length⟩] := by
  unfold exposures
  rw [newIndices_append_pair]
  have hlt : tr.length < (tr.append (EvE ev)).length := by simp [length_append']
  have hA0 : ∀ {E₂ : Type} [ExecTraceTypes.Has E₂],
      (((tr.append (EvE ev)).append (NetE msg)).at? tr.length : Option E₂) =
        (TraceEntryHas.proj (TraceEntryHas.inj (EvE ev) : ExecTrace.Entry)) :=
    fun {_ _} => by rw [at?_append_lt _ _ hlt, at?_append_length]
  have hA1 : ∀ {E₂ : Type} [ExecTraceTypes.Has E₂],
      (((tr.append (EvE ev)).append (NetE msg)).at? (tr.length + 1) : Option E₂) =
        (TraceEntryHas.proj (TraceEntryHas.inj (NetE msg) : ExecTrace.Entry)) :=
    fun {_ _} => by
      rw [show tr.length + 1 = (tr.append (EvE ev)).length from by
        simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]]
      exact at?_append_length _ _
  have hmsg : ((tr.append (EvE ev)).append (NetE msg)).getMessageSentAt (tr.length + 1) =
      some msg := by
    simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hA1, proj_inj_eq]
  have hpq0 : ((tr.append (EvE ev)).append (NetE msg)).getEventAt PQXDHEvent tr.length =
      some ev := by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hA0, proj_inj_eq]
  have hpq1 : ((tr.append (EvE ev)).append (NetE msg)).getEventAt PQXDHEvent (tr.length + 1) =
      none := by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hA1]; rfl
  have htr0 : ((tr.append (EvE ev)).append (NetE msg)).getEventAt TREvent tr.length = none := by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hA0]; rfl
  have htr1 : ((tr.append (EvE ev)).append (NetE msg)).getEventAt TREvent (tr.length + 1) =
      none := by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hA1]; rfl
  simp only [List.filterMap_cons, List.filterMap_nil, pqExposureAt, trExposureAt, hpq0, hpq1,
    htr1, htr0, hmsg, Option.toList_some]
  cases ev <;> simp_all [pqLeakKind]

theorem appendsOnlyExposure_pq_pair (t : ExecTrace) (ev : PQXDHEvent) (msg : DY.Bytes) :
    AppendsOnlyExposure t ((t.append (EvE ev)).append (NetE msg)) := by
  refine ⟨Trace.le_trans _ _ _ (Trace.append_le _ _) (Trace.append_le _ _), fun i h hi => ?_⟩
  have hlen : ((t.append (EvE ev)).append (NetE msg)).length = t.length + 2 := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rcases (show i = t.length ∨ i = t.length + 1 by omega) with rfl | rfl
  · have : ((t.append (EvE ev)).append (NetE msg)).at t.length h =
        TraceEntryHas.inj (EvE ev) := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [this]; exact ⟨rfl, fun _ he => by cases he⟩
  · have : ((t.append (EvE ev)).append (NetE msg)).at (t.length + 1) h =
        TraceEntryHas.inj (NetE msg) := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [this]; exact ⟨rfl, fun _ he => by cases he⟩

def IsCompromiseMove : Move → Prop
  | .compromiseIK .. | .compromiseSPK .. | .compromisePQSPK .. | .compromiseOPK .. => True
  | _ => False

private theorem run_discard_snd {α : Type} (x : Traceful α) (tr : ExecTrace) :
    ((do let _ ← x; pure ()).run tr).2.val = (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, t⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

/-- The key a compromise move reads (by kind) and the event it logs. -/
def compromiseShape : Move → Option (Participant × Nat × DY.Libsignal.PQXDH.KeyKind ×
    (DY.Bytes → PQXDHEvent))
  | .compromiseIK p i => some (p, i, .identity, fun sk => .CompromisedIK p (DY.DiffieHellman.dhPk sk))
  | .compromiseSPK b i =>
    some (b, i, .signedPrekey, fun sk => .CompromisedSPK b (DY.DiffieHellman.dhPk sk))
  | .compromisePQSPK b i => some (b, i, .pqPrekey, fun sk => .CompromisedPQSPK b (DY.PQKem.kemPk sk))
  | .compromiseOPK b i =>
    some (b, i, .oneTimePrekey, fun sk => .CompromisedOPK b (DY.DiffieHellman.dhPk sk))
  | _ => none

theorem compromise_next {m : Move} {p : Participant} {i : Nat}
    {kind : DY.Libsignal.PQXDH.KeyKind} {mk : DY.Bytes → PQXDHEvent} {tr : ExecTrace}
    {sk : DY.Bytes} (hm : compromiseShape m = some (p, i, kind, mk))
    (hst : tr.at? i = some (StE p { kind, sk }))
    (hguard : m = .compromiseOPK p i →
      DY.Libsignal.PQXDH.opkUsedB tr p (DY.DiffieHellman.dhPk sk) = false := by exact nofun) :
    m.next tr = (tr.append (EvE (mk sk))).append (NetE sk) := by
  cases m <;> simp only [compromiseShape, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hm <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hm <;>
    (unfold Move.next Move.act; rw [run_discard_snd])
  · unfold DY.Libsignal.PQXDH.compromiseIK
    exact (Runs.bind (Runs.getKey hst) (Runs.bind (Runs.logEvent _ _) (Runs.sendMessage _ _))).2
  · unfold DY.Libsignal.PQXDH.compromiseSPK
    exact (Runs.bind (Runs.getKey hst) (Runs.bind (Runs.logEvent _ _) (Runs.sendMessage _ _))).2
  · unfold DY.Libsignal.PQXDH.compromisePQSPK
    exact (Runs.bind (Runs.getKey hst) (Runs.bind (Runs.logEvent _ _) (Runs.sendMessage _ _))).2
  · unfold DY.Libsignal.PQXDH.compromiseOPK
    exact (Runs.bind (Runs.getKey hst) (Runs.bind
      (Runs.requireTracePredicate (by simp [hguard rfl]))
      (Runs.bind (Runs.logEvent _ _) (Runs.sendMessage _ _)))).2

theorem compromise_vis {m : Move} {p : Participant} {i : Nat}
    {kind : DY.Libsignal.PQXDH.KeyKind} {mk : DY.Bytes → PQXDHEvent} {tr : ExecTrace}
    {sk : DY.Bytes} {pq : Bool} (hm : compromiseShape m = some (p, i, kind, mk))
    (hst : tr.at? i = some (StE p { kind, sk })) (hk : pqLeakKind (mk sk) = some pq)
    (hguard : m = .compromiseOPK p i →
      DY.Libsignal.PQXDH.opkUsedB tr p (DY.DiffieHellman.dhPk sk) = false := by exact nofun) :
    m.vis tr = [⟨.leak, [sk], .leakPq pq, some tr.length⟩] := by
  have hnext := compromise_next hm hst hguard
  cases m <;> simp only [compromiseShape, reduceCtorEq] at hm <;>
    (unfold Move.vis; dsimp only [List.nil_append]; rw [hnext]) <;>
    exact exposures_append_pq_pair tr _ sk pq hk

theorem compromise_isSetup {m : Move} (hm : IsCompromiseMove m) : m.isSetup = false := by
  cases m <;> cases hm <;> rfl

theorem compromise_anchored {m : Move} (hm : IsCompromiseMove m) (tr : ExecTrace) :
    m.LogsSessionCompletion tr := by
  cases m <;> cases hm <;> trivial

theorem compromise_reachable {m : Move} (hm : IsCompromiseMove m) {tr : ExecTrace}
    (hreach : tr.Reachable reachability) : (m.next tr).Reachable reachability := by
  cases m <;> cases hm <;> rename_i p idx
  · unfold Move.next Move.act; rw [run_discard_snd]
    exact (Traceful.PreservesReachability_base DY.Libsignal.PQXDH.compromiseIK.reachability
      reachability (p, idx) tr hreach trivial).1
  · unfold Move.next Move.act; rw [run_discard_snd]
    exact (Traceful.PreservesReachability_base DY.Libsignal.PQXDH.compromiseSPK.reachability
      reachability (p, idx) tr hreach trivial).1
  · unfold Move.next Move.act; rw [run_discard_snd]
    exact (Traceful.PreservesReachability_base DY.Libsignal.PQXDH.compromisePQSPK.reachability
      reachability (p, idx) tr hreach trivial).1
  · unfold Move.next Move.act; rw [run_discard_snd]
    exact (Traceful.PreservesReachability_base DY.Libsignal.PQXDH.compromiseOPK.reachability
      reachability (p, idx) tr hreach trivial).1

theorem modelRun_snoc_compromise {r : ProtocolSetup} {ms : List Move} {m : Move}
    (hm : IsCompromiseMove m) (hrun : ModelRun r ms) : ModelRun r (ms ++ [m]) := by
  refine modelRun_snoc_of r ms m hrun (compromise_isSetup hm)
    (compromise_reachable hm hrun.2.2.1.1) (compromise_anchored hm _) ?_ ?_
    (by cases m <;> cases hm <;> trivial) (by cases m <;> cases hm <;> rfl) <;>
    cases m <;> cases hm <;> simp [compromisesCurrentFrom, ownSaltsFrom]

local macro "peel_setup_at" : tactic => `(tactic|
  (simp only [setupTr5, setupTr4, setupTr3, setupTr2, setupTr1]
   repeat (first
     | (rw [at?_append_of_lt _ _ ?hlt]; case hlt => simp [Trace.append, Trace.length])
     | exact at?_append_eq _ _ rfl)))

theorem setupTrace_state_entries (r : ProtocolSetup) (hne : r.alice ≠ r.bob) :
    (setupTrace r).at? 4 = some (StE r.alice { kind := .identity, sk := setupSecret r 0 }) ∧
    (setupTrace r).at? 9 = some (StE r.bob { kind := .identity, sk := setupSecret r 1 }) ∧
    (setupTrace r).at? 13 = some (StE r.bob { kind := .signedPrekey, sk := setupSecret r 2 }) ∧
    (setupTrace r).at? 19 = some (StE r.bob { kind := .pqPrekey, sk := setupSecret r 4 }) ∧
    (r.withOpk = true →
      (setupTrace r).at? 24 = some (StE r.bob { kind := .oneTimePrekey, sk := setupSecret r 6 })) := by
  obtain ⟨h0, h1, h2, h4, h6⟩ := setupSecret_eq r hne
  rw [h0, h1, h2, h4, setupTrace_eq r hne]
  refine ⟨?_, ?_, ?_, ?_, fun hopk => ?_⟩
  · split <;> (simp only [setupTr5, setupTr4, setupTr3, setupTr2, setupTr1]
               repeat (first
                 | (rw [at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
                 | exact at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])))
  · split <;> (simp only [setupTr5, setupTr4, setupTr3, setupTr2, setupTr1]
               repeat (first
                 | (rw [at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
                 | exact at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])))
  · split <;> (simp only [setupTr5, setupTr4, setupTr3, setupTr2, setupTr1]
               repeat (first
                 | (rw [at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
                 | exact at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])))
  · split <;> (simp only [setupTr5, setupTr4, setupTr3, setupTr2, setupTr1]
               repeat (first
                 | (rw [at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
                 | exact at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])))
  · rw [h6 hopk]; simp only [hopk, ↓reduceIte]
    simp only [setupTr5, setupTr4, setupTr3, setupTr2, setupTr1]
    repeat (first
      | (rw [at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
      | exact at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]))

private theorem at?_some_of_le {E : Type} [ExecTraceTypes.Has E] {t T : ExecTrace} (hle : t ≤ T)
    {j : Nat} {x : E} (h : (t.at? j : Option E) = some x) : (T.at? j : Option E) = some x := by
  by_cases hj : j < t.length
  · have hj' : j < T.length := Nat.lt_of_lt_of_le hj (Trace.length_le t T hle)
    rw [← h]
    simp only [Trace.at?, hj, hj', ↓reduceDIte]
    rw [← Trace.at_le t T j hj hle]
  · simp [Trace.at?, hj] at h

theorem runTrace_state_entries (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move) :
    (runTraceMoves r ms).at? 4 = some (StE r.alice { kind := .identity, sk := setupSecret r 0 }) ∧
    (runTraceMoves r ms).at? 9 = some (StE r.bob { kind := .identity, sk := setupSecret r 1 }) ∧
    (runTraceMoves r ms).at? 13 = some (StE r.bob { kind := .signedPrekey, sk := setupSecret r 2 }) ∧
    (runTraceMoves r ms).at? 19 = some (StE r.bob { kind := .pqPrekey, sk := setupSecret r 4 }) ∧
    (r.withOpk = true →
      (runTraceMoves r ms).at? 24 = some (StE r.bob { kind := .oneTimePrekey, sk := setupSecret r 6 })) := by
  have hle := setupTrace_le_runTrace r ms
  obtain ⟨h4, h9, h13, h19, h24⟩ := setupTrace_state_entries r hne
  exact ⟨at?_some_of_le hle h4, at?_some_of_le hle h9, at?_some_of_le hle h13, at?_some_of_le hle h19,
    fun hopk => at?_some_of_le hle (h24 hopk)⟩

theorem setupPublic_8_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) (hOpk : r.withOpk = true) :
    setupPublic r 8 = DY.DiffieHellman.dhPk (setupSecret r 6) := by
  obtain ⟨_, _, _, _, hs6⟩ := setupSecret_eq r hNe
  rw [hs6 hOpk]
  have hlen5 : (setupTr5 r.alice r.bob).length = 26 := by
    simp only [setupTr5, setupTr4, setupTr3, setupTr2, setupTr1,
      Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hr26 : List.range' 0 (26 - 0) =
      [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25] := rfl
  rw [setupPublic, setupSent, setupTrace_eq r hNe]
  simp only [hOpk, ↓reduceIte, newIndices,
    Symbolic.DYBridge.DY.Trace.length_eq_1, hlen5, hr26,
    List.filterMap_cons, List.filterMap_nil]
  simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1,
    setupTr5, setupTr4, setupTr3, setupTr2, setupTr1,
    Symbolic.DYBridge.DY.Trace.append_eq_1,
    DY.Trace.at?, Symbolic.DYBridge.DY.Trace.at_eq_2,
    Symbolic.DYBridge.DY.Trace.length_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2]
  rfl

/-- The setup-secret disjuncts of `LeakableSecret`. -/
def SetupLeak (r : ProtocolSetup) (opkUsed : Bool) (k : HwBytes) : Prop :=
  k = secretBytes r 0 ∨ k = secretBytes r 1 ∨ k = secretBytes r 2 ∨ k = r.kyberSecB ∨
    (r.withOpk = true ∧ opkUsed = false ∧ k = secretBytes r 6)

theorem leakableSecret_cases {r : ProtocolSetup} {records : Participant → Option HwBytes} {used : Bool}
    {k : HwBytes} (h : LeakableSecret r records used k) :
    SetupLeak r used k ∨ ∃ p rec, records p = some (recordBytes rec) ∧ KeyInRecord rec k := by
  rcases h with h | (h | h | h | h) | h
  exacts [.inl (.inr (.inr (.inr (.inl h)))), .inl (.inl h), .inl (.inr (.inl h)),
    .inl (.inr (.inr (.inl h))), .inl (.inr (.inr (.inr (.inr h)))), .inr h]

/-- Every `.leak k` event of a `SetupLeak` secret extends `ms` by a single PQXDH compromise move
preserving `MatchedPrefix` and satisfying `AppendsOnlyExposure`. -/
theorem setupLeak_step {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost}
    {ms : List Move} {acc : List MachineEvent} {used : Bool} {k : HwBytes}
    (hne : r.alice ≠ r.bob) (hmp : MatchedPrefix interpretation r S who g ms acc)
    (hleak : SetupLeak r used k)
    (hopk_unused : r.withOpk = true → used = false →
      DY.Libsignal.PQXDH.opkUsedB (runTraceMoves r ms) r.bob (setupPublic r 8) = false) :
    ∃ m, IsCompromiseMove m ∧
      MatchedPrefix interpretation r S who g (ms ++ [m]) (acc ++ [.leak k]) ∧
      AppendsOnlyExposure (runTraceMoves r ms) (runTraceMoves r (ms ++ [m])) := by
  obtain ⟨hst4, hst9, hst13, hst19, hst24⟩ := runTrace_state_entries r hne ms
  obtain ⟨hg0, hg1, hg2, _, hg6⟩ := gamma_setupSecret interpretation r S g hmp.1 hne
  have hexp : ∀ m, IsCompromiseMove m → ∀ {p i kind mk sk},
      compromiseShape m = some (p, i, kind, mk) →
      (runTraceMoves r ms).at? i = some (StE p { kind, sk }) →
      (m = .compromiseOPK p i →
        DY.Libsignal.PQXDH.opkUsedB (runTraceMoves r ms) p (DY.DiffieHellman.dhPk sk) = false) →
      AppendsOnlyExposure (runTraceMoves r ms) (runTraceMoves r (ms ++ [m])) := by
    intro m _ p i kind mk sk hm hst hguard
    rw [runTrace_snoc, compromise_next hm hst hguard]
    exact appendsOnlyExposure_pq_pair _ _ _
  have hnocs : ∀ {x : HwBytes}, ∀ ev ∈ ([MachineEvent.leak x] : List MachineEvent),
      eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt := by
    intro x ev hev; rw [List.mem_singleton.mp hev]; simp [eventKind]
  rcases hleak with rfl | rfl | rfl | rfl | ⟨hopk, hused, rfl⟩
  · refine ⟨.compromiseIK r.alice 4, trivial,
      matchedPrefix_snoc_env hmp (modelRun_snoc_compromise trivial hmp.2.1) rfl rfl hnocs
        (by rw [compromise_vis rfl hst4 rfl]; simp) ?_,
      hexp _ trivial rfl hst4 nofun⟩
    rw [compromise_vis rfl hst4 rfl]
    exact .cons ⟨rfl, congrArg (· :: []) hg0⟩ .nil
  · refine ⟨.compromiseIK r.bob 9, trivial,
      matchedPrefix_snoc_env hmp (modelRun_snoc_compromise trivial hmp.2.1) rfl rfl hnocs
        (by rw [compromise_vis rfl hst9 rfl]; simp) ?_,
      hexp _ trivial rfl hst9 nofun⟩
    rw [compromise_vis rfl hst9 rfl]
    exact .cons ⟨rfl, congrArg (· :: []) hg1⟩ .nil
  · refine ⟨.compromiseSPK r.bob 13, trivial,
      matchedPrefix_snoc_env hmp (modelRun_snoc_compromise trivial hmp.2.1) rfl rfl hnocs
        (by rw [compromise_vis rfl hst13 rfl]; simp) ?_,
      hexp _ trivial rfl hst13 nofun⟩
    rw [compromise_vis rfl hst13 rfl]
    exact .cons ⟨rfl, congrArg (· :: []) hg2⟩ .nil
  · refine ⟨.compromisePQSPK r.bob 19, trivial,
      matchedPrefix_snoc_env hmp (modelRun_snoc_compromise trivial hmp.2.1) rfl rfl hnocs
        (by rw [compromise_vis rfl hst19 rfl]; simp) ?_,
      hexp _ trivial rfl hst19 nofun⟩
    rw [compromise_vis rfl hst19 rfl]
    exact .cons ⟨rfl, rfl⟩ .nil
  · have hopk_guard : DY.Libsignal.PQXDH.opkUsedB (runTraceMoves r ms) r.bob
        (DY.DiffieHellman.dhPk (setupSecret r 6)) = false := by
      rw [← setupPublic_8_eq r hne hopk]
      exact hopk_unused hopk hused
    refine ⟨.compromiseOPK r.bob 24, trivial,
      matchedPrefix_snoc_env hmp (modelRun_snoc_compromise trivial hmp.2.1) rfl rfl hnocs
        (by rw [compromise_vis rfl (hst24 hopk) rfl (fun _ => hopk_guard)]; simp) ?_,
      hexp _ trivial rfl (hst24 hopk) (fun _ => hopk_guard)⟩
    rw [compromise_vis rfl (hst24 hopk) rfl (fun _ => hopk_guard)]
    exact .cons ⟨rfl, congrArg (· :: []) (hg6 hopk)⟩ .nil

end Symbolic.Swarm.CREF.TR
