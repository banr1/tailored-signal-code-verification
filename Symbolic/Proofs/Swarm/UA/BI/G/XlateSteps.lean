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
public import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Translation Accumulator Step Lemmas

Defines the translation accumulator `AccInv` relating step-level `MatchesEvents` traces to
move-level `Clean` traces over `flatEvents`, and proves accumulator extension lemmas for invisible
network steps, DH/KEM inversion steps, and DH/KEM break steps.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.G.XlateSteps

open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
cref_hide_foreign_instances

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Traceful)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF (SemReady)
open Symbolic.Proofs.Swarm.UA.Defs (flatEvents SchedFits)
open Symbolic.Proofs.Swarm.UA.XlateSteps (VisSendPtEq visSendPtEq_append
  step_reachable invisible_eq_network attackerSend_next_eq_network
  NoReadColAt noReadColAt_snoc honestKeysFrom_append honestKeysOf_append
  PrekeyCallsPos prekeyCallsPos_snoc OutcomeFaithfulCli2 outcomeFaithfulCli2_snoc
  rngLengthsFaithfulCli_snoc StateLoadSub stateLoadSub_append_steps stateLoadSub_snoc_none)
open Symbolic.Proofs.Swarm.UA.BI.Step (next_network next_breakDH next_breakKEM
  next_invertDH_eq ok_invertDH_eq next_invertKEM_eq ok_invertKEM_eq matchesEvents_snoc_env)

/-! ## Accumulator and Invisible Steps -/

theorem matchesEventsAt_append_invisible {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pre : List Step} (hinv : ∀ x ∈ pre, x.cls = .invisible) :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
      {evs : List CliEvent} {vis : List VisEntry},
      MatchesEventsAt interp r S g initIds tr ss evs vis →
      MatchesEventsAt interp r S g initIds tr (ss ++ pre) evs vis
  | _, _, ss, _, _, .nil h => .nil fun x hx =>
    (List.mem_append.mp hx).elim (h x) (hinv x)
  | _, _, _, _, _, .run1 hp hrm hrest => by
    simpa [List.append_assoc] using
      MatchesEventsAt.run1 hp hrm (matchesEventsAt_append_invisible hinv hrest)
  | _, _, _, _, _, .run0 hp hrej hrest => by
    simpa [List.append_assoc] using
      MatchesEventsAt.run0 hp hrej (matchesEventsAt_append_invisible hinv hrest)
  | _, _, _, _, _, .env hp hem hrest => by
    simpa [List.append_assoc] using
      MatchesEventsAt.env hp hem (matchesEventsAt_append_invisible hinv hrest)

theorem matchesEvents_append_invisible {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pre : List Step} (hinv : ∀ x ∈ pre, x.cls = .invisible)
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEvents interp r S g tr ss evs vis) :
    MatchesEvents interp r S g tr (ss ++ pre) evs vis :=
  matchesEventsAt_append_invisible hinv h

/-- Translation accumulator relating a clean move trace `(τ, ms)` on `flatEvents evs_acc` to a
step trace `(ss_acc, vis_acc)` matching `evs_acc` with identical `runTrace`, honest keys, and
send/plaintext terms. -/
structure AccInv (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost)
    (evs_acc : List CliEvent) (ss_acc : List Step) (vis_acc : List VisEntry)
    (τ : List MachineEvent) (ms : List Move) : Prop where
  cs : CoinSplit (flatEvents evs_acc) τ
  clean : Clean interp r S who ok g ms τ
  nr : NoReadColAt interp r S g ms τ
  ppos : PrekeyCallsPos r ms
  out2 : OutcomeFaithfulCli2 r ok ms
  rng32 : RngLengthsFaithfulCli interp r S g ms
  tr_eq : runTraceMoves r ms = runTrace r ss_acc
  keys_eq : honestKeysFrom (setupTrace r) ms = honestKeysOf (setupTrace r) ss_acc
  vpt : VisSendPtEq (runVis r ms) vis_acc
  mev : MatchesEvents interp r S g (setupTrace r) ss_acc evs_acc vis_acc
  sload : StateLoadSub r ms ss_acc

theorem accInv_nil {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (hwf : ProtocolSetupWF r) (hS : SemReady interp r S) (who : List Participant) (ok : Nat → Bool)
    {g : Ghost} (hcompat : GhostAndSemMatchSetup interp r S g) :
    AccInv interp r S who ok g [] [] [] [] [] := by
  have h := Symbolic.Proofs.Swarm.UA.XlateSteps.accInv_nil hwf hS who ok hcompat
  exact ⟨h.cs, h.clean, h.nr, h.ppos, h.out2, h.rng32, h.tr_eq, h.keys_eq, h.vpt,
    .nil (fun _ hx => nomatch hx), h.sload⟩

/-- Extends `AccInv` by a move `m` with no visible entries and a step `s` with the same next trace
whose CLI events flatten to `[]`. -/
theorem accInv_step_hidden {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {evs_acc evs_new : List CliEvent} {ss_acc : List Step} {vis_acc v : List VisEntry}
    {τ : List MachineEvent} {ms : List Move} {m : Move} {s : Step}
    (h : AccInv interp r S who ok g evs_acc ss_acc vis_acc τ ms)
    (hnext : m.next (runTraceMoves r ms) = s.next (runTraceMoves r ms))
    (hvis : m.vis (runTraceMoves r ms) = [])
    (hppath : m.prekeyPath? = none) (hsload : m.stateLoad? = none)
    (hkm : ∀ tr : ExecTrace, honestKeysFrom tr [m] = [])
    (hks : ∀ tr : ExecTrace, honestKeysOf tr [s] = [])
    (hfe : flatEvents evs_new = [])
    (hvpt : VisSendPtEq [] v)
    (hcl : Clean interp r S who ok g (ms ++ [m]) τ)
    (hmev : MatchesEvents interp r S g (setupTrace r) (ss_acc ++ [s]) (evs_acc ++ evs_new)
      (vis_acc ++ v)) :
    AccInv interp r S who ok g (evs_acc ++ evs_new) (ss_acc ++ [s]) (vis_acc ++ v) τ
      (ms ++ [m]) := by
  refine ⟨?_, hcl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmev, ?_⟩
  · rw [Symbolic.Proofs.Swarm.UA.Base.flatEvents_append, hfe, List.append_nil]
    exact h.cs
  · simpa using noReadColAt_snoc (m := m) (blk := []) h.clean.1.1 h.nr
      (fun _ _ hb => nomatch hb)
  · exact prekeyCallsPos_snoc h.ppos (fun hp => by rw [hppath] at hp; cases hp)
  · exact outcomeFaithfulCli2_snoc h.out2 (by simp [hvis])
  · exact rngLengthsFaithfulCli_snoc h.rng32 (by simp [hvis])
  · rw [runTrace_snoc, Symbolic.Proofs.Swarm.UA.Base.runTrace_append, runSteps, runSteps,
      hnext, h.tr_eq]
  · rw [honestKeysFrom_append, honestKeysOf_append, hkm, hks, h.keys_eq]
  · rw [runVis_snoc, hvis]
    exact visSendPtEq_append h.vpt hvpt
  · exact stateLoadSub_append_steps (stateLoadSub_snoc_none h.sload hsload) [s]

theorem accInv_step_network {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {evs_acc : List CliEvent} {ss_acc : List Step} {vis_acc : List VisEntry}
    {τ : List MachineEvent} {ms : List Move} (msg : _root_.DY.Bytes)
    (hpre : (Step.network msg).PreCond (runTrace r ss_acc))
    (h : AccInv interp r S who ok g evs_acc ss_acc vis_acc τ ms) :
    AccInv interp r S who ok g evs_acc (ss_acc ++ [.network msg]) vis_acc τ
      (ms ++ [.attackerSend msg]) := by
  have hreach' : (runTraceMoves r (ms ++ [.attackerSend msg])).Reachable reachability := by
    rw [runTrace_snoc, attackerSend_next_eq_network, h.tr_eq]
    exact step_reachable (by rw [← h.tr_eq]; exact h.clean.1.1.2.1.2.2.1.1) hpre
  have hcl' : Clean interp r S who ok g (ms ++ [.attackerSend msg]) τ :=
    clean_attackerSend h.clean hreach'
  have hvis_nil : (Move.attackerSend msg).vis (runTraceMoves r ms) = [] := by
    have hlen1 := h.clean.1.1.2.2.2.2.2.length_eq
    have hlen2 := hcl'.1.1.2.2.2.2.2.length_eq
    rw [runVis_snoc, List.length_append] at hlen2
    exact List.eq_nil_of_length_eq_zero (by omega)
  have h' := accInv_step_hidden (evs_new := []) (v := []) h
    (attackerSend_next_eq_network msg _) hvis_nil rfl rfl
    (fun _ => rfl) (fun _ => rfl) rfl ⟨rfl, rfl⟩ hcl'
    (by
      simpa only [List.append_nil] using matchesEvents_append_invisible
        (pre := [.network msg]) (fun x hx => by rcases List.mem_singleton.mp hx with rfl; rfl)
        h.mev)
  simpa only [List.append_nil] using h'

theorem accInv_step_invisible_list {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {evs_acc : List CliEvent} :
    ∀ {pre rest : List Step} (_hinv : ∀ x ∈ pre, x.cls = .invisible)
      {ss_acc : List Step} (_hwf : StepsWF (pre ++ rest) (runTrace r ss_acc))
      {vis_acc : List VisEntry} {τ : List MachineEvent} {ms : List Move},
      AccInv interp r S who ok g evs_acc ss_acc vis_acc τ ms →
      ∃ ms', AccInv interp r S who ok g evs_acc (ss_acc ++ pre) vis_acc τ ms'
  | [], _, _, _, _, _, _, ms, h => ⟨ms, by simpa using h⟩
  | s :: pre, rest, hinv, ss_acc, hwf, vis_acc, τ, ms, h => by
    obtain ⟨msg, rfl⟩ := invisible_eq_network (hinv s (List.mem_cons_self ..))
    have h1 := accInv_step_network msg hwf.1 h
    have hwf' : StepsWF (pre ++ rest) (runTrace r (ss_acc ++ [.network msg])) := by
      simpa [Symbolic.Proofs.Swarm.UA.Base.runTrace_append, runSteps] using hwf.2.2
    obtain ⟨ms', h2⟩ := accInv_step_invisible_list (rest := rest)
      (fun x hx => hinv x (List.mem_cons_of_mem _ hx)) hwf' h1
    exact ⟨ms', by simpa [List.append_assoc] using h2⟩

/-! ## Invert Steps -/

private theorem receiveMessage_run (pkIdx : Nat) (tr : ExecTrace) :
    ((_root_.DY.Network.receiveMessage pkIdx).run tr).1 =
        (tr.at? pkIdx : Option _root_.DY.Network.ExecEntryT).map (·.msg) ∧
      ((_root_.DY.Network.receiveMessage pkIdx).run tr).2.val = tr := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Traceful.run_bind,
    Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  dsimp only
  cases (tr.at? pkIdx : Option _root_.DY.Network.ExecEntryT) with
  | none => exact ⟨rfl, rfl⟩
  | some e => dsimp only; rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩

private theorem invertDH_run {pkIdx : Nat} {tr : ExecTrace}
    (hok : ((_root_.DY.Libsignal.PQXDH.invertDH pkIdx).run tr).1.isSome = true) :
    ∃ sk : _root_.DY.Bytes, ((_root_.DY.Libsignal.PQXDH.invertDH pkIdx).run tr).2.val =
      tr.append (⟨sk⟩ : _root_.DY.Network.ExecEntryT) := by
  unfold _root_.DY.Libsignal.PQXDH.invertDH at hok ⊢
  rw [Traceful.run_bind] at hok ⊢
  have hg2 : ((_root_.DY.Libsignal.TripleRatchet.guardTrace
      _root_.DY.Libsignal.PQXDH.brokenDHB).run tr).2.val = tr := by
    unfold _root_.DY.Libsignal.TripleRatchet.guardTrace
    rw [Traceful.run_mk]
  rcases hg : (_root_.DY.Libsignal.TripleRatchet.guardTrace _root_.DY.Libsignal.PQXDH.brokenDHB).run tr
    with ⟨og, tg, _⟩
  rw [hg] at hg2 hok
  dsimp only at hg2 hok ⊢
  subst hg2
  rcases og with _ | ⟨⟩
  · simp at hok
  · dsimp only at hok ⊢
    rw [Traceful.run_bind] at hok ⊢
    have hr2 := (receiveMessage_run pkIdx tg).2
    rcases hr : (_root_.DY.Network.receiveMessage pkIdx).run tg with ⟨or_, tr_, _⟩
    rw [hr] at hr2 hok
    dsimp only at hr2 hok ⊢
    subst hr2
    rcases or_ with _ | pk
    · simp at hok
    · dsimp only at hok ⊢
      cases hsk : _root_.DY.Libsignal.PQXDH.extractDhSecretKey (_root_.DY.X25519.normalizeX25519Key pk) with
      | none => simp [hsk, Traceful.run_failure] at hok
      | some sk =>
        refine ⟨sk, ?_⟩
        dsimp only
        rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]

private theorem invertKEM_run {pkIdx : Nat} {tr : ExecTrace}
    (hok : ((_root_.DY.Libsignal.PQXDH.invertKEM pkIdx).run tr).1.isSome = true) :
    ∃ sk : _root_.DY.Bytes, ((_root_.DY.Libsignal.PQXDH.invertKEM pkIdx).run tr).2.val =
      tr.append (⟨sk⟩ : _root_.DY.Network.ExecEntryT) := by
  unfold _root_.DY.Libsignal.PQXDH.invertKEM at hok ⊢
  rw [Traceful.run_bind] at hok ⊢
  have hg2 : ((_root_.DY.Libsignal.TripleRatchet.guardTrace
      _root_.DY.Libsignal.PQXDH.brokenKEMB).run tr).2.val = tr := by
    unfold _root_.DY.Libsignal.TripleRatchet.guardTrace
    rw [Traceful.run_mk]
  rcases hg : (_root_.DY.Libsignal.TripleRatchet.guardTrace _root_.DY.Libsignal.PQXDH.brokenKEMB).run tr
    with ⟨og, tg, _⟩
  rw [hg] at hg2 hok
  dsimp only at hg2 hok ⊢
  subst hg2
  rcases og with _ | ⟨⟩
  · simp at hok
  · dsimp only at hok ⊢
    rw [Traceful.run_bind] at hok ⊢
    have hr2 := (receiveMessage_run pkIdx tg).2
    rcases hr : (_root_.DY.Network.receiveMessage pkIdx).run tg with ⟨or_, tr_, _⟩
    rw [hr] at hr2 hok
    dsimp only at hr2 hok ⊢
    subst hr2
    rcases or_ with _ | pk
    · simp at hok
    · dsimp only at hok ⊢
      rw [Traceful.run_bind] at hok ⊢
      have hl2 : ((liftM (_root_.DY.PQKem.invertKemPublicKey pk) : Traceful _root_.DY.Bytes).run
          tr_).2.val = tr_ := by
        erw [Traceful.run_mk]
      rcases hl : (liftM (_root_.DY.PQKem.invertKemPublicKey pk) : Traceful _root_.DY.Bytes).run tr_
        with ⟨ol, tl, _⟩
      rw [hl] at hl2 hok
      dsimp only at hl2 hok ⊢
      subst hl2
      rcases ol with _ | sk
      · simp at hok
      · refine ⟨sk, ?_⟩
        dsimp only
        rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]

theorem exists_network_next_of_invert {s : Step} {tr : ExecTrace}
    (hs : (∃ h, s = .invertDH h) ∨ ∃ h, s = .invertKEM h) (hok : s.ok tr = true) :
    ∃ sk : _root_.DY.Bytes, s.next tr = (Step.network sk).next tr := by
  rcases hs with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · rw [ok_invertDH_eq] at hok
    obtain ⟨sk, hsk⟩ := invertDH_run hok
    exact ⟨sk, by rw [next_invertDH_eq, next_network, hsk]⟩
  · rw [ok_invertKEM_eq] at hok
    obtain ⟨sk, hsk⟩ := invertKEM_run hok
    exact ⟨sk, by rw [next_invertKEM_eq, next_network, hsk]⟩

/-- Extends `AccInv` across a successful `invertDH` or `invertKEM` step by translating it to
`Move.attackerSend` of the inverted secret. -/
theorem accInv_step_invert {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {evs_acc : List CliEvent} {ev : EnvEvent} {s : Step} {ss_acc : List Step}
    {vis_acc v : List VisEntry} {τ : List MachineEvent} {ms : List Move}
    (hs : (∃ h, s = .invertDH h) ∨ ∃ h, s = .invertKEM h)
    (hok : s.ok (runTrace r ss_acc) = true)
    (hs_pre : s.PreCond (runTrace r ss_acc))
    (hfe : flatEvents [.env ev] = [])
    (hvpt : VisSendPtEq [] v)
    (hem : EnvMatches interp r S g (runTrace r ss_acc) s ev v)
    (h : AccInv interp r S who ok g evs_acc ss_acc vis_acc τ ms) :
    ∃ m, AccInv interp r S who ok g (evs_acc ++ [.env ev]) (ss_acc ++ [s]) (vis_acc ++ v) τ
      (ms ++ [m]) := by
  obtain ⟨sk, hsk⟩ := exists_network_next_of_invert hs hok
  have hnext : (Move.attackerSend sk).next (runTraceMoves r ms) = s.next (runTraceMoves r ms) := by
    rw [attackerSend_next_eq_network, h.tr_eq, hsk]
  have hreach' : (runTraceMoves r (ms ++ [.attackerSend sk])).Reachable reachability := by
    rw [runTrace_snoc, hnext, h.tr_eq]
    exact step_reachable (by rw [← h.tr_eq]; exact h.clean.1.1.2.1.2.2.1.1) hs_pre
  have hcl' : Clean interp r S who ok g (ms ++ [.attackerSend sk]) τ :=
    clean_attackerSend h.clean hreach'
  have hvis_nil : (Move.attackerSend sk).vis (runTraceMoves r ms) = [] := by
    have hlen1 := h.clean.1.1.2.2.2.2.2.length_eq
    have hlen2 := hcl'.1.1.2.2.2.2.2.length_eq
    rw [runVis_snoc, List.length_append] at hlen2
    exact List.eq_nil_of_length_eq_zero (by omega)
  have hks : ∀ tr : ExecTrace, honestKeysOf tr [s] = [] := by
    intro tr
    rcases hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  exact ⟨.attackerSend sk, accInv_step_hidden h hnext hvis_nil rfl rfl (fun _ => rfl) hks hfe
    hvpt hcl' (matchesEvents_snoc_env (pre := []) h.mev (fun _ hx => nomatch hx) hem)⟩

/-! ## Break Steps -/

/-- Specification of a move `m` corresponding to a `breakDH` or `breakKEM` step `s`: identical
next trace, no visible entries, valid non-setup move with no party, pre-key path, or state load,
not a reject move, free of colliding reads, and publishing no honest SPQR keys. -/
structure BrkMoveFor (m : Move) (s : Step) : Prop where
  next_eq : ∀ tr : ExecTrace, m.next tr = s.next tr
  vis_nil : ∀ tr : ExecTrace, m.vis tr = []
  move_ok : ∀ (r : ProtocolSetup) (tr : ExecTrace), MoveOK r m tr
  party_none : m.party? = none
  ppath_none : m.prekeyPath? = none
  sload_none : m.stateLoad? = none
  not_reject : ∀ ds, m ≠ .reject ds
  no_readcol : ∀ (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pre : List Move) (e : MachineEvent), ¬ MoveReadsCollidingMsg interp r S g pre e m
  keys_nil : ∀ tr : ExecTrace, honestKeysFrom tr [m] = []

/-- Existence of moves satisfying `BrkMoveFor` for `Step.breakDH` and `Step.breakKEM`. -/
def BrkMovesExist : Prop :=
  (∃ m, BrkMoveFor m .breakDH) ∧ ∃ m, BrkMoveFor m .breakKEM

theorem eventIdx_brk_none {s : Step} (hs : s = .breakDH ∨ s = .breakKEM)
    (p : _root_.DY.Libsignal.PQXDH.PQXDHEvent → Bool)
    (hpDH : p .BrokenDH = false) (hpKEM : p .BrokenKEM = false) (tr : ExecTrace) :
    eventIdx p tr (s.next tr) = none := by
  rcases hs with rfl | rfl
  · unfold eventIdx
    rw [next_breakDH]
    have hlen : (tr.append (⟨_root_.DY.Libsignal.PQXDH.PQXDHEvent.BrokenDH⟩ :
        _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.PQXDH.PQXDHEvent)).length =
        tr.length + 1 := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    simp [newIndices, hlen, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Symbolic.Swarm.CREF.TR.at?_append_self,
      hpDH]
  · unfold eventIdx
    rw [next_breakKEM]
    have hlen : (tr.append (⟨_root_.DY.Libsignal.PQXDH.PQXDHEvent.BrokenKEM⟩ :
        _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.PQXDH.PQXDHEvent)).length =
        tr.length + 1 := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    simp [newIndices, hlen, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Symbolic.Swarm.CREF.TR.at?_append_self,
      hpKEM]

/-- Extends `AccInv` across a `breakDH` or `breakKEM` step using a move satisfying `BrkMoveFor`. -/
theorem accInv_step_brk {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {evs_acc : List CliEvent} {ev : EnvEvent} {s : Step} {m : Move} {ss_acc : List Step}
    {vis_acc : List VisEntry} {τ : List MachineEvent} {ms : List Move}
    (hm : BrkMoveFor m s) (hs : s = .breakDH ∨ s = .breakKEM)
    (hs_pre : s.PreCond (runTrace r ss_acc))
    (hfe : flatEvents [.env ev] = [])
    (hem : EnvMatches interp r S g (runTrace r ss_acc) s ev [])
    (h : AccInv interp r S who ok g evs_acc ss_acc vis_acc τ ms) :
    AccInv interp r S who ok g (evs_acc ++ [.env ev]) (ss_acc ++ [s]) vis_acc τ (ms ++ [m]) := by
  have hreach' : (runTraceMoves r (ms ++ [m])).Reachable reachability := by
    rw [runTrace_snoc, hm.next_eq, h.tr_eq]
    exact step_reachable (by rw [← h.tr_eq]; exact h.clean.1.1.2.1.2.2.1.1) hs_pre
  have hmp' : MatchedPrefix interp r S who g (ms ++ [m]) τ :=
    matchedPrefix_snoc_hidden h.clean.1.1 (hm.move_ok r _) hreach' (hm.vis_nil _)
      hm.party_none hm.ppath_none hm.sload_none
  have hof' : OutcomeFaithful r ok (ms ++ [m]) :=
    outcomeFaithful_snoc_neutral h.clean.1.2 hm.not_reject (by
      rw [hm.next_eq]; exact eventIdx_brk_none hs _ rfl rfl _)
  have hnrc' : ¬ ReadCollision interp r S g (ms ++ [m]) τ := by
    simpa using not_readCollision_append_noAccept (ms' := [m]) (blk := []) h.clean.2
      (fun _ he => nomatch he)
      (fun m' hm' pre e => by
        rcases List.mem_singleton.mp hm' with rfl
        exact hm.no_readcol interp r S g pre e)
  have hks : ∀ tr : ExecTrace, honestKeysOf tr [s] = [] := by
    intro tr
    rcases hs with rfl | rfl <;> rfl
  have h' := accInv_step_hidden (evs_new := [.env ev]) (v := []) h (hm.next_eq _)
    (hm.vis_nil _) hm.ppath_none hm.sload_none hm.keys_nil hks hfe ⟨rfl, rfl⟩
    ⟨⟨hmp', hof'⟩, hnrc'⟩
    (matchesEvents_snoc_env (pre := []) h.mev (fun _ hx => nomatch hx) hem)
  simpa only [List.append_nil] using h'

end Symbolic.Proofs.Swarm.UA.BI.G.XlateSteps
