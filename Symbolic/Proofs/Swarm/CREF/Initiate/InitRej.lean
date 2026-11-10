/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Initiate.MidRngPure
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.Random
import DY.Actions.ProtocolEvent
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Mathlib.Data.Set.Operations
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# `session_initiate` Reject Explanations, `Runs` Calculus, and `gamma` Unfolding

Defines bundle OPK acceptance (`BundleOpkAccepted`) and Kyber entropy reconstruction
(`entropyBytes`), proves `MatchedPrefix` extension across `Move.reject`, and provides `Runs` monad
evaluators and `gamma` unfolding equations for `session_initiate`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY DY.Comparse
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent KeyKind)
open DY.Libsignal.TripleRatchet (TRState TREvent x25519LowOrder)
open DY.Libsignal.Refinement (x25519PublicKeySymbol)
open CryptoProofLib.Refinement (ExternInterpretation)

/-! ## Bundle OPK acceptance and Kyber entropy reconstruction -/

/-- Which X25519 DH leg returned all-zero shared secret during `session_initiate`. -/
inductive InitiateDhLeg where
  | dh1 | dh2 | dh3 | dh4
  deriving DecidableEq, Repr

theorem initiateFullDrawLengths_getD_succ {j : Nat} (hj : j < 32) :
    initiateFullDrawLengths.getD (j + 1) 0 = 4 := by
  unfold initiateFullDrawLengths
  revert j hj; decide

abbrev compHwLit (bs : HwBytes) : DY.Bytes := litOf bs

/-- A bundle's OPK field passes libsignal's `session_initiate` parsing and non-zero DH4 check:
either no OPK is present (`bundle[4]? = some 0`), or `bundle[4]? = some 1` with `0x05` Curve25519
tag at byte 9 and non-low-order 32-byte u-coordinate at bytes `10..42`. -/
def BundleOpkAccepted (bundle : HwBytes) : Prop :=
  bundle[4]? = some 0#8 ∨
    (bundle[4]? = some 1#8 ∧ bundle[9]? = some 5#8 ∧
      x25519LowOrder (litOf (slice bundle 10 32)) = false)

/-- Reconstructs the 32-byte Kyber encapsulation `entropy` from the 34 hardware draws `ds` of an ok
`session_initiate` call: byte `j` (`0 ≤ j < 32`) is byte `0` of the 4-byte draw `ds[j + 1]`. -/
def entropyBytes (ds : List HwBytes) : HwBytes :=
  (List.range 32).map fun j => (ds.getD (j + 1) []).getD 0 0#8

@[simp] theorem length_entropyBytes (ds : List HwBytes) :
    (entropyBytes ds).length = 32 := by
  simp [entropyBytes]

theorem getElem?_entropyBytes (ds : List HwBytes) {j : Nat} (hj : j < 32)
    (hd : (ds.getD (j + 1) []).length = 4) :
    (entropyBytes ds)[j]? = (ds.getD (j + 1) [])[0]? := by
  unfold entropyBytes
  rw [List.getElem?_map, List.getElem?_range hj, Option.map_some]
  rcases h : ds.getD (j + 1) [] with _ | ⟨b, bs⟩
  · rw [h] at hd; simp at hd
  · simp [List.getD]

theorem length_getD_of_map_length {ds : List HwBytes} {ns : List Nat}
    (h : ds.map List.length = ns) (i : Nat) :
    (ds.getD i []).length = ns.getD i 0 := by
  subst h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ds[i]? <;> rfl

theorem forall₂_of_getElem? {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (hlen : xs.length = ys.length)
    (h : ∀ (i : Nat) x y, xs[i]? = some x → ys[i]? = some y → R x y) :
    List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact .nil
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      exact .cons (h 0 x y rfl rfl) (ih hlen fun i a b ha hb => h (i + 1) a b ha hb)

/-! ## `runMoves`, `runVis`, and `Move.reject` algebra -/

theorem runTrace_eq_setup (r : ProtocolSetup) (ms : List Move) :
    runTraceMoves r ms = (runMoves ms (setupTrace r)).1 := by
  simp [runTraceMoves, setupMove_next_nil, runMoves]

theorem setupTrace_le_runTrace (r : ProtocolSetup) (ms : List Move) :
    setupTrace r ≤ runTraceMoves r ms := by
  rw [runTrace_eq_setup]
  exact runMoves_le ms (setupTrace r)

@[simp] theorem next_reject (draws : List Nat) (tr : ExecTrace) :
    (Move.reject draws).next tr = tr := by
  unfold Move.next Move.act
  simp only [DY.Traceful.run_pure]

@[simp] theorem anchored_reject (draws : List Nat) (tr : ExecTrace) :
    (Move.reject draws).LogsSessionCompletion tr = True := rfl

@[simp] theorem vis_reject (draws : List Nat) (tr : ExecTrace) :
    (Move.reject draws).vis tr =
      (⟨.recv, [], .unconstrained, none⟩ : VisEntry) ::
        draws.map fun n => (⟨.rng, [], .fresh n, none⟩ : VisEntry) := by
  simp [Move.vis, next_reject]

@[simp] theorem runTrace_snoc_reject (r : ProtocolSetup) (ms : List Move) (draws : List Nat) :
    runTraceMoves r (ms ++ [.reject draws]) = runTraceMoves r ms := by
  rw [runTrace_snoc, next_reject]

theorem runVis_snoc_reject (r : ProtocolSetup) (ms : List Move) (draws : List Nat) :
    runVis r (ms ++ [.reject draws]) =
      runVis r ms ++
        ((⟨.recv, [], .unconstrained, none⟩ : VisEntry) ::
          draws.map fun n => (⟨.rng, [], .fresh n, none⟩ : VisEntry)) := by
  rw [runVis_snoc, vis_reject]

theorem eventMatchesEntry_recv_unconstrained (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (b : HwBytes) :
    EventMatchesEntry interpretation r S g (.recv b) ⟨.recv, [], .unconstrained, none⟩ := by
  simp [EventMatchesEntry, eventKind]

theorem eventMatchesEntry_rng_fresh (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (d : HwBytes) :
    EventMatchesEntry interpretation r S g (.rng d) ⟨.rng, [], .fresh d.length, none⟩ := by
  simp [EventMatchesEntry, eventKind, eventBytes]

theorem ini_forall₂_rng_fresh (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ds : List HwBytes) :
    List.Forall₂ (EventMatchesEntry interpretation r S g) (ds.map MachineEvent.rng)
      ((ds.map List.length).map fun n => (⟨.rng, [], .fresh n, none⟩ : VisEntry)) := by
  induction ds with
  | nil => exact .nil
  | cons d ds ih => exact .cons (eventMatchesEntry_rng_fresh interpretation r S g d) ih

/-! ## Faithfulness combinators and `matchedPrefix_append_reject` -/

theorem callStarts_rng_map (ds : List HwBytes) :
    callStarts (ds.map MachineEvent.rng) = [] := by
  induction ds with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem callStarts_initiate_block (b : HwBytes) (ds : List HwBytes) :
    callStarts (.recv b :: ds.map MachineEvent.rng) = [.recv b] := by
  unfold callStarts
  simp only [List.filter_cons, eventKind, beq_self_eq_true, Bool.true_or, ↓reduceIte]
  exact congrArg (MachineEvent.recv b :: ·) (callStarts_rng_map ds)

/-- Every move in `ms` carrying `prekeyPath? = some promote` sits at a call index strictly below
`(callStarts acc).length` (holds after `Sanitize.clearStuckWrap` and on all non-stuck runs). -/
def PrekeyPathsInBounds (r : ProtocolSetup) (ms : List Move) (acc : List MachineEvent) : Prop :=
  ∀ (i : Nat) (m : Move) (promote : Bool),
    ms[i]? = some m → m.prekeyPath? = some promote →
    callCount (runVis r (ms.take i)) < (callStarts acc).length

theorem roleFaithful_snoc_of_party_none {r : ProtocolSetup} {who : List Participant}
    {ms : List Move} {m₀ : Move} (hm₀ : m₀.party? = none) (hrf : RoleFaithful r who ms) :
    RoleFaithful r who (ms ++ [m₀]) := by
  intro i m p hi hp
  rcases Nat.lt_or_ge i ms.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact hrf i m p hi hp
  · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
    · simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi; simp [hm₀] at hp
    · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi

theorem pathFaithful_snoc_initiate_of_prekeyPath_none {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    {m₀ : Move} (b : HwBytes) (ds : List HwBytes)
    (hm₀ : m₀.prekeyPath? = none)
    (hb : PrekeyPathsInBounds r ms acc)
    (hpf : PathFaithful interpretation r S g ms acc) :
    PathFaithful interpretation r S g (ms ++ [m₀]) (acc ++ (.recv b :: ds.map MachineEvent.rng)) := by
  intro i m promote b' p hi hpath hcall hparse
  rcases Nat.lt_or_ge i ms.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at hcall ⊢
    have hk := hb i m promote hi hpath
    rw [callStarts_append, callStarts_initiate_block, List.getElem?_append_left hk] at hcall
    exact hpf i m promote b' p hi hpath hcall hparse
  · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
    · simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi; simp [hm₀] at hpath
    · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi

theorem zip_append_of_eq_length {α β : Type} :
    ∀ {xs₁ xs₂ : List α} {ys₁ ys₂ : List β},
      xs₁.length = ys₁.length →
      (xs₁ ++ xs₂).zip (ys₁ ++ ys₂) = xs₁.zip ys₁ ++ xs₂.zip ys₂
  | [], _, [], _, _ => rfl
  | _ :: _, _, [], _, h => by simp at h
  | [], _, _ :: _, _, h => by simp at h
  | _ :: xs₁, xs₂, _ :: ys₁, ys₂, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [zip_append_of_eq_length h]

private theorem not_recv_mem_zip_rng :
    ∀ (ds : List HwBytes) (ev : MachineEvent × VisEntry),
      ev ∈ (ds.map MachineEvent.rng).zip
        ((ds.map List.length).map fun n => (⟨.rng, [], .fresh n, none⟩ : VisEntry)) →
      ev.2.kind ≠ .recv
  | [], _, h => by simp at h
  | _ :: ds, ev, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · intro hc; cases hc
    · exact not_recv_mem_zip_rng ds ev h

theorem readFaithful_snoc_reject {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent} (b : HwBytes) (ds : List HwBytes)
    (hlen : acc.length = (runVis r ms).length)
    (hrf : ReadFaithful interpretation r S g ms acc) :
    ReadFaithful interpretation r S g (ms ++ [.reject (ds.map List.length)])
      (acc ++ (.recv b :: ds.map MachineEvent.rng)) := by
  intro ev hev hkind
  rw [runVis_snoc_reject, zip_append_of_eq_length hlen, List.mem_append] at hev
  rcases hev with hev_pre | hev_blk
  · have hprev := hrf ev hev_pre hkind
    revert hprev
    cases ev.2.layout <;> simp [recvRepresentations, preKeyRepresentations, runTrace_snoc_reject]
  · simp only [List.zip_cons_cons, List.mem_cons] at hev_blk
    rcases hev_blk with rfl | hev_tail
    · trivial
    · exact absurd hkind (not_recv_mem_zip_rng ds ev hev_tail)

/-- Extends a `MatchedPrefix` explanation across a rejected `session_initiate` call emitting
`.recv bundle :: ds.map .rng`. -/
theorem matchedPrefix_append_reject {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (hM : MatchedPrefix interpretation r S who g ms τ)
    (hb : PrekeyPathsInBounds r ms τ)
    (bundle : HwBytes) (ds : List HwBytes) :
    MatchedPrefix interpretation r S who g (ms ++ [Move.reject (ds.map List.length)])
      (τ ++ (.recv bundle :: ds.map MachineEvent.rng)) := by
  obtain ⟨hcompat, hrun, hrole, hpath, hread, hvis⟩ := hM
  refine ⟨hcompat,
    modelRun_snoc_reject hrun (ds.map List.length),
    roleFaithful_snoc_of_party_none rfl hrole,
    pathFaithful_snoc_initiate_of_prekeyPath_none bundle ds rfl hb hpath,
    readFaithful_snoc_reject bundle ds hvis.length_eq hread,
    ?_⟩
  rw [runVis_snoc_reject]
  exact List.rel_append hvis (.cons
    (eventMatchesEntry_recv_unconstrained interpretation r S g bundle)
    (ini_forall₂_rng_fresh interpretation r S g ds))

/-! ## `Runs` monad evaluators and `attackerSend` -/

/-- `x : Traceful α` evaluates on `tr` to `some a` with post-trace `tr'`. -/
def Runs {α : Type} (x : Traceful α) (tr : ExecTrace) (a : α) (tr' : ExecTrace) : Prop :=
  (x.run tr).1 = some a ∧ (x.run tr).2.val = tr'

theorem Runs.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr tr₁ tr₂ : ExecTrace} {a : α} {b : β}
    (hx : Runs x tr a tr₁) (hf : Runs (f a) tr₁ b tr₂) :
    Runs (x >>= f) tr b tr₂ := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hf1, hf2⟩ := hf
  unfold Runs
  rw [Traceful.run_bind]
  rcases hr : x.run tr with ⟨o, tMid⟩
  rw [hr] at hx1 hx2; dsimp only at hx1 hx2
  subst hx1; subst hx2
  exact ⟨hf1, hf2⟩

theorem Runs.pure {α : Type} (a : α) (tr : ExecTrace) : Runs (Pure.pure a) tr a tr := by
  simp [Runs, DY.Traceful.run_pure]

theorem Runs.getEntry {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {i : Nat} {e : E}
    (h : (tr.at? i : Option E) = some e) : Runs (DY.getEntry i : Traceful E) tr e tr := by
  simp [Runs, Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk, h]

theorem Runs.appendEntry {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    Runs (DY.appendEntry e) tr tr.length (tr.append e) := by
  simp [Runs, Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]

theorem Runs.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : p) :
    Runs (_root_.guard p) tr () tr := by
  simp [Runs, _root_.guard, h, DY.Traceful.run_pure]

theorem Runs.ini_traceLength (tr : ExecTrace) :
    Runs DY.Libsignal.TripleRatchet.traceLength tr tr.length tr := by
  unfold Runs DY.Libsignal.TripleRatchet.traceLength
  simp [DY.Traceful.run_mk]

abbrev ini_EvE (ev : PQXDHEvent) : DY.ProtocolEvent.ExecEntryT PQXDHEvent := ⟨ev⟩
abbrev ini_TREvE (ev : TREvent) : DY.ProtocolEvent.ExecEntryT TREvent := ⟨ev⟩
abbrev ini_CEvE (ev : ComposedEvent) : DY.ProtocolEvent.ExecEntryT ComposedEvent := ⟨ev⟩
abbrev ini_NetE (b : DY.Bytes) : DY.Network.ExecEntryT := ⟨b⟩
abbrev ini_RndE (n : Nat) : DY.Random.ExecEntryT := ⟨n⟩
abbrev ini_StE (me : DY.Participant) (st : PQXDHState) :
    DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState PQXDHState) :=
  ⟨{ participant := me, state := st }⟩
abbrev ini_TRStE (me : DY.Participant) (st : TRState) :
    DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState TRState) :=
  ⟨{ participant := me, state := st }⟩

theorem Runs.logPQEvent (tr : ExecTrace) (ev : PQXDHEvent) :
    Runs (DY.ProtocolEvent.logEvent ev) tr () (tr.append (ini_EvE ev)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact Runs.bind (Runs.appendEntry tr _) (Runs.pure _ _)

theorem Runs.logTREvent (tr : ExecTrace) (ev : TREvent) :
    Runs (DY.ProtocolEvent.logEvent ev) tr () (tr.append (ini_TREvE ev)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact Runs.bind (Runs.appendEntry tr _) (Runs.pure _ _)

theorem Runs.logCEvent (tr : ExecTrace) (ev : ComposedEvent) :
    Runs (DY.ProtocolEvent.logEvent ev) tr () (tr.append (ini_CEvE ev)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact Runs.bind (Runs.appendEntry tr _) (Runs.pure _ _)

theorem Runs.genRand (tr : ExecTrace) (n : Nat) :
    Runs (DY.Random.genRand n) tr (randTerm tr.length n) (tr.append (ini_RndE n)) := by
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1]
  exact Runs.bind (Runs.appendEntry tr _) (Runs.pure _ _)

theorem Runs.sendMessage (tr : ExecTrace) (b : DY.Bytes) :
    Runs (DY.Network.sendMessage b) tr tr.length (tr.append (ini_NetE b)) := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1]
  exact Runs.appendEntry _ _

theorem Runs.ini_receiveMessage {tr : ExecTrace} {i : Nat} {b : DY.Bytes}
    (h : tr.at? i = some (ini_NetE b)) : Runs (DY.Network.receiveMessage i) tr b tr := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact Runs.bind (Runs.getEntry h) (Runs.pure _ _)

theorem Runs.storeTRState (tr : ExecTrace) (me : DY.Participant) (st : TRState) :
    Runs (DY.PersistentLocalState.storeLocalState me st) tr tr.length (tr.append (ini_TRStE me st)) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]
  exact Runs.appendEntry _ _

theorem Runs.getKey {tr : ExecTrace} {me : DY.Participant} {h : Nat}
    {kind : KeyKind} {sk : DY.Bytes}
    (hst : tr.at? h = some (ini_StE me { kind, sk })) :
    Runs (DY.Libsignal.PQXDH.getKey me h kind) tr sk tr := by
  unfold DY.Libsignal.PQXDH.getKey
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine Runs.bind (Runs.bind (Runs.bind (Runs.getEntry hst) (Runs.pure _ _))
    (Runs.bind (Runs.guard (p := me = me) _ rfl) (Runs.pure _ _))) ?_
  exact Runs.bind (Runs.guard (p := kind = kind) _ rfl) (Runs.pure _ _)

theorem Runs.ini_lookupIdentity {tr : ExecTrace} {p : DY.Participant} {i : Nat}
    {ikPk vkPk : DY.Bytes} {honest : Bool}
    (h : tr.at? i = some (ini_EvE (.IdentityRegistered p ikPk vkPk honest))) :
    Runs (DY.Libsignal.PQXDH.lookupIdentity p i) tr (ikPk, vkPk) tr :=
  Runs.bind (Runs.getEntry h) (Runs.bind (Runs.guard (p := p = p) _ rfl) (Runs.pure _ _))

theorem Runs.requireTracePredicate {p : ExecTrace → Bool} {tr : ExecTrace} (h : p tr = true) :
    Runs (DY.Libsignal.PQXDH.guardTrace p) tr () tr := by
  unfold Runs DY.Libsignal.PQXDH.guardTrace
  rw [Traceful.run_mk, h]
  exact ⟨rfl, rfl⟩

/-- Optional network-handle lookup predicate used by `aliceHandshake` / `aliceStart`. -/
def NetOpt (tr : ExecTrace) : Option Nat → Option DY.Bytes → Prop
  | none, none => True
  | some i, some o => tr.at? i = some (ini_NetE o)
  | _, _ => False

theorem at?_append_self {T : Type} [ExecTraceTypes.Has T] (tr : ExecTrace) (x : T) :
    ((tr.append x).at? tr.length : Option T) = some x :=
  DY.Trace.at?_append tr x

theorem at?_append_of_lt {T S : Type} [ExecTraceTypes.Has T] [ExecTraceTypes.Has S]
    (tr : ExecTrace) (x : S) {i : Nat} (hlt : i < tr.length) :
    ((tr.append x).at? i : Option T) = (tr.at? i : Option T) := by
  have hlt' : i < (tr.append x).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, hlt', ↓reduceDIte]
  rw [DY.Trace.at_le tr (tr.append x) i hlt (DY.Trace.append_le tr x)]

theorem at?_append_eq_of_eq {T S : Type} [ExecTraceTypes.Has T] [ExecTraceTypes.Has S]
    (tr : ExecTrace) (x : S) {i : Nat} (hi : i = tr.length) :
    ((tr.append x).at? i : Option T) = TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) := by
  subst hi
  have hlt : tr.length < (tr.append x).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp only [DY.Trace.at?, hlt, ↓reduceDIte]
  simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2]

theorem getMessageSentAt_of_at? {tr : ExecTrace} {i : Nat} {b : DY.Bytes}
    (h : (tr.at? i : Option DY.Network.ExecEntryT) = some (ini_NetE b)) :
    tr.getMessageSentAt i = some b := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]; rw [h]

theorem getMessageSentAt_attackerSend (tr : ExecTrace) (msg : DY.Bytes) :
    ((Move.attackerSend msg).next tr).getMessageSentAt tr.length = some msg := by
  have hn : (Move.attackerSend msg).next tr = tr.append (ini_NetE msg) := by
    unfold Move.next Move.act
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
      DY.Traceful.run_mk, DY.Traceful.run_pure]
  rw [hn]
  exact getMessageSentAt_of_at? (at?_append_self tr (ini_NetE msg))

theorem attackerSend_reachable {tr : ExecTrace} (hreach : tr.Reachable reachability)
    {msg : DY.Bytes} (hknow : msg.AttackerKnows tr) :
    ((Move.attackerSend msg).next tr).Reachable reachability :=
  b5_attackerSend_reachable hreach msg hknow

/-! ## Concretization `gamma` unfolding lemmas -/

section GammaLemmas

unseal DY.Bytes in
local instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
local instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
local instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
local instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemEncap interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
local instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemSS interpretation S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_randTerm (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (i n : Nat) :
    gamma interpretation S g (randTerm i n) = if n = 0 then [] else g.σ i n := by
  unfold gamma gamma' randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]
  unfold concretizeRandom node
  split <;> rfl

theorem gamma_litOf (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (bs : HwBytes) :
    gamma interpretation S g (litOf bs) = bs := by
  unfold gamma gamma' litOf
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll interpretation S g)]
  unfold concretizeLit node ofByteArray
  simp only [List.map_map]
  exact List.map_id'' (fun x => rfl) bs

theorem gamma_compHwLit (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (bs : HwBytes) :
    gamma interpretation S g (compHwLit bs) = bs :=
  gamma_litOf interpretation S g bs

theorem ini_gamma_dhPk (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sk : DY.Bytes) :
    gamma interpretation S g (DY.DiffieHellman.dhPk sk) =
      (interpretation x25519PublicKeySymbol [clamp (gamma interpretation S g sk)]).getD [] := by
  unfold gamma gamma'
  show ((({sk} : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeDhPk interpretation) (concretizeAll interpretation S g)]
  rfl

end GammaLemmas

theorem ecKey_inj {a b : HwBytes} (h : ecKey a = ecKey b) : a = b := by
  injection h

theorem kyberKey_inj {a b : HwBytes} (h : kyberKey a = kyberKey b) : a = b := by
  injection h

end Symbolic.Swarm.CREF
