/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Stage1Kyber -- shake: keep
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.Literal
import Symbolic.DYBridge.DY.EquationalTheory.Concat
import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.EquationalTheory.Sign

/-!
# Fresh-Ghost Invariance for the Composed Model

Invariance of concretization (`gamma'` and `gamma`), session state relations, and visible-entry
matching under `updateFreshAt` at timestamps beyond `MemoStampsLt` / `StampsLt`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR.FreshSigma

cref_open
open Symbolic.Swarm.CREF.TR
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Rust (RecordRec)
open DY.Libsignal.TripleRatchet (TRState TREvent trMsgKeys trHonestWireMsg)
open DY.Libsignal.TripleRatchet (hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 lit createChain kdfCk kdfRk
  chainKeyAt computeMac)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent)

abbrev StEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev TREntry := DY.ProtocolEvent.ExecEntryT TREvent
abbrev PQStEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState PQXDHState)
abbrev PQEvEntry := DY.ProtocolEvent.ExecEntryT PQXDHEvent
abbrev CEvEntry := DY.ProtocolEvent.ExecEntryT ComposedEvent

/-! ## `Traceful` and `getLocalState` helpers -/

theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem getLocalState_fst (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 =
      match (tr.at? stH : Option StEntry) with
      | some ⟨⟨p, st⟩⟩ => if p = me then some st else none
      | none => none := by
  have hg1 : ((DY.getEntry stH : Traceful StEntry).run tr).1 = (tr.at? stH : Option StEntry) := by
    rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  have hg2 : ((DY.getEntry stH : Traceful StEntry).run tr).2.val = tr := by
    rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  rw [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    run_bind_fst, run_bind_fst, run_bind_snd, hg1, hg2]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only; rw [Traceful.run_pure]; dsimp only
    change (((if p = me then pure () else failure : Traceful Unit) >>= fun _ => pure st).run tr).1 =
      if p = me then some st else none
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h, ite_eq_left_iff.mpr fun h => absurd hp h]
      rw [run_bind_fst, Traceful.run_pure]; dsimp only; rw [Traceful.run_pure]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp, ite_eq_right_iff.mpr fun h => absurd h hp]
      rw [run_bind_fst, Traceful.run_failure]

theorem at?_eq_some_of_getLocalState_some {p : Participant} {stateIdx : Nat}
    {tr : ExecTrace} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st) :
    (tr.at? stateIdx : Option StEntry) = some ⟨⟨p, st⟩⟩ := by
  rw [getLocalState_fst] at hst
  rcases h : (tr.at? stateIdx : Option StEntry) with _ | ⟨⟨me, st'⟩⟩
  · rw [h] at hst; cases hst
  · rw [h] at hst
    by_cases hme : me = p
    · subst hme; simp only [↓reduceIte, Option.some.injEq] at hst; subst hst; rfl
    · simp only [hme, ↓reduceIte] at hst; cases hst

/-! ## `updateFreshAt` and `MemoStampsLt` / `StampsLt` -/

def updateFreshAt (σ : Nat → Nat → DY.Libsignal.HwBytes) (ts n : Nat) (m : DY.Libsignal.HwBytes) :
    Nat → Nat → DY.Libsignal.HwBytes :=
  fun i k => if i = ts ∧ k = n then m else σ i k

@[simp] theorem updateFreshAt_self (σ : Nat → Nat → HwBytes) (ts n : Nat) (m : HwBytes) :
    updateFreshAt σ ts n m ts n = m := by simp [updateFreshAt]

theorem setupTrace_le_runTrace (r₀ : ProtocolSetup) (ms : List Move) :
    setupTrace r₀ ≤ runTraceMoves r₀ ms := runMoves_le ms (setupTrace r₀)

def MemoStampsLt (ts : Nat) (g : ConcretizedTerm) : Prop :=
  ∀ (t sh : DY.Bytes) (v : HwBytes) (r : DY.Random.Random DY.Bytes),
    (t, sh, v) ∈ g.memo → t.view? DY.Random.Random = some r → r.timestamp < ts

def StampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (b : DY.Bytes) : Prop :=
  MemoStampsLt ts (gamma' i S g b)

theorem memoStampsLt_of_mem {ts : Nat} {v : HwBytes} {self sh : DY.Bytes} {cs : List ConcretizedTerm}
    (h : MemoStampsLt ts (node v self sh cs)) {c : ConcretizedTerm} (hc : c ∈ cs) : MemoStampsLt ts c :=
  fun t sh' val r hmem hview =>
    h t sh' val r (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c, hc, hmem⟩)) hview

theorem memoStampsLt_of_spqrNode {ts : Nat} {v : HwBytes} {cs : List ConcretizedTerm}
    (h : MemoStampsLt ts (spqrNode v cs)) {c : ConcretizedTerm} (hc : c ∈ cs) : MemoStampsLt ts c :=
  fun t sh' val r hmem hview => h t sh' val r (List.mem_flatMap.mpr ⟨c, hc, hmem⟩) hview

theorem memoStampsLt_of_opaqueNode {ts : Nat} {v : HwBytes} {cs : List ConcretizedTerm}
    (h : MemoStampsLt ts (opaqueNode v cs)) {c : ConcretizedTerm} (hc : c ∈ cs) : MemoStampsLt ts c :=
  memoStampsLt_of_spqrNode h hc

theorem memoStampsLt_of_spqrKeyNode {ts : Nat} {v : HwBytes} {cs : List ConcretizedTerm}
    (h : MemoStampsLt ts (spqrKeyNode v cs)) {c : ConcretizedTerm} (hc : c ∈ cs) : MemoStampsLt ts c :=
  memoStampsLt_of_spqrNode h hc

def MemoRel (ts : Nat) (p : ConcretizedTerm × ConcretizedTerm) : Prop := MemoStampsLt ts p.1 → p.2 = p.1

theorem gConcat0_pp2 (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 concretizeConcat concretizeConcat rec1 rec2 (MemoRel ts) := by
  intro ⟨l, r⟩ ih h; dsimp only [concretizeConcat, MemoRel] at h ⊢
  have hl : rec2 l = rec1 l := ih l (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  have hr : rec2 r = rec1 r := ih r (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  rw [hl, hr]

theorem gDhPk_pp2 (i : ExternInterpretation) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeDhPk i) (concretizeDhPk i) rec1 rec2 (MemoRel ts) := by
  intro ⟨sk⟩ ih h; dsimp only [concretizeDhPk, MemoRel] at h ⊢
  have hs : rec2 sk = rec1 sk := ih sk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  rw [hs]

theorem gDh_pp2 (i : ExternInterpretation) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeDh i) (concretizeDh i) rec1 rec2 (MemoRel ts) := by
  intro ⟨pk, sk⟩ ih h; dsimp only [concretizeDh, MemoRel] at h ⊢
  have hp : rec2 pk = rec1 pk := ih pk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  have hs : rec2 sk = rec1 sk := ih sk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  rw [hp, hs]

theorem gKdf0_pp2 (i : ExternInterpretation) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeKdf i) (concretizeKdf i) rec1 rec2 (MemoRel ts) := by
  intro ⟨a, b⟩ ih h; dsimp only [concretizeKdf, MemoRel] at h ⊢
  have ha : rec2 a = rec1 a := ih a (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  have hb : rec2 b = rec1 b := ih b (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  rw [ha, hb]

theorem gSym0_pp2 (i : ExternInterpretation) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeSym i) (concretizeSym i) rec1 rec2 (MemoRel ts) := by
  intro ⟨k, iv, m⟩ ih h; dsimp only [concretizeSym, MemoRel] at h ⊢
  have hk : rec2 k = rec1 k := ih k (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  have hiv : rec2 iv = rec1 iv := ih iv (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  have hm : rec2 m = rec1 m := ih m (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  rw [hk, hiv, hm]

theorem gTrunc0_pp2 (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 concretizeTrunc concretizeTrunc rec1 rec2 (MemoRel ts) := by
  intro ⟨a⟩ ih h; dsimp only [concretizeTrunc, MemoRel] at h ⊢
  have ha : rec2 a = rec1 a := ih a (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  rw [ha]

theorem gVariant0_pp2 {i : ExternInterpretation} (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeVariant i) (concretizeVariant i) rec1 rec2 (MemoRel ts) := by
  intro ⟨k, _, _⟩ ih h; dsimp only [concretizeVariant, MemoRel] at h ⊢
  have hk : rec2 k = rec1 k := ih k (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  rw [hk]

theorem gKemPk_pp2 (S : OpaqueSymbolSemantics) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeKemPk S) (concretizeKemPk S) rec1 rec2 (MemoRel ts) := by
  intro ⟨sk⟩ ih h; dsimp only [concretizeKemPk, MemoRel] at h ⊢
  have hs : rec2 sk = rec1 sk := ih sk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  rw [hs]

theorem gKemEncap_pp2 (i : ExternInterpretation) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeKemEncap i) (concretizeKemEncap i) rec1 rec2 (MemoRel ts) := by
  intro ⟨pk, ss⟩ ih h; dsimp only [concretizeKemEncap, MemoRel] at h ⊢
  split at h
  · rename_i h32
    have hp : rec2 pk = rec1 pk := ih pk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
    have hs : rec2 ss = rec1 ss := ih ss (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
    simp only [hp, hs, h32, ↓reduceIte]
  · rename_i h32
    have hp : rec2 pk = rec1 pk := ih pk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
    have hs : rec2 ss = rec1 ss := ih ss (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
    simp only [hp, hs, h32, ↓reduceIte]

theorem gKemSS_pp2 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeKemSS i S) (concretizeKemSS i S) rec1 rec2 (MemoRel ts) := by
  intro ⟨pk, coins⟩ ih h; dsimp only [concretizeKemSS, MemoRel] at h ⊢
  split at h
  · rename_i h32
    have hp : rec2 pk = rec1 pk := ih pk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
    have hc : rec2 coins = rec1 coins := ih coins (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
    simp only [hp, hc, h32, ↓reduceIte]
  · rename_i h32
    have hp : rec2 pk = rec1 pk := ih pk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
    have hc : rec2 coins = rec1 coins := ih coins (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
    simp only [hp, hc, h32, ↓reduceIte]

theorem gKemRej_pp2 (S : OpaqueSymbolSemantics) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeKemRej S) (concretizeKemRej S) rec1 rec2 (MemoRel ts) := by
  intro ⟨sk, ct⟩ ih h; dsimp only [concretizeKemRej, MemoRel] at h ⊢
  have hs : rec2 sk = rec1 sk := ih sk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  have hc : rec2 ct = rec1 ct := ih ct (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  rw [hs, hc]

theorem gVk_pp2 (S : OpaqueSymbolSemantics) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeVk S) (concretizeVk S) rec1 rec2 (MemoRel ts) := by
  intro ⟨sk⟩ ih h; dsimp only [concretizeVk, MemoRel] at h ⊢
  have hs : rec2 sk = rec1 sk := ih sk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  rw [hs]

theorem gSign_pp2 (S : OpaqueSymbolSemantics) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeSign S) (concretizeSign S) rec1 rec2 (MemoRel ts) := by
  intro ⟨sk, msg, r⟩ ih h; dsimp only [concretizeSign, MemoRel] at h ⊢
  have hs : rec2 sk = rec1 sk := ih sk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  have hm : rec2 msg = rec1 msg := ih msg (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  have hr : rec2 r = rec1 r := ih r (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  rw [hs, hm, hr]

theorem gTrWire0_pp2 (g : Ghost) (ts n : Nat) (m : HwBytes) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeTrWire g) (concretizeTrWire { g with σ := updateFreshAt g.σ ts n m }) rec1 rec2 (MemoRel ts) := by
  intro ⟨v, rk, c, pc, ct, pq, ev⟩ ih h; dsimp only [concretizeTrWire, MemoRel] at h ⊢
  have hrk : rec2 rk = rec1 rk := ih rk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  have hct : rec2 ct = rec1 ct := ih ct (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  have hpq : rec2 pq = rec1 pq := ih pq (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  rw [hrk, hct, hpq]

theorem gSpqrInit_pp2 (S : OpaqueSymbolSemantics) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeSpqrInit S) (concretizeSpqrInit S) rec1 rec2 (MemoRel ts) := by
  intro ⟨a, p⟩ ih h; dsimp only [concretizeSpqrInit, MemoRel] at h ⊢
  have ha : rec2 a = rec1 a := ih a (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  have hp : rec2 p = rec1 p := ih p (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  rw [ha, hp]

theorem gSpqrSendState_pp2 (S : OpaqueSymbolSemantics) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeSpqrSendState S) (concretizeSpqrSendState S) rec1 rec2 (MemoRel ts) := by
  intro ⟨a, b⟩ ih h; dsimp only [concretizeSpqrSendState, MemoRel] at h ⊢
  have ha : rec2 a = rec1 a := ih a (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  have hb : rec2 b = rec1 b := ih b (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  rw [ha, hb]

theorem gSpqrSendKey_pp2 (S : OpaqueSymbolSemantics) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeSpqrSendKey S) (concretizeSpqrSendKey S) rec1 rec2 (MemoRel ts) := by
  intro ⟨a, b⟩ ih h; dsimp only [concretizeSpqrSendKey, MemoRel] at h ⊢
  have ha : rec2 a = rec1 a := ih a (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_spqrKeyNode h (by simp))
  have hb : rec2 b = rec1 b := ih b (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_spqrKeyNode h (by simp))
  rw [ha, hb]

theorem gSpqrSendMsg_pp2 (S : OpaqueSymbolSemantics) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeSpqrSendMsg S) (concretizeSpqrSendMsg S) rec1 rec2 (MemoRel ts) := by
  intro ⟨a, b⟩ ih h; dsimp only [concretizeSpqrSendMsg, MemoRel] at h ⊢
  have ha : rec2 a = rec1 a := ih a (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  have hb : rec2 b = rec1 b := ih b (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  rw [ha, hb]

theorem gSpqrRecvState_pp2 (S : OpaqueSymbolSemantics) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeSpqrRecvState S) (concretizeSpqrRecvState S) rec1 rec2 (MemoRel ts) := by
  intro ⟨a, b⟩ ih h; dsimp only [concretizeSpqrRecvState, MemoRel] at h ⊢
  have ha : rec2 a = rec1 a := ih a (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  have hb : rec2 b = rec1 b := ih b (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_opaqueNode h (by simp))
  rw [ha, hb]

theorem gSpqrRecvKey_pp2 (S : OpaqueSymbolSemantics) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeSpqrRecvKey S) (concretizeSpqrRecvKey S) rec1 rec2 (MemoRel ts) := by
  intro ⟨a, b⟩ ih h; dsimp only [concretizeSpqrRecvKey, MemoRel] at h ⊢
  have ha : rec2 a = rec1 a := ih a (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_spqrKeyNode h (by simp))
  have hb : rec2 b = rec1 b := ih b (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_spqrKeyNode h (by simp))
  rw [ha, hb]

theorem gSpqrChainKey_pp2 (S : OpaqueSymbolSemantics) (ts : Nat) (rec1 rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeSpqrChainKey S) (concretizeSpqrChainKey S) rec1 rec2 (MemoRel ts) := by
  intro ⟨a, p, idx⟩ ih h; dsimp only [concretizeSpqrChainKey, MemoRel] at h ⊢
  have ha : rec2 a = rec1 a := ih a (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_spqrKeyNode h (by simp))
  have hp : rec2 p = rec1 p := ih p (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_spqrKeyNode h (by simp))
  have hi : rec2 idx = rec1 idx := ih idx (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_spqrKeyNode h (by simp))
  rw [ha, hp, hi]

theorem allFuns_partialProof2 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ts n : Nat) (m : HwBytes) (rec1 rec2 : DY.Bytes → ConcretizedTerm) (id : Fin 12) :
    DY.Bytes.PartialProof2 (allFuns i S g id)
      (allFuns i S { g with σ := updateFreshAt g.σ ts n m } id) rec1 rec2 (MemoRel ts) := by
  match id with
  | ⟨0, _⟩ =>
    dsimp only [allFuns, DY.Libsignal.Composed.SubF.internal]
    intro x _ h; dsimp only [concretizeRandom, MemoRel] at h ⊢
    split
    · rfl
    · next hsz =>
      simp only [hsz, ↓reduceIte] at h
      have hlt := h x.pack x.pack (g.σ x.timestamp x.size) x (List.mem_cons_self ..) (BytesView.view_pack x)
      have hne : x.timestamp ≠ ts := by omega
      simp [updateFreshAt, hne]
  | ⟨1, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩ _ _ _; rfl
  | ⟨2, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gConcat0_pp2 ts rec1 rec2
  | ⟨3, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro id2
    match id2 with | ⟨0, _⟩ => exact gDhPk_pp2 i ts rec1 rec2 | ⟨1, _⟩ => exact gDh_pp2 i ts rec1 rec2
  | ⟨4, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gKdf0_pp2 i ts rec1 rec2
  | ⟨5, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gSym0_pp2 i ts rec1 rec2
  | ⟨6, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gTrunc0_pp2 ts rec1 rec2
  | ⟨7, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gVariant0_pp2 ts rec1 rec2
  | ⟨8, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact gKemPk_pp2 S ts rec1 rec2
    | ⟨1, _⟩ => exact gKemEncap_pp2 i ts rec1 rec2
    | ⟨2, _⟩ => exact gKemSS_pp2 i S ts rec1 rec2
    | ⟨3, _⟩ => exact gKemRej_pp2 S ts rec1 rec2
  | ⟨9, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro id2
    match id2 with | ⟨0, _⟩ => exact gVk_pp2 S ts rec1 rec2 | ⟨1, _⟩ => exact gSign_pp2 S ts rec1 rec2
  | ⟨10, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact gSpqrInit_pp2 S ts rec1 rec2
    | ⟨1, _⟩ => exact gSpqrSendState_pp2 S ts rec1 rec2
    | ⟨2, _⟩ => exact gSpqrSendKey_pp2 S ts rec1 rec2
    | ⟨3, _⟩ => exact gSpqrSendMsg_pp2 S ts rec1 rec2
    | ⟨4, _⟩ => exact gSpqrRecvState_pp2 S ts rec1 rec2
    | ⟨5, _⟩ => exact gSpqrRecvKey_pp2 S ts rec1 rec2
    | ⟨6, _⟩ => exact gSpqrChainKey_pp2 S ts rec1 rec2
  | ⟨11, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩
    exact gTrWire0_pp2 g ts n m rec1 rec2

theorem gamma'_updateFreshAt_of_stampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ts n : Nat) (m : HwBytes) (b : DY.Bytes) :
    StampsLt i S g ts b →
      gamma' i S { g with σ := updateFreshAt g.σ ts n m } b = gamma' i S g b := by
  have hpf : DY.Bytes.Proof2 (concretizeAll i S g) (concretizeAll i S { g with σ := updateFreshAt g.σ ts n m }) (MemoRel ts) :=
    DY.Bytes.PartialProof2.combine (allFuns_partialProof2 i S g ts n m _ _)
  exact hpf.prove b

theorem gamma_updateFreshAt_of_stampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ts n : Nat) (m : HwBytes) (b : DY.Bytes) (h : StampsLt i S g ts b) :
    gamma i S { g with σ := updateFreshAt g.σ ts n m } b = gamma i S g b :=
  congrArg ConcretizedTerm.bytes (gamma'_updateFreshAt_of_stampsLt i S g ts n m b h)

theorem stampsLt_mono {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts₁ ts₂ : Nat}
    {b : DY.Bytes} (hle : ts₁ ≤ ts₂) (h : StampsLt i S g ts₁ b) : StampsLt i S g ts₂ b :=
  fun t sh v r hmem hview => Nat.lt_of_lt_of_le (h t sh v r hmem hview) hle

theorem stampsLt_updateFreshAt_iff {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts n : Nat} {m : HwBytes} {b : DY.Bytes} (h : StampsLt i S g ts b) :
    StampsLt i S { g with σ := updateFreshAt g.σ ts n m } ts b := by
  unfold StampsLt; rw [gamma'_updateFreshAt_of_stampsLt i S g ts n m b h]; exact h

theorem memoStampsLt_node {ts : Nat} {v : HwBytes} {self sh : DY.Bytes} {cs : List ConcretizedTerm}
    (hself : self.view? DY.Random.Random = none) :
    MemoStampsLt ts (node v self sh cs) ↔ ∀ c ∈ cs, MemoStampsLt ts c := by
  refine ⟨fun h c hc => memoStampsLt_of_mem h hc, fun h t sh' val r hmem hview => ?_⟩
  rcases List.mem_cons.mp hmem with ⟨rfl, rfl, rfl⟩ | hrest
  · rw [hself] at hview; cases hview
  · obtain ⟨c, hc, hcmem⟩ := List.mem_flatMap.mp hrest
    exact h c hc t sh' val r hcmem hview

theorem memoStampsLt_spqrNode {ts : Nat} {v : HwBytes} {cs : List ConcretizedTerm} :
    MemoStampsLt ts (spqrNode v cs) ↔ ∀ c ∈ cs, MemoStampsLt ts c := by
  refine ⟨fun h c hc => memoStampsLt_of_spqrNode h hc, fun h t sh' val r hmem hview => ?_⟩
  obtain ⟨c, hc, hcmem⟩ := List.mem_flatMap.mp hmem
  exact h c hc t sh' val r hcmem hview

theorem memoStampsLt_opaqueNode {ts : Nat} {v : HwBytes} {cs : List ConcretizedTerm} :
    MemoStampsLt ts (opaqueNode v cs) ↔ ∀ c ∈ cs, MemoStampsLt ts c :=
  memoStampsLt_spqrNode

theorem memoStampsLt_spqrKeyNode {ts : Nat} {v : HwBytes} {cs : List ConcretizedTerm} :
    MemoStampsLt ts (spqrKeyNode v cs) ↔ ∀ c ∈ cs, MemoStampsLt ts c :=
  memoStampsLt_spqrNode

/-! ## Constructor lemmas for `StampsLt` -/

section UnsealedStamps
unseal DY.Bytes

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

instance : DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction concretizeConcat (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeDh i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeSym i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, symFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction concretizeTrunc (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeKemEncap i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeKemSS i S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeKemRej S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeVk S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeSign S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeSpqrInit S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeSpqrSendState S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeSpqrSendKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeSpqrSendMsg S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeSpqrRecvState S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeSpqrRecvKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeSpqrChainKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
instance : DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem stampsLt_rand_of_lt {ts t : Nat} (n : Nat) (hlt : t < ts) : StampsLt i S g ts (randTerm t n) := by
  unfold StampsLt gamma' randTerm; rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g)]
  dsimp only [concretizeRandom, node, MemoStampsLt]; split
  · intro _ _ _ _ hmem; cases hmem
  · intro b sh val r hmem hview
    rcases List.mem_singleton.mp hmem with ⟨rfl, rfl, rfl⟩
    rw [BytesView.view_pack ({ timestamp := t, size := n } : DY.Random.Random DY.Bytes)] at hview
    cases hview; exact hlt

@[simp] theorem stampsLt_lit (ts : Nat) (x : DY.Literal.Literal.SubF DY.Bytes) :
    StampsLt i S g ts x.pack := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq concretizeLit (concretizeAll i S g)]
  exact (memoStampsLt_node (self := x.pack)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)).mpr (by simp)

@[simp] theorem stampsLt_concat_pack (ts : Nat) (x : DY.Concat.Concat.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.lhs ∧ StampsLt i S g ts x.rhs := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll i S g)]; dsimp only [concretizeConcat]
  rw [memoStampsLt_node (self := x.pack)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp

@[simp] theorem stampsLt_dhPk_pack (ts : Nat) (x : DY.DiffieHellman.DhPk.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.sk := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeDhPk i) (concretizeAll i S g)]; dsimp only [concretizeDhPk]
  rw [memoStampsLt_node (self := x.pack)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp

@[simp] theorem stampsLt_dh_pack (ts : Nat) (x : DY.DiffieHellman.Dh.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.pk ∧ StampsLt i S g ts x.sk := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]; dsimp only [concretizeDh]
  rw [memoStampsLt_node (self := x.pack)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp

@[simp] theorem stampsLt_kdf_pack (ts : Nat) (x : DY.KdfExtract.KdfExtract.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.salt ∧ StampsLt i S g ts x.ikm := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]; dsimp only [concretizeKdf]
  rw [memoStampsLt_node (self := x.pack)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp

@[simp] theorem stampsLt_sym_pack (ts : Nat) (x : DY.SymEnc.Enc.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔
      StampsLt i S g ts x.key ∧ StampsLt i S g ts x.iv ∧ StampsLt i S g ts x.msg := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeSym i) (concretizeAll i S g)]; dsimp only [concretizeSym]
  rw [memoStampsLt_node (self := x.pack)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp

@[simp] theorem stampsLt_trunc_pack (ts : Nat) (x : DY.Trunc.Trunc8.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.input := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq concretizeTrunc (concretizeAll i S g)]; dsimp only [concretizeTrunc]
  rw [memoStampsLt_node (self := x.pack)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp

@[simp] theorem stampsLt_variant_pack (ts : Nat) (x : DY.X25519.Variant.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.key := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeVariant i) (concretizeAll i S g)]; dsimp only [concretizeVariant]
  rw [memoStampsLt_node (self := x.pack)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp

@[simp] theorem stampsLt_kemPk_pack (ts : Nat) (x : DY.PQKem.Pk.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.sk := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll i S g)]; dsimp only [concretizeKemPk]
  rw [memoStampsLt_opaqueNode]; simp

@[simp] theorem stampsLt_kemEncap_pack (ts : Nat) (x : DY.PQKem.Encap.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.pk ∧ StampsLt i S g ts x.entropy := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeKemEncap i) (concretizeAll i S g)]; dsimp only [concretizeKemEncap]
  split
  · rw [memoStampsLt_node (self := x.pack)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
  · rw [memoStampsLt_opaqueNode]; simp

@[simp] theorem stampsLt_kemSS_pack (ts : Nat) (x : DY.PQKem.SharedSecret.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.pk ∧ StampsLt i S g ts x.entropy := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeKemSS i S) (concretizeAll i S g)]; dsimp only [concretizeKemSS]
  split
  · rw [memoStampsLt_node (self := x.pack)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
  · rw [memoStampsLt_opaqueNode]; simp

@[simp] theorem stampsLt_kemRej_pack (ts : Nat) (x : DY.PQKem.RejKey.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.sk ∧ StampsLt i S g ts x.cipher := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeKemRej S) (concretizeAll i S g)]; dsimp only [concretizeKemRej]
  rw [memoStampsLt_node (self := x.pack)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp

@[simp] theorem stampsLt_vk_pack (ts : Nat) (x : DY.Signature.Vk.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.sk := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeVk S) (concretizeAll i S g)]; dsimp only [concretizeVk]
  rw [memoStampsLt_opaqueNode]; simp

@[simp] theorem stampsLt_sign_pack (ts : Nat) (x : DY.Signature.Sign.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.sk ∧ StampsLt i S g ts x.nonce ∧ StampsLt i S g ts x.msg := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeSign S) (concretizeAll i S g)]; dsimp only [concretizeSign]
  rw [memoStampsLt_opaqueNode]; simp

@[simp] theorem stampsLt_spqrInit_pack (ts : Nat) (x : DY.Spqr.InitState.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.authKey ∧ StampsLt i S g ts x.params := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll i S g)]; dsimp only [concretizeSpqrInit]
  rw [memoStampsLt_opaqueNode]; simp

@[simp] theorem stampsLt_spqrSendState_pack (ts : Nat) (x : DY.Spqr.SendState.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.st ∧ StampsLt i S g ts x.coins := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrSendState S) (concretizeAll i S g)]; dsimp only [concretizeSpqrSendState]
  rw [memoStampsLt_opaqueNode]; simp

@[simp] theorem stampsLt_spqrSendKey_pack (ts : Nat) (x : DY.Spqr.SendKey.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.st ∧ StampsLt i S g ts x.coins := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrSendKey S) (concretizeAll i S g)]; dsimp only [concretizeSpqrSendKey]
  rw [memoStampsLt_spqrKeyNode]; simp

@[simp] theorem stampsLt_spqrSendMsg_pack (ts : Nat) (x : DY.Spqr.SendMsg.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.st ∧ StampsLt i S g ts x.coins := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrSendMsg S) (concretizeAll i S g)]; dsimp only [concretizeSpqrSendMsg]
  rw [memoStampsLt_opaqueNode]; simp

@[simp] theorem stampsLt_spqrRecvState_pack (ts : Nat) (x : DY.Spqr.RecvState.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.st ∧ StampsLt i S g ts x.msg := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrRecvState S) (concretizeAll i S g)]; dsimp only [concretizeSpqrRecvState]
  rw [memoStampsLt_opaqueNode]; simp

@[simp] theorem stampsLt_spqrRecvKey_pack (ts : Nat) (x : DY.Spqr.RecvKey.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔ StampsLt i S g ts x.st ∧ StampsLt i S g ts x.msg := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrRecvKey S) (concretizeAll i S g)]; dsimp only [concretizeSpqrRecvKey]
  rw [memoStampsLt_spqrKeyNode]; simp

@[simp] theorem stampsLt_spqrChainKey_pack (ts : Nat) (x : DY.Spqr.ChainKey.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔
      StampsLt i S g ts x.authKey ∧ StampsLt i S g ts x.params ∧ StampsLt i S g ts x.idx := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrChainKey S) (concretizeAll i S g)]; dsimp only [concretizeSpqrChainKey]
  rw [memoStampsLt_spqrKeyNode]; simp

@[simp] theorem stampsLt_trWire_pack (ts : Nat) (x : DY.TrWire.TrWireMsg.SubF DY.Bytes) :
    StampsLt i S g ts x.pack ↔
      StampsLt i S g ts x.senderRatchetKey ∧
      StampsLt i S g ts x.ciphertext ∧ StampsLt i S g ts x.pqRatchet := by
  unfold StampsLt gamma'; rw [DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll i S g)]; dsimp only [concretizeTrWire]
  rw [memoStampsLt_node (self := x.pack)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp

end UnsealedStamps

theorem stampsLt_x25519Key {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {pk : DY.Bytes} (h : StampsLt i S g ts pk) :
    StampsLt i S g ts (DY.X25519.normalizeX25519Key pk) := by
  have hpv := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
  unfold DY.X25519.normalizeX25519Key; split
  · next x hx => rw [hx] at hpv; rw [← hpv] at h; exact (stampsLt_variant_pack i S g ts x).mp h
  · exact h

theorem stampsLt_dh {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {pk sk : DY.Bytes} (hpk : StampsLt i S g ts pk) (hsk : StampsLt i S g ts sk) :
    StampsLt i S g ts (DY.DiffieHellman.dh pk sk) := by
  have hpv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk
  dsimp [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]; split
  · next sk2 hx =>
    rw [hx] at hpv; rw [← hpv] at hpk
    have hsk2 : StampsLt i S g ts sk2 := (stampsLt_dhPk_pack i S g ts ⟨sk2⟩).mp hpk
    split
    · exact (stampsLt_dh_pack i S g ts ⟨({ sk := sk2 } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack, sk⟩).mpr
        ⟨(stampsLt_dhPk_pack i S g ts ⟨sk2⟩).mpr hsk2, hsk⟩
    · exact (stampsLt_dh_pack i S g ts ⟨({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack, sk2⟩).mpr
        ⟨(stampsLt_dhPk_pack i S g ts ⟨sk⟩).mpr hsk, hsk2⟩
  · exact (stampsLt_dh_pack i S g ts ⟨pk, sk⟩).mpr ⟨hpk, hsk⟩

theorem stampsLt_literalToBytes (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (b : ByteArray) :
    StampsLt i S g ts (DY.Literal.literalToBytes b) := stampsLt_lit i S g ts ⟨b⟩
theorem stampsLt_concat {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {a b : DY.Bytes}
    (ha : StampsLt i S g ts a) (hb : StampsLt i S g ts b) : StampsLt i S g ts (DY.Concat.concat a b) :=
  (stampsLt_concat_pack i S g ts ⟨a, b⟩).mpr ⟨ha, hb⟩
theorem stampsLt_dhPk {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {sk : DY.Bytes}
    (hsk : StampsLt i S g ts sk) : StampsLt i S g ts (DY.DiffieHellman.dhPk sk) :=
  (stampsLt_dhPk_pack i S g ts ⟨sk⟩).mpr hsk
theorem stampsLt_kemPk {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {sk : DY.Bytes}
    (hsk : StampsLt i S g ts sk) : StampsLt i S g ts (DY.PQKem.kemPk sk) :=
  (stampsLt_kemPk_pack i S g ts ⟨sk⟩).mpr hsk
theorem stampsLt_kemEncap {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {pk e : DY.Bytes}
    (hpk : StampsLt i S g ts pk) (he : StampsLt i S g ts e) :
    StampsLt i S g ts (DY.PQKem.kemEncap pk e).1 ∧ StampsLt i S g ts (DY.PQKem.kemEncap pk e).2 :=
  ⟨(stampsLt_kemEncap_pack i S g ts ⟨pk, e⟩).mpr ⟨hpk, he⟩, (stampsLt_kemSS_pack i S g ts ⟨pk, e⟩).mpr ⟨hpk, he⟩⟩
theorem stampsLt_kemDecap {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {sk ct ss : DY.Bytes}
    (hdec : DY.PQKem.kemDecap sk ct = some ss) (hct : StampsLt i S g ts ct) : StampsLt i S g ts ss := by
  obtain ⟨e, rfl, rfl⟩ := Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.kemDecap_eq_some_iff.mp hdec
  obtain ⟨hpk, he⟩ := (stampsLt_kemEncap_pack i S g ts ⟨DY.PQKem.kemPk sk, e⟩).mp hct
  exact (stampsLt_kemSS_pack i S g ts ⟨DY.PQKem.kemPk sk, e⟩).mpr ⟨hpk, he⟩
theorem stampsLt_kemRejKey {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {sk ct : DY.Bytes}
    (hsk : StampsLt i S g ts sk) (hct : StampsLt i S g ts ct) : StampsLt i S g ts (DY.PQKem.kemRejKey sk ct) :=
  (stampsLt_kemRej_pack i S g ts ⟨sk, ct⟩).mpr ⟨hsk, hct⟩
theorem stampsLt_vk {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {sk : DY.Bytes}
    (hsk : StampsLt i S g ts sk) : StampsLt i S g ts (DY.Signature.vk sk) :=
  (stampsLt_vk_pack i S g ts ⟨sk⟩).mpr hsk
theorem stampsLt_sign {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {sk n m : DY.Bytes}
    (hsk : StampsLt i S g ts sk) (hn : StampsLt i S g ts n) (hm : StampsLt i S g ts m) :
    StampsLt i S g ts (DY.Signature.sign sk n m) :=
  (stampsLt_sign_pack i S g ts ⟨sk, n, m⟩).mpr ⟨hsk, hn, hm⟩
theorem stampsLt_kdfExtract {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {s ikm : DY.Bytes}
    (hs : StampsLt i S g ts s) (hikm : StampsLt i S g ts ikm) : StampsLt i S g ts (DY.KdfExtract.kdfExtract s ikm) :=
  (stampsLt_kdf_pack i S g ts ⟨s, ikm⟩).mpr ⟨hs, hikm⟩
theorem stampsLt_symEnc {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {k iv m : DY.Bytes}
    (hk : StampsLt i S g ts k) (hiv : StampsLt i S g ts iv) (hm : StampsLt i S g ts m) :
    StampsLt i S g ts (DY.SymEnc.symEnc k iv m) :=
  (stampsLt_sym_pack i S g ts ⟨k, iv, m⟩).mpr ⟨hk, hiv, hm⟩
theorem stampsLt_symDec {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {k iv ct m : DY.Bytes}
    (hdec : DY.SymEnc.symDec k iv ct = some m) (hct : StampsLt i S g ts ct) : StampsLt i S g ts m := by
  rw [DY.SymEnc.symDec_eq_some k iv ct m hdec] at hct
  exact ((stampsLt_sym_pack i S g ts ⟨k, iv, m⟩).mp hct).2.2
theorem stampsLt_trunc8 {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {x : DY.Bytes}
    (hx : StampsLt i S g ts x) : StampsLt i S g ts (DY.Trunc.trunc8 x) :=
  (stampsLt_trunc_pack i S g ts ⟨x⟩).mpr hx
theorem stampsLt_trWireMsg {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {v : UInt8} {rk : DY.Bytes} {c pc : UInt32} {ct pq : DY.Bytes} {ev : DY.TrWire.EncodingVariation}
    (hrk : StampsLt i S g ts rk) (hct : StampsLt i S g ts ct) (hpq : StampsLt i S g ts pq) :
    StampsLt i S g ts (DY.TrWire.trWireMsg v rk c pc ct pq ev) :=
  (stampsLt_trWire_pack i S g ts ⟨v, rk, c, pc, ct, pq, ev⟩).mpr ⟨hrk, hct, hpq⟩
theorem stampsLt_spqrParams (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (dir : DY.Spqr.Direction) :
    StampsLt i S g ts (DY.Spqr.encodeSpqrDirectionParams dir) := stampsLt_literalToBytes i S g ts _
theorem stampsLt_spqrIdx (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (idx : UInt32) :
    StampsLt i S g ts (DY.Spqr.encodeSpqrIndexTerm idx) := stampsLt_literalToBytes i S g ts _
theorem stampsLt_zeroKey (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) :
    StampsLt i S g ts DY.Spqr.zeroKey := stampsLt_literalToBytes i S g ts _
theorem stampsLt_spqrInit {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {authKey params : DY.Bytes} (ha : StampsLt i S g ts authKey) (hp : StampsLt i S g ts params) :
    StampsLt i S g ts (DY.Spqr.spqrInit authKey params) :=
  (stampsLt_spqrInit_pack i S g ts ⟨authKey, params⟩).mpr ⟨ha, hp⟩
theorem stampsLt_spqrChainKey {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {authKey params idx : DY.Bytes} (ha : StampsLt i S g ts authKey) (hp : StampsLt i S g ts params)
    (hi : StampsLt i S g ts idx) : StampsLt i S g ts (DY.Spqr.spqrChainKey authKey params idx) :=
  (stampsLt_spqrChainKey_pack i S g ts ⟨authKey, params, idx⟩).mpr ⟨ha, hp, hi⟩

theorem stampsLt_spqrSend {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {st coins : DY.Bytes} (hst : StampsLt i S g ts st) (hc : StampsLt i S g ts coins) :
    StampsLt i S g ts (DY.Spqr.spqrSend st coins).1 ∧
    StampsLt i S g ts (DY.Spqr.spqrSend st coins).2.1 ∧
    StampsLt i S g ts (DY.Spqr.spqrSend st coins).2.2 := by
  refine ⟨(stampsLt_spqrSendState_pack i S g ts ⟨st, coins⟩).mpr ⟨hst, hc⟩, ?_,
    (stampsLt_spqrSendMsg_pack i S g ts ⟨st, coins⟩).mpr ⟨hst, hc⟩⟩
  have hpv := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
  unfold DY.Spqr.spqrSend; dsimp only; split
  · next authKey params hx =>
    have hst' := hst; rw [hx] at hpv; rw [← hpv] at hst'
    obtain ⟨ha, hp⟩ := (stampsLt_spqrInit_pack i S g ts ⟨authKey, params⟩).mp hst'
    exact stampsLt_spqrChainKey ha hp (stampsLt_spqrIdx i S g ts 1)
  · exact (stampsLt_spqrSendKey_pack i S g ts ⟨st, coins⟩).mpr ⟨hst, hc⟩

theorem stampsLt_spqrRecv {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {st msg st' key : DY.Bytes} {idx : UInt32}
    (hst : StampsLt i S g ts st) (hmsg : StampsLt i S g ts msg)
    (hrecv : DY.Spqr.spqrRecv st msg idx = some (st', key)) :
    StampsLt i S g ts st' ∧ StampsLt i S g ts key := by
  have hpv := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
  unfold DY.Spqr.spqrRecv at hrecv; split at hrecv
  · cases hrecv
  · dsimp only at hrecv; split at hrecv
    · next authKey params hx =>
      have hst' := hst; rw [hx] at hpv; rw [← hpv] at hst'
      obtain ⟨ha, _⟩ := (stampsLt_spqrInit_pack i S g ts ⟨authKey, params⟩).mp hst'
      split at hrecv
      · next dir _ =>
        injection hrecv with hrecv; injection hrecv with hst_eq hkey; subst hst_eq hkey
        refine ⟨(stampsLt_spqrRecvState_pack i S g ts ⟨st, msg⟩).mpr ⟨hst, hmsg⟩, ?_⟩
        split
        · exact stampsLt_zeroKey i S g ts
        · exact stampsLt_spqrChainKey ha (stampsLt_spqrParams i S g ts dir.flip)
            (stampsLt_spqrIdx i S g ts idx)
      · cases hrecv
    · injection hrecv with hrecv; injection hrecv with hst_eq hkey; subst hst_eq hkey
      exact ⟨(stampsLt_spqrRecvState_pack i S g ts ⟨st, msg⟩).mpr ⟨hst, hmsg⟩,
        (stampsLt_spqrRecvKey_pack i S g ts ⟨st, msg⟩).mpr ⟨hst, hmsg⟩⟩

theorem attackerKnowledge_implies_stampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) :
    DY.SubAttackerKnowledge.Implies DY.AttackerKnowledge.attackerKnowledge (StampsLt i S g ts) := by
  change DY.SubAttackerKnowledge.Implies DY.Libsignal.Composed.attackerKnowledge (StampsLt i S g ts)
  dsimp [DY.Libsignal.Composed.attackerKnowledge]
  apply DY.SubAttackerKnowledge.combine.implies; intro id
  match id with
  | ⟨0, _⟩ =>
    dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DY.Random.attackerKnowledge]
    intro b h; rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at h; exact h.elim
  | ⟨1, _⟩ =>
    dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DY.Literal.attackerKnowledge]
    apply DY.SubAttackerKnowledge.combine'.implies
    intro ⟨0, _⟩ b h
    dsimp [DY.Literal.attackerKnowledge.internal] at h
    rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at h
    rcases h with ⟨lit, rfl⟩; exact stampsLt_lit i S g ts ⟨lit⟩
  | ⟨2, _⟩ =>
    dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DY.Concat.attackerKnowledge]
    apply DY.SubAttackerKnowledge.combine'.implies; intro id2
    match id2 with
    | ⟨0, _⟩ =>
      intro b h; dsimp [DY.Concat.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at h
      rcases h with ⟨l, r, rfl, hl, hr⟩; exact (stampsLt_concat_pack i S g ts ⟨l, r⟩).mpr ⟨hl, hr⟩
    | ⟨1, _⟩ =>
      intro b h; dsimp [DY.Concat.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at h
      rcases h with ⟨inp, r, idx, hsp, hinp⟩
      rw [← DY.Concat.concat_split inp idx b r hsp.symm] at hinp
      exact ((stampsLt_concat_pack i S g ts ⟨b, r⟩).mp hinp).1
    | ⟨2, _⟩ =>
      intro b h; dsimp [DY.Concat.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at h
      rcases h with ⟨inp, l, idx, hsp, hinp⟩
      rw [← DY.Concat.concat_split inp idx l b hsp.symm] at hinp
      exact ((stampsLt_concat_pack i S g ts ⟨l, b⟩).mp hinp).2
  | ⟨3, _⟩ =>
    dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DY.DiffieHellman.attackerKnowledge]
    apply DY.SubAttackerKnowledge.combine'.implies; intro id2
    match id2 with
    | ⟨0, _⟩ =>
      intro b h; dsimp [DY.DiffieHellman.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at h
      rcases h with ⟨sk, rfl, hsk⟩; exact (stampsLt_dhPk_pack i S g ts ⟨sk⟩).mpr hsk
    | ⟨1, _⟩ =>
      intro b h; dsimp [DY.DiffieHellman.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at h
      rcases h with ⟨pk, sk, rfl, hpk, hsk⟩; exact stampsLt_dh hpk hsk
  | ⟨4, _⟩ =>
    dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DY.KdfExtract.attackerKnowledge]
    apply DY.SubAttackerKnowledge.combine'.implies
    intro ⟨0, _⟩ b h
    dsimp [DY.KdfExtract.attackerKnowledge.internal] at h
    rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at h
    rcases h with ⟨salt, ikm, rfl, ha, hb⟩; exact (stampsLt_kdf_pack i S g ts ⟨salt, ikm⟩).mpr ⟨ha, hb⟩
  | ⟨5, _⟩ =>
    apply DY.SubAttackerKnowledge.combine'.implies; intro id2
    match id2 with
    | ⟨0, _⟩ => rintro b ⟨k, iv, msg, rfl, hk, hiv, hm⟩; exact (stampsLt_sym_pack i S g ts ⟨k, iv, msg⟩).mpr ⟨hk, hiv, hm⟩
    | ⟨1, _⟩ =>
      rintro b ⟨k, iv, ct, hdec, _, _, hct⟩
      rw [DY.SymEnc.symDec_eq_some k iv ct b hdec.symm] at hct
      exact ((stampsLt_sym_pack i S g ts ⟨k, iv, b⟩).mp hct).2.2
  | ⟨6, _⟩ =>
    apply DY.SubAttackerKnowledge.combine'.implies
    intro ⟨0, _⟩; rintro b ⟨inp, rfl, ha⟩; exact (stampsLt_trunc_pack i S g ts ⟨inp⟩).mpr ha
  | ⟨7, _⟩ =>
    apply DY.SubAttackerKnowledge.combine'.implies; intro id2
    match id2 with
    | ⟨0, _⟩ =>
      rintro b ⟨key, v, t, rfl, hk⟩
      have hk' := stampsLt_x25519Key hk
      dsimp only [DY.X25519.x25519TorsionVariant]
      split
      · exact hk'
      · exact (stampsLt_variant_pack i S g ts ⟨DY.X25519.normalizeX25519Key key, v, t⟩).mpr hk'
    | ⟨1, _⟩ => rintro b ⟨x, hx, rfl⟩; exact (stampsLt_variant_pack i S g ts x).mp hx
  | ⟨8, _⟩ =>
    apply DY.SubAttackerKnowledge.combine'.implies; intro id2
    match id2 with
    | ⟨0, _⟩ => rintro b ⟨sk, rfl, hsk⟩; exact stampsLt_kemPk hsk
    | ⟨1, _⟩ =>
      rintro b ⟨pk, e, rhs, heq, hpk, he⟩
      have h1 : b = (DY.PQKem.kemEncap pk e).1 := congrArg Prod.fst heq
      rw [h1]; exact (stampsLt_kemEncap hpk he).1
    | ⟨2, _⟩ =>
      rintro b ⟨pk, e, lhs, heq, hpk, he⟩
      have h2 : b = (DY.PQKem.kemEncap pk e).2 := congrArg Prod.snd heq
      rw [h2]; exact (stampsLt_kemEncap hpk he).2
    | ⟨3, _⟩ => rintro b ⟨sk, ct, hdec, _, hct⟩; exact stampsLt_kemDecap hdec.symm hct
    | ⟨4, _⟩ => rintro b ⟨sk, ct, rfl, hsk, hct⟩; exact stampsLt_kemRejKey hsk hct
  | ⟨9, _⟩ =>
    dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DY.Signature.attackerKnowledge]
    apply DY.SubAttackerKnowledge.combine'.implies; intro id2
    match id2 with
    | ⟨0, _⟩ =>
      intro b h; dsimp [DY.Signature.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at h
      rcases h with ⟨sk, rfl, hsk⟩; exact stampsLt_vk hsk
    | ⟨1, _⟩ =>
      intro b h; dsimp [DY.Signature.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at h
      rcases h with ⟨sk, nonce, msg, rfl, hsk, hn, hm⟩; exact stampsLt_sign hsk hn hm
  | ⟨10, _⟩ =>
    apply DY.SubAttackerKnowledge.combine'.implies; intro id2
    match id2 with
    | ⟨0, _⟩ => rintro b ⟨authKey, params, rfl, ha, hp⟩; exact stampsLt_spqrInit ha hp
    | ⟨1, _⟩ => rintro b ⟨authKey, params, idx, rfl, ha, hp, hi⟩; exact stampsLt_spqrChainKey ha hp hi
    | ⟨2, _⟩ => rintro b ⟨st, coins, rfl, hst, hc⟩; exact (stampsLt_spqrSend hst hc).1
    | ⟨3, _⟩ => rintro b ⟨st, coins, rfl, hst, hc⟩; exact (stampsLt_spqrSend hst hc).2.1
    | ⟨4, _⟩ => rintro b ⟨st, coins, rfl, hst, hc⟩; exact (stampsLt_spqrSend hst hc).2.2
    | ⟨5, _⟩ => rintro b ⟨st, msg, idx, ⟨st', key⟩, hrecv, rfl, hst, hmsg⟩; exact (stampsLt_spqrRecv hst hmsg hrecv).1
    | ⟨6, _⟩ => rintro b ⟨st, msg, idx, ⟨st', key⟩, hrecv, rfl, hst, hmsg⟩; exact (stampsLt_spqrRecv hst hmsg hrecv).2
    | ⟨7, _⟩ =>
      rintro b (⟨x, hx, rfl | rfl⟩ | ⟨x, hx, rfl | rfl⟩ | ⟨x, hx, rfl | rfl⟩)
      · exact ((stampsLt_spqrInit_pack i S g ts x).mp hx).1
      · exact ((stampsLt_spqrInit_pack i S g ts x).mp hx).2
      · exact ((stampsLt_spqrSendState_pack i S g ts x).mp hx).1
      · exact ((stampsLt_spqrSendState_pack i S g ts x).mp hx).2
      · exact ((stampsLt_spqrRecvState_pack i S g ts x).mp hx).1
      · exact ((stampsLt_spqrRecvState_pack i S g ts x).mp hx).2
  | ⟨11, _⟩ =>
    apply DY.SubAttackerKnowledge.combine'.implies; intro id2
    match id2 with
    | ⟨0, _⟩ =>
      rintro b ⟨x, rfl, hrk, hct, hpq⟩
      exact (stampsLt_trWire_pack i S g ts x).mpr ⟨hrk, hct, hpq⟩
    | ⟨1, _⟩ =>
      rintro b ⟨x, hx, harg⟩
      have h3 := (stampsLt_trWire_pack i S g ts x).mp hx
      rcases harg with rfl | rfl | rfl
      · exact h3.1
      · exact h3.2.1
      · exact h3.2.2

theorem attackerKnows_stampsLt {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {tr : ExecTrace} (hbase : ∀ m, tr.BaseAttackerKnows m → StampsLt i S g ts m)
    {b : DY.Bytes} (hkn : b.AttackerKnows tr) : StampsLt i S g ts b := by
  refine DY.Bytes.AttackerKnows.is_least_fixpoint (StampsLt i S g ts) b tr
    (attackerKnowledge_implies_stampsLt i S g ts) (fun m hm => ?_) hkn
  simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, DY.SubAttackerKnowledge.fromPred] at hm
  exact hbase m hm

theorem stampsLt_hmac {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {k m : DY.Bytes}
    (hk : StampsLt i S g ts k) (hm : StampsLt i S g ts m) : StampsLt i S g ts (hmac k m) :=
  stampsLt_kdfExtract hk hm
theorem stampsLt_hkdfBlock1 {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {prk info : DY.Bytes}
    (hprk : StampsLt i S g ts prk) (hinfo : StampsLt i S g ts info) : StampsLt i S g ts (hkdfBlock1 prk info) :=
  stampsLt_hmac hprk (stampsLt_concat hinfo (stampsLt_literalToBytes i S g ts _))
theorem stampsLt_hkdfBlock2 {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {prk info : DY.Bytes}
    (hprk : StampsLt i S g ts prk) (hinfo : StampsLt i S g ts info) : StampsLt i S g ts (hkdfBlock2 prk info) :=
  stampsLt_hmac hprk (stampsLt_concat (stampsLt_hkdfBlock1 hprk hinfo)
    (stampsLt_concat hinfo (stampsLt_literalToBytes i S g ts _)))
theorem stampsLt_hkdfBlock3 {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {prk info : DY.Bytes}
    (hprk : StampsLt i S g ts prk) (hinfo : StampsLt i S g ts info) : StampsLt i S g ts (hkdfBlock3 prk info) :=
  stampsLt_hmac hprk (stampsLt_concat (stampsLt_hkdfBlock2 hprk hinfo)
    (stampsLt_concat hinfo (stampsLt_literalToBytes i S g ts _)))
theorem stampsLt_kdfRk {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {rk dhOut : DY.Bytes}
    (hrk : StampsLt i S g ts rk) (hdh : StampsLt i S g ts dhOut) :
    StampsLt i S g ts (kdfRk rk dhOut).1 ∧ StampsLt i S g ts (kdfRk rk dhOut).2 :=
  ⟨stampsLt_hkdfBlock1 (stampsLt_hmac hrk hdh) (stampsLt_literalToBytes i S g ts _),
   stampsLt_hkdfBlock2 (stampsLt_hmac hrk hdh) (stampsLt_literalToBytes i S g ts _)⟩
theorem stampsLt_createChain {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {rk pk sk : DY.Bytes}
    (hrk : StampsLt i S g ts rk) (hpk : StampsLt i S g ts pk) (hsk : StampsLt i S g ts sk) :
    StampsLt i S g ts (createChain rk pk sk).1 ∧ StampsLt i S g ts (createChain rk pk sk).2 :=
  stampsLt_kdfRk hrk (stampsLt_dh (stampsLt_x25519Key hpk) hsk)
theorem stampsLt_kdfCk {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {ck : DY.Bytes}
    (hck : StampsLt i S g ts ck) : StampsLt i S g ts (kdfCk ck).1 ∧ StampsLt i S g ts (kdfCk ck).2 :=
  ⟨stampsLt_hmac hck (stampsLt_literalToBytes i S g ts _), stampsLt_hmac hck (stampsLt_literalToBytes i S g ts _)⟩
theorem stampsLt_chainKeyAt {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} :
    ∀ {ck : DY.Bytes} (n : Nat), StampsLt i S g ts ck → StampsLt i S g ts (chainKeyAt ck n)
  | _, 0, hck => hck
  | _, n + 1, hck => stampsLt_chainKeyAt n (stampsLt_kdfCk hck).1

theorem stampsLt_trMsgKeys {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {pqSalt seed : DY.Bytes} (hpq : StampsLt i S g ts pqSalt) (hs : StampsLt i S g ts seed) :
    StampsLt i S g ts (trMsgKeys pqSalt seed).cipherKey ∧
    StampsLt i S g ts (trMsgKeys pqSalt seed).macKey ∧
    StampsLt i S g ts (trMsgKeys pqSalt seed).iv := by
  have hp : StampsLt i S g ts (hmac pqSalt seed) := stampsLt_hmac hpq hs
  have hi : StampsLt i S g ts (lit "WhisperMessageKeys") :=
    stampsLt_literalToBytes i S g ts ("WhisperMessageKeys".toUTF8)
  exact ⟨stampsLt_hkdfBlock1 hp hi, stampsLt_hkdfBlock2 hp hi, stampsLt_hkdfBlock3 hp hi⟩

theorem stampsLt_computeMac {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {mk sik rik w : DY.Bytes} (hmk : StampsLt i S g ts mk) (hsik : StampsLt i S g ts sik)
    (hrik : StampsLt i S g ts rik) (hw : StampsLt i S g ts w) :
    StampsLt i S g ts (computeMac mk sik rik w) :=
  stampsLt_trunc8 (stampsLt_hmac hmk (stampsLt_concat hsik (stampsLt_concat hrik hw)))

theorem stampsLt_trHonestWireMsg {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {rk ct pq : DY.Bytes} (hrk : StampsLt i S g ts rk) (c pc : UInt32)
    (hct : StampsLt i S g ts ct) (hpq : StampsLt i S g ts pq) :
    StampsLt i S g ts (trHonestWireMsg rk c pc ct pq) :=
  stampsLt_trWireMsg hrk hct hpq

/-! ## State, visible-entry, and trace-entry stamp predicates -/

def StateStampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (st : TRState) : Prop :=
  StampsLt i S g ts st.myIk ∧ StampsLt i S g ts st.peerIk ∧ StampsLt i S g ts st.rk ∧
  StampsLt i S g ts st.dhs ∧ StampsLt i S g ts st.cks ∧ StampsLt i S g ts st.spqr ∧
  ∀ c ∈ st.recv, StampsLt i S g ts c.ratchetKey ∧ StampsLt i S g ts c.chainKey

theorem sessionOf_updateFreshAt_of_stampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ts n : Nat) (m : HwBytes) (st : TRState) (h : StateStampsLt i S g ts st) :
    sessionOf i (gamma i S { g with σ := updateFreshAt g.σ ts n m }) st =
      sessionOf i (gamma i S g) st := by
  rcases h with ⟨hmy, hpeer, hrk, hdhs, hcks, hspqr, hrecv⟩
  unfold sessionOf; dsimp only
  rw [gamma_updateFreshAt_of_stampsLt i S g ts n m st.dhs hdhs,
      gamma_updateFreshAt_of_stampsLt i S g ts n m st.myIk hmy,
      gamma_updateFreshAt_of_stampsLt i S g ts n m st.peerIk hpeer,
      gamma_updateFreshAt_of_stampsLt i S g ts n m st.rk hrk,
      gamma_updateFreshAt_of_stampsLt i S g ts n m st.cks hcks,
      gamma_updateFreshAt_of_stampsLt i S g ts n m st.spqr hspqr]
  congr 1; apply List.map_congr_left; intro c hc
  rw [gamma_updateFreshAt_of_stampsLt i S g ts n m c.ratchetKey (hrecv c hc).1,
      gamma_updateFreshAt_of_stampsLt i S g ts n m c.chainKey (hrecv c hc).2]

theorem stateRel_updateFreshAt_of_stampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ts n : Nat) (m : HwBytes) (st : TRState) (rec : RecordRec) (h : StateStampsLt i S g ts st) :
    StateRel i S { g with σ := updateFreshAt g.σ ts n m } st rec ↔ StateRel i S g st rec := by
  unfold StateRel; rw [sessionOf_updateFreshAt_of_stampsLt i S g ts n m st h]

theorem trKeyShape_updateFreshAt_of_stampsLt {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts n : Nat} {m : HwBytes} {st : TRState}
    (hlt : StateStampsLt i S g ts st) (h : TRKeyShape i S g st) :
    TRKeyShape i S { g with σ := updateFreshAt g.σ ts n m } st := by
  obtain ⟨hmy, hpeer, _, hdhs, hcks, _, _⟩ := hlt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gamma_updateFreshAt_of_stampsLt i S g ts n m _ hdhs]; exact h.dhs_len
  · rw [gamma_updateFreshAt_of_stampsLt i S g ts n m _ hcks]; exact h.cks_len
  · rw [gamma_updateFreshAt_of_stampsLt i S g ts n m _ hmy]; exact h.myIk_ser
  · rw [gamma_updateFreshAt_of_stampsLt i S g ts n m _ hpeer]; exact h.peerIk_ser

/-- Additional symbolic terms carried by a layout (`preKeyInner` base keys) and read by
`EventMatchesEntry` through `gamma`. -/
def layoutKeys : VisByteLayout → List DY.Bytes
  | .preKeyInner eks => eks
  | _ => []

/-- Every symbolic term read by `gamma` when matching `v` has random timestamps below `ts`. -/
def VisStampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (v : VisEntry) : Prop :=
  (∀ t ∈ v.terms, StampsLt i S g ts t) ∧ ∀ t ∈ layoutKeys v.layout, StampsLt i S g ts t

theorem visStampsLt_of_terms {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {v : VisEntry} (hl : layoutKeys v.layout = []) (h : ∀ t ∈ v.terms, StampsLt i S g ts t) :
    VisStampsLt i S g ts v :=
  ⟨h, fun t ht => by rw [hl] at ht; cases ht⟩

theorem bundleMatches_updateFreshAt_of_visStampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ts n : Nat) (m b : HwBytes) (terms : List DY.Bytes)
    (hv : ∀ t ∈ terms, StampsLt i S g ts t) :
    PreKeyBundleLayoutMatches i S { g with σ := updateFreshAt g.σ ts n m } b terms ↔
      PreKeyBundleLayoutMatches i S g b terms := by
  match terms with
  | [spk, spkSig, pqpk, pqpkSig] =>
    simp only [PreKeyBundleLayoutMatches, BundleSignedKeysMatch,
      gamma_updateFreshAt_of_stampsLt i S g ts n m spk (hv spk (by simp)),
      gamma_updateFreshAt_of_stampsLt i S g ts n m spkSig (hv spkSig (by simp)),
      gamma_updateFreshAt_of_stampsLt i S g ts n m pqpk (hv pqpk (by simp)),
      gamma_updateFreshAt_of_stampsLt i S g ts n m pqpkSig (hv pqpkSig (by simp))]
  | [spk, spkSig, pqpk, pqpkSig, opk] =>
    simp only [PreKeyBundleLayoutMatches, BundleSignedKeysMatch,
      gamma_updateFreshAt_of_stampsLt i S g ts n m spk (hv spk (by simp)),
      gamma_updateFreshAt_of_stampsLt i S g ts n m spkSig (hv spkSig (by simp)),
      gamma_updateFreshAt_of_stampsLt i S g ts n m pqpk (hv pqpk (by simp)),
      gamma_updateFreshAt_of_stampsLt i S g ts n m pqpkSig (hv pqpkSig (by simp)),
      gamma_updateFreshAt_of_stampsLt i S g ts n m opk (hv opk (by simp))]
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem sendMatches_updateFreshAt_of_visStampsLt (i : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (initIds : Option BundlePreKeyIds)
    (ts n : Nat) (m b : HwBytes) (terms : List DY.Bytes)
    (hv : ∀ t ∈ terms, StampsLt i S g ts t) :
    SendMatches i r S { g with σ := updateFreshAt g.σ ts n m } initIds b terms ↔
      SendMatches i r S g initIds b terms := by
  match terms with
  | [ek, ct, msg] =>
    simp only [SendMatches,
      gamma_updateFreshAt_of_stampsLt i S g ts n m ek (hv ek (by simp)),
      gamma_updateFreshAt_of_stampsLt i S g ts n m ct (hv ct (by simp)),
      gamma_updateFreshAt_of_stampsLt i S g ts n m msg (hv msg (by simp))]
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => rfl

theorem preKeyRecvMatches_updateFreshAt_of_visStampsLt (i : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ts n : Nat) (m b : HwBytes) (terms : List DY.Bytes)
    (hv : ∀ t ∈ terms, StampsLt i S g ts t) :
    PreKeyRecvMatches i r S { g with σ := updateFreshAt g.σ ts n m } b terms ↔
      PreKeyRecvMatches i r S g b terms := by
  match terms with
  | [ek, ct, msg] =>
    simp only [PreKeyRecvMatches,
      gamma_updateFreshAt_of_stampsLt i S g ts n m ek (hv ek (by simp)),
      gamma_updateFreshAt_of_stampsLt i S g ts n m ct (hv ct (by simp)),
      gamma_updateFreshAt_of_stampsLt i S g ts n m msg (hv msg (by simp))]
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => rfl

theorem preKeyRecvOpkMatches_updateFreshAt_of_visStampsLt (i : ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ts n : Nat) (m b : HwBytes) (terms : List DY.Bytes)
    (hv : ∀ t ∈ terms, StampsLt i S g ts t) :
    PreKeyRecvOpkMatches i r S { g with σ := updateFreshAt g.σ ts n m } b terms ↔
      PreKeyRecvOpkMatches i r S g b terms := by
  match terms with
  | [ek, ct, msg] =>
    exact and_congr_left fun _ =>
      preKeyRecvMatches_updateFreshAt_of_visStampsLt i r S g ts n m b [ek, ct, msg] hv
  | [ek, ct, msg, _opk] =>
    exact and_congr_left fun _ =>
      preKeyRecvMatches_updateFreshAt_of_visStampsLt i r S g ts n m b [ek, ct, msg]
        (fun t ht => hv t (by simp at ht; rcases ht with rfl | rfl | rfl <;> simp))
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem eventMatchesEntry_updateFreshAt_of_visStampsLt (i : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ts n : Nat) (m : HwBytes) (e : MachineEvent) (v : VisEntry)
    (hv : VisStampsLt i S g ts v) :
    EventMatchesEntry i r S { g with σ := updateFreshAt g.σ ts n m } e v ↔
      EventMatchesEntry i r S g e v := by
  have hmap : v.terms.map (gamma i S { g with σ := updateFreshAt g.σ ts n m }) =
      v.terms.map (gamma i S g) :=
    List.map_congr_left fun t ht => gamma_updateFreshAt_of_stampsLt i S g ts n m t (hv.1 t ht)
  have hkeys := hv.2
  have hv := hv.1
  unfold EventMatchesEntry; apply and_congr_right; intro _; dsimp only
  cases hl : v.layout with
  | single => rw [hmap]
  | whisper =>
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [gamma_updateFreshAt_of_stampsLt i S g ts n m t (hv t (by simp [ht]))]
  | bundle => exact bundleMatches_updateFreshAt_of_visStampsLt i S g ts n m (eventBytes e) v.terms hv
  | preKeySend =>
    exact exists_congr fun ids =>
      sendMatches_updateFreshAt_of_visStampsLt i r S g (some ids) ts n m (eventBytes e) v.terms hv
  | preKeyRecv => exact preKeyRecvOpkMatches_updateFreshAt_of_visStampsLt i r S g ts n m (eventBytes e) v.terms hv
  | preKeyInner eks =>
    rw [hl] at hkeys
    refine exists_congr fun t => exists_congr fun p => and_congr_right fun ht => and_congr_right fun _ => ?_
    rw [gamma_updateFreshAt_of_stampsLt i S g ts n m t (hv t (by simp [ht]))]
    refine and_congr_left fun _ => exists_congr fun ek => and_congr_right fun hek => ?_
    rw [gamma_updateFreshAt_of_stampsLt i S g ts n m ek (hkeys ek hek)]
  | fresh _ => rfl
  | kyberCoin j =>
    apply and_congr_right; intro _
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [gamma_updateFreshAt_of_stampsLt i S g ts n m t (hv t (by simp [ht]))]
  | unconstrained => rfl
  | leakPq pq => cases pq <;> simp [hmap]
  | leakRecord =>
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [gamma_updateFreshAt_of_stampsLt i S g ts n m t (hv t (by simp [ht]))]

def EventStampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) : TREvent → Prop
  | .SkippedKeyStored _ pk _ seed _ _ => StampsLt i S g ts seed ∧ StampsLt i S g ts pk
  | .ExposedMK _ seed _ _ => StampsLt i S g ts seed
  | .ExposedSpqr _ spqr _ => StampsLt i S g ts spqr
  | .Received _ _ _ _ m => StampsLt i S g ts m
  | _ => True

def PQEventStampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) : PQXDHEvent → Prop
  | .IdentityRegistered _ ikPk vk _ => StampsLt i S g ts ikPk ∧ StampsLt i S g ts vk
  | .BobDone _ _ _ _ _ _ _ ek _ _ => StampsLt i S g ts ek
  | _ => True

def EntryStampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat)
    (ent : ExecTrace.Entry) : Prop :=
  (∀ e : Network.ExecEntryT, TraceEntryHas.proj ent = some e → StampsLt i S g ts e.msg) ∧
  (∀ e : StEntry, TraceEntryHas.proj ent = some e → StateStampsLt i S g ts e.st.state) ∧
  (∀ e : TREntry, TraceEntryHas.proj ent = some e → EventStampsLt i S g ts e.ev) ∧
  (∀ e : PQStEntry, TraceEntryHas.proj ent = some e → StampsLt i S g ts e.st.state.sk) ∧
  (∀ e : PQEvEntry, TraceEntryHas.proj ent = some e → PQEventStampsLt i S g ts e.ev)

def TraceEntriesLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat)
    (tr : ExecTrace) : Prop :=
  (∀ b, tr.BaseAttackerKnows b → StampsLt i S g ts b) ∧
  (∀ j (hj : j < tr.length), EntryStampsLt i S g ts (tr.at j hj))

theorem traceEntriesLt_nil (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) :
    TraceEntriesLt i S g ts (DY.Trace.nil : ExecTrace) :=
  ⟨fun _ h => False.elim ((Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1 _).mp h),
    fun _ hj => by simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hj⟩

theorem traceEntriesLt_knows {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {tr : ExecTrace} (htr : TraceEntriesLt i S g ts tr) {b : DY.Bytes} (hkn : b.AttackerKnows tr) :
    StampsLt i S g ts b :=
  attackerKnows_stampsLt htr.1 hkn

theorem traceEntriesLt_append {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hbase : ∀ b, (tr.append e).BaseAttackerKnows b → StampsLt i S g ts b)
    (hent : EntryStampsLt i S g ts (TraceEntryHas.inj e))
    (htr : TraceEntriesLt i S g ts tr) :
    TraceEntriesLt i S g ts (tr.append e) := by
  refine ⟨hbase, fun j hj => ?_⟩
  by_cases hlt : j < tr.length
  · rw [← DY.Trace.at_le tr (tr.append e) j hlt (DY.Trace.append_le tr e)]; exact htr.2 j hlt
  · have heq : j = tr.length := by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hj; omega
    subst heq; simpa [Symbolic.DYBridge.DY.Trace.append_eq_1, DY.Trace.snoc, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] using hent

theorem traceEntriesLt_at?_net {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {tr : ExecTrace} (htr : TraceEntriesLt i S g ts tr) {j : Nat} {e : Network.ExecEntryT}
    (h : (tr.at? j : Option Network.ExecEntryT) = some e) : StampsLt i S g ts e.msg := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).1 e h
  · cases h

theorem traceEntriesLt_at?_st {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {tr : ExecTrace} (htr : TraceEntriesLt i S g ts tr) {j : Nat} {e : StEntry}
    (h : (tr.at? j : Option StEntry) = some e) : StateStampsLt i S g ts e.st.state := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).2.1 e h
  · cases h

theorem traceEntriesLt_at?_tr {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {tr : ExecTrace} (htr : TraceEntriesLt i S g ts tr) {j : Nat} {e : TREntry}
    (h : (tr.at? j : Option TREntry) = some e) : EventStampsLt i S g ts e.ev := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).2.2.1 e h
  · cases h

theorem traceEntriesLt_at?_pqst {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {tr : ExecTrace} (htr : TraceEntriesLt i S g ts tr) {j : Nat} {e : PQStEntry}
    (h : (tr.at? j : Option PQStEntry) = some e) : StampsLt i S g ts e.st.state.sk := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).2.2.2.1 e h
  · cases h

theorem traceEntriesLt_at?_pqev {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {tr : ExecTrace} (htr : TraceEntriesLt i S g ts tr) {j : Nat} {e : PQEvEntry}
    (h : (tr.at? j : Option PQEvEntry) = some e) : PQEventStampsLt i S g ts e.ev := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).2.2.2.2 e h
  · cases h
end Symbolic.Swarm.CREF.TR.FreshSigma
