/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs

/-!
# Budget-Threaded `SessionRecord::serialize` with One Previous Session

Allocation-budget envelope `SerializePrev1Env` and budget-threaded subroutine contracts
`serializePrev1SpecWithEnv` / `serializePrev1Spec` for `<SessionRecord>::serialize` on a record
with one archived previous session (`previous_sessions = [enc]`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  encodeRecordPrev1 encodeRecordPrev1_length_pos
  encodeRecordPrev1Mem encodeRecordPrev1Mem_eq_of_canon
  SerializePrev1Ghost
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEvents FitsEnv
  SeqEnv FreeOnlyEvs rustAllocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (segCloneEvents SegCloneEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget (
  vecVecClone1Events
)

abbrev SerializePrev1Ghost :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.SerializePrev1Ghost
abbrev encodeRecordPrev1 :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.encodeRecordPrev1
abbrev encodeRecordPrev1_length_pos :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.encodeRecordPrev1_length_pos
abbrev encodeRecordPrev1Mem :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.encodeRecordPrev1Mem
abbrev encodeRecordPrev1Mem_eq_of_canon :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.encodeRecordPrev1Mem_eq_of_canon

/-- Deterministic allocation prefix emitted by `<SessionRecord>::serialize` on `(G, sess, [enc])`
prior to epilogue drops: `SessionStructure::clone`, `<Vec<Vec<u8>> as Clone>::clone` on `[enc]`,
and output `Vec::with_capacity`. -/
def serializePrev1AllocPrefix (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) : List AllocEvent :=
  segCloneEvents G sess.state ++
    vecVecClone1Events enc ++
    rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1

/-- Bounded allocation-event envelope for `<SessionRecord>::serialize` on `(G, sess, [enc])`:
`SegCloneEnv G sess.state`, `vecVecClone1Events enc`, output `Vec::with_capacity`, and epilogue
`FreeOnlyEvs` drops. -/
def SerializePrev1Env (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (SegCloneEnv G sess.state)
    (SeqEnv (· = vecVecClone1Events enc)
      (SeqEnv (· = rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1) FreeOnlyEvs))

theorem SerializePrev1Env.of_steps {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {enc : List (BitVec 8)} {e1 e2 e3 e4 : List AllocEvent}
    (h1 : SegCloneEnv G sess.state e1)
    (h2 : e2 = vecVecClone1Events enc)
    (h3 : e3 = rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
    (h4 : FreeOnlyEvs e4) :
    SerializePrev1Env G sess enc (e1 ++ e2 ++ e3 ++ e4) := by
  rw [List.append_assoc, List.append_assoc]
  exact SeqEnv.append h1 (SeqEnv.append h2 (SeqEnv.append h3 h4))

theorem fitsEnv_segClone_of_serializePrev1 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (h : FitsEnv M lim st (SerializePrev1Env G sess enc)) :
    FitsEnv M lim st (SegCloneEnv G sess.state) :=
  h.seq_left

theorem fitsEvents_vecVecClone1_of_serializePrev1 {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {e1 : List AllocEvent}
    (h : FitsEnv M lim st (SerializePrev1Env G sess enc))
    (h1 : SegCloneEnv G sess.state e1) :
    FitsEvents M lim (M.stepEvents e1 st) (vecVecClone1Events enc) :=
  FitsEnv.eq_iff.mp (h.seq_right h1).seq_left

theorem fitsEvents_outAlloc_of_serializePrev1 {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {e1 : List AllocEvent}
    (h : FitsEnv M lim st (SerializePrev1Env G sess enc))
    (h1 : SegCloneEnv G sess.state e1) :
    FitsEvents M lim (M.stepEvents (e1 ++ vecVecClone1Events enc) st)
      (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1) := by
  rw [AllocCostModel.stepEvents_append]
  exact FitsEnv.eq_iff.mp ((h.seq_right h1).seq_right rfl).seq_left

/-- Envelope-parameterized budget-threaded contract for `<SessionRecord>::serialize` on a record
with current session `x.sess` and `previous_sessions = [x.enc]`. -/
def serializePrev1SpecWithEnv (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec (SerializePrev1Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (Env x.G x.sess x.enc)⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.serializePrev1Spec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜Env x.G x.sess x.enc evs⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.serializePrev1Spec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

def serializePrev1Spec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (SerializePrev1Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (SerializePrev1Env x.G x.sess x.enc)⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.serializePrev1Spec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜SerializePrev1Env x.G x.sess x.enc evs⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.serializePrev1Spec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

theorem subroutine_ok_serializePrev1SpecWithEnv_mono {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ :
      SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (himp : ∀ G sess enc evs, Env₁ G sess enc evs → Env₂ G sess enc evs)
    (h : subroutine_ok prog entry (serializePrev1SpecWithEnv M A lim Env₁)) :
    subroutine_ok prog entry (serializePrev1SpecWithEnv M A lim Env₂) := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ _ s0 hp => ?_)
    (fun ⟨x, st⟩ _ s0 sf hq => ?_)
  · dsimp only [serializePrev1SpecWithEnv] at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨hp.1.mono (himp x.G x.sess x.enc), hp.2⟩
  · dsimp only [serializePrev1SpecWithEnv] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨himp x.G x.sess x.enc evs hq.1, hq.2⟩

theorem subroutine_ok_serializePrev1Spec_of_withEnv {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (himp : ∀ G sess enc evs, Env G sess enc evs → SerializePrev1Env G sess enc evs)
    (h : subroutine_ok prog entry (serializePrev1SpecWithEnv M A lim Env)) :
    subroutine_ok prog entry (serializePrev1Spec M A lim) := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ _ s0 hp => ?_)
    (fun ⟨x, st⟩ _ s0 sf hq => ?_)
  · dsimp only [serializePrev1Spec, serializePrev1SpecWithEnv] at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨hp.1.mono (himp x.G x.sess x.enc), hp.2⟩
  · dsimp only [serializePrev1Spec, serializePrev1SpecWithEnv] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨himp x.G x.sess x.enc evs hq.1, hq.2⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget
