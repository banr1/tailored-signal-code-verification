/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `PqRatchetState::encode_to_vec` (Block `426`): Budget-Threaded Specifications

Deterministic allocation envelope (`PqRatchetStateEncodeToVecEnv`) and pinned/unpinned
`RustCliAllocBudget M` specifications for `PqRatchetState::encode_to_vec` (`Block 426`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget

open Arm64 ProofLib
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withLsRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (PqRatchetState)
open CryptoVerification.LibsignalTripleRatchet (doReserveStackX)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStateEncodeToVecPinnedGhost PqRatchetStateEncodeToVecGhost
   pqRatchetStatePBPinnedAt pqRatchetStatePBAt pqRatchetStatePBAt_eq_exists_pinned
   pqRatchetStatePBEncodedLen pqRatchetStatePBEncodedLen_eq_proto
   encodeToVecStackOf blkPC_426 blkPl_426)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
   FitsEvents FitsEnv rustAllocEvents)

/-! ## 1. Deterministic Events & Envelope for `PqRatchetState::encode_to_vec` -/

/-- Deterministic `AllocEvent` list emitted by `PqRatchetState::encode_to_vec`:
    `[]` when `pqRatchetStatePBEncodedLen st = 0`, else `rustAllocEvents (pqRatchetStatePBEncodedLen st) 1`. -/
def pqRatchetStateEncodeToVecEvents (st : PqRatchetState) : List AllocEvent :=
  if pqRatchetStatePBEncodedLen st = 0 then []
  else rustAllocEvents (pqRatchetStatePBEncodedLen st) 1

/-- Concrete allocation envelope for `PqRatchetState::encode_to_vec`. -/
def PqRatchetStateEncodeToVecEnv (st : PqRatchetState) (evs : List AllocEvent) : Prop :=
  (pqRatchetStatePBEncodedLen st = 0 ∧ evs = []) ∨
  (0 < pqRatchetStatePBEncodedLen st ∧ evs = rustAllocEvents (pqRatchetStatePBEncodedLen st) 1)

theorem pqRatchetStateEncodeToVecEnv_events (st : PqRatchetState) :
    PqRatchetStateEncodeToVecEnv st (pqRatchetStateEncodeToVecEvents st) := by
  unfold PqRatchetStateEncodeToVecEnv pqRatchetStateEncodeToVecEvents
  by_cases h : pqRatchetStatePBEncodedLen st = 0
  · simp only [h, ↓reduceIte, true_and, true_or]
  · exact Or.inr ⟨Nat.pos_of_ne_zero h, by simp only [h, ↓reduceIte]⟩

theorem pqRatchetStateEncodeToVecEvents_eq_of_env {st : PqRatchetState} {evs : List AllocEvent}
    (h : PqRatchetStateEncodeToVecEnv st evs) :
    evs = pqRatchetStateEncodeToVecEvents st := by
  unfold pqRatchetStateEncodeToVecEvents
  rcases h with ⟨hz, rfl⟩ | ⟨hpos, rfl⟩
  · simp only [hz, ↓reduceIte]
  · simp only [Nat.ne_of_gt hpos, ↓reduceIte]

theorem fitsEvents_pqRatchetStateEncodeToVec_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits)
    (st_a : M.σ) (st : PqRatchetState) (h : FitsEnv M lim st_a (PqRatchetStateEncodeToVecEnv st)) :
    FitsEvents M lim st_a (pqRatchetStateEncodeToVecEvents st) :=
  h (pqRatchetStateEncodeToVecEvents st) (pqRatchetStateEncodeToVecEnv_events st)

/-! ## 2. Budget-Threaded Specifications for `PqRatchetState::encode_to_vec` -/

/-- Deterministic (`NoOom`) pinned specification of `PqRatchetState::encode_to_vec` (`Block 426`). -/
def pqRatchetStateEncodeToVecPinnedNoOomSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PqRatchetStateEncodeToVecPinnedGhost × M.σ) where
  pre := fun ⟨x, st_a⟩ s =>
    ⌜s.readReg64 .x0 = x.sret ∧
      s.readReg64 .x1 = x.a ∧
      (PqRatchetState.encodeRaw x.st).length < 2 ^ 63 ∧
      FitsEvents M lim st_a (pqRatchetStateEncodeToVecEvents x.st)⌝ ∗
      memRegion x.sret 24 ∗
      pqRatchetStatePBPinnedAt A.repAlloc x.g x.a x.st ∗
      A.pool lim st_a s ∗ stackAt s.sp (encodeToVecStackOf resStack)
  post := fun ⟨x, st_a⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A.repAlloc x.sret (PqRatchetState.encodeRaw x.st) ∗
      pqRatchetStatePBPinnedAt A.repAlloc x.g x.a x.st ∗
      A.pool lim (M.stepEvents (pqRatchetStateEncodeToVecEvents x.st) st_a) sf ∗
      stackAt s0.sp (encodeToVecStackOf resStack)

/-- Deterministic (`NoOom`) unpinned specification of `PqRatchetState::encode_to_vec` (`Block 426`). -/
def pqRatchetStateEncodeToVecNoOomSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PqRatchetStateEncodeToVecGhost × M.σ) where
  pre := fun ⟨x, st_a⟩ s =>
    ⌜s.readReg64 .x0 = x.sret ∧
      s.readReg64 .x1 = x.a ∧
      (PqRatchetState.encodeRaw x.st).length < 2 ^ 63 ∧
      FitsEvents M lim st_a (pqRatchetStateEncodeToVecEvents x.st)⌝ ∗
      memRegion x.sret 24 ∗
      pqRatchetStatePBAt A.repAlloc x.a x.st ∗
      A.pool lim st_a s ∗ stackAt s.sp (encodeToVecStackOf resStack)
  post := fun ⟨x, st_a⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A.repAlloc x.sret (PqRatchetState.encodeRaw x.st) ∗
      pqRatchetStatePBAt A.repAlloc x.a x.st ∗
      A.pool lim (M.stepEvents (pqRatchetStateEncodeToVecEvents x.st) st_a) sf ∗
      stackAt s0.sp (encodeToVecStackOf resStack)

/-- Envelope-parameterized pinned specification of `PqRatchetState::encode_to_vec`. -/
def pqRatchetStateEncodeToVecPinnedSpecOfEnv (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : PqRatchetState → List AllocEvent → Prop) :
    Spec (PqRatchetStateEncodeToVecPinnedGhost × M.σ) where
  pre := fun ⟨x, st_a⟩ s =>
    ⌜s.readReg64 .x0 = x.sret ∧
      s.readReg64 .x1 = x.a ∧
      (PqRatchetState.encodeRaw x.st).length < 2 ^ 63 ∧
      FitsEnv M lim st_a (Env x.st)⌝ ∗
      memRegion x.sret 24 ∗
      pqRatchetStatePBPinnedAt A.repAlloc x.g x.a x.st ∗
      A.pool lim st_a s ∗ stackAt s.sp (encodeToVecStackOf resStack)
  post := fun ⟨x, st_a⟩ s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x.st evs⌝ ∗
        vecU8 A.repAlloc x.sret (PqRatchetState.encodeRaw x.st) ∗
        pqRatchetStatePBPinnedAt A.repAlloc x.g x.a x.st ∗
        A.pool lim (M.stepEvents evs st_a) sf ∗
        stackAt s0.sp (encodeToVecStackOf resStack)

/-- Envelope-parameterized unpinned specification of `PqRatchetState::encode_to_vec`. -/
def pqRatchetStateEncodeToVecSpecOfEnv (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : PqRatchetState → List AllocEvent → Prop) :
    Spec (PqRatchetStateEncodeToVecGhost × M.σ) where
  pre := fun ⟨x, st_a⟩ s =>
    ⌜s.readReg64 .x0 = x.sret ∧
      s.readReg64 .x1 = x.a ∧
      (PqRatchetState.encodeRaw x.st).length < 2 ^ 63 ∧
      FitsEnv M lim st_a (Env x.st)⌝ ∗
      memRegion x.sret 24 ∗
      pqRatchetStatePBAt A.repAlloc x.a x.st ∗
      A.pool lim st_a s ∗ stackAt s.sp (encodeToVecStackOf resStack)
  post := fun ⟨x, st_a⟩ s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x.st evs⌝ ∗
        vecU8 A.repAlloc x.sret (PqRatchetState.encodeRaw x.st) ∗
        pqRatchetStatePBAt A.repAlloc x.a x.st ∗
        A.pool lim (M.stepEvents evs st_a) sf ∗
        stackAt s0.sp (encodeToVecStackOf resStack)

def pqRatchetStateEncodeToVecPinnedSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PqRatchetStateEncodeToVecPinnedGhost × M.σ) :=
  pqRatchetStateEncodeToVecPinnedSpecOfEnv resStack A lim PqRatchetStateEncodeToVecEnv

def pqRatchetStateEncodeToVecSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PqRatchetStateEncodeToVecGhost × M.σ) :=
  pqRatchetStateEncodeToVecSpecOfEnv resStack A lim PqRatchetStateEncodeToVecEnv

abbrev pqRatchetStateEncodeToVecPinnedSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PqRatchetStateEncodeToVecPinnedGhost × M.σ) :=
  pqRatchetStateEncodeToVecPinnedSpecOf 0x40 A lim

abbrev pqRatchetStateEncodeToVecSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PqRatchetStateEncodeToVecGhost × M.σ) :=
  pqRatchetStateEncodeToVecSpecOf 0x40 A lim

abbrev pqRatchetStateEncodeToVecPinnedSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PqRatchetStateEncodeToVecPinnedGhost × M.σ) :=
  pqRatchetStateEncodeToVecPinnedSpecOf doReserveStackX A lim

abbrev pqRatchetStateEncodeToVecSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PqRatchetStateEncodeToVecGhost × M.σ) :=
  pqRatchetStateEncodeToVecSpecOf doReserveStackX A lim

/-! ## 3. `NoOom` → `FitsEnv` and `Pinned` → `Unpinned` Lifting Bridges -/

theorem subroutine_ok_pqRatchetStateEncodeToVecPinned_of_noOom {prog : Program} {entry : BitVec 64}
    {resStack : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry (pqRatchetStateEncodeToVecPinnedNoOomSpecOf resStack A lim)) :
    subroutine_ok prog entry (pqRatchetStateEncodeToVecPinnedSpecOf resStack A lim) := by
  refine subroutine_ok_mono h ?_ ?_
  · intro ⟨x, st_a⟩ s R hpre
    dsimp only [pqRatchetStateEncodeToVecPinnedSpecOf, pqRatchetStateEncodeToVecPinnedSpecOfEnv,
      pqRatchetStateEncodeToVecPinnedNoOomSpecOf] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hlen, hfits⟩, hm⟩
    exact ⟨⟨hx0, hx1, hlen, fitsEvents_pqRatchetStateEncodeToVec_of_fitsEnv M lim st_a x.st hfits⟩, hm⟩
  · intro ⟨x, st_a⟩ s0 sf R hpost
    dsimp only [pqRatchetStateEncodeToVecPinnedSpecOf, pqRatchetStateEncodeToVecPinnedSpecOfEnv,
      pqRatchetStateEncodeToVecPinnedNoOomSpecOf] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨pqRatchetStateEncodeToVecEvents x.st, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hm⟩
    exact ⟨⟨htr, pqRatchetStateEncodeToVecEnv_events x.st⟩, hm⟩

theorem subroutine_ok_pqRatchetStateEncodeToVec_of_pinned {prog : Program} {entry : BitVec 64}
    {resStack : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : PqRatchetState → List AllocEvent → Prop}
    (hpinned : subroutine_ok prog entry (pqRatchetStateEncodeToVecPinnedSpecOfEnv resStack A lim Env)) :
    subroutine_ok prog entry (pqRatchetStateEncodeToVecSpecOfEnv resStack A lim Env) := by
  apply subroutine_ok_outcome_intro
  intro ⟨x, st_a⟩ R s0 hpc hrun hpre hsp
  dsimp only [pqRatchetStateEncodeToVecSpecOfEnv] at hpre
  rw [pqRatchetStatePBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨⟨x.sret, x.a, g, x.st⟩, st_a⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [pqRatchetStateEncodeToVecPinnedSpecOfEnv] at hpost
    dsimp only [pqRatchetStateEncodeToVecSpecOfEnv]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [pqRatchetStatePBAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ## 4. Placed Contract Propositions (`Block 426`) -/

def PqRatchetStateEncodeToVecPinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
    (blkPl_426).base
    (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecPinnedSpecX A lim)))

def PqRatchetStateEncodeToVecPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
    (blkPl_426).base
    (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecSpecX A lim)))

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
