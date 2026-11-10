/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefs
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget -- shake: keep

/-!
# Budget-Threaded `<Vec<Vec<u8>> as Clone>::clone` Specification on 1 Element

Defines the deterministic event list `vecVecClone1Events`, envelope `VecVecClone1Env`, and
total-correctness budget contract `vecVecClone1SpecX` for `<Vec<Vec<u8>> as Clone>::clone` on `len = 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget

open Arm64 ProofLib
open CryptoVerification.RustHeap (arrayAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  prevElem prevVecAt vecVecClone1StackX VecVecClone1Ghost
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv rustAllocEvents
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)

abbrev vecVecClone1StackX : Nat :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vecVecClone1StackX
abbrev VecVecClone1Ghost :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecClone1Ghost

/-- Allocator events of `<Vec<Vec<u8>> as Clone>::clone` on `len = 1`: `rustAllocEvents 24 8` for
the outer buffer, plus `rustAllocEvents enc.length 1` when `enc ≠ []`. -/
def vecVecClone1Events (enc : List (BitVec 8)) : List AllocEvent :=
  rustAllocEvents 24 8 ++ (if enc.length = 0 then [] else rustAllocEvents enc.length 1)

/-- Exact allocator event envelope for `<Vec<Vec<u8>> as Clone>::clone` on `len = 1`. -/
def VecVecClone1Env (x : VecVecClone1Ghost) (evs : List AllocEvent) : Prop :=
  evs = vecVecClone1Events x.enc

theorem vecVecClone1Env_bounded {x : VecVecClone1Ghost} {evs : List AllocEvent}
    (henc : (AllocEvent.alloc x.enc.length).withinMaxAlloc) (h : VecVecClone1Env x evs) :
    BoundedRustEvs 2 (max 24 x.enc.length) evs := by
  subst h
  by_cases h0 : x.enc.length = 0
  · have hevs : vecVecClone1Events x.enc = [AllocEvent.alloc 24] := by
      simp [vecVecClone1Events, h0, rustAllocEvents]
    rw [hevs]
    refine ⟨by decide, fun ev hev => ?_⟩
    rcases List.mem_singleton.mp hev with rfl
    refine ⟨by decide, Nat.le_max_left 24 x.enc.length, ?_, ?_⟩
    · rintro _ _ ⟨⟩
    · rintro _ _ _ ⟨⟩
  · have h1 : 1 ≤ x.enc.length := Nat.pos_of_ne_zero h0
    have hevs : vecVecClone1Events x.enc =
        [AllocEvent.alloc 24, AllocEvent.alloc x.enc.length] := by
      simp [vecVecClone1Events, h0, h1, rustAllocEvents]
    rw [hevs]
    refine ⟨Nat.le_refl 2, fun ev hev => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl
    · refine ⟨by decide, Nat.le_max_left 24 x.enc.length, ?_, ?_⟩
      · rintro _ _ ⟨⟩
      · rintro _ _ _ ⟨⟩
    · refine ⟨henc, Nat.le_max_right 24 x.enc.length, ?_, ?_⟩
      · rintro _ _ ⟨⟩
      · rintro _ _ _ ⟨⟩

/-- Budget-threaded specification of `<Vec<Vec<u8>> as Clone>::clone` on `len = 1`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def vecVecClone1SpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (VecVecClone1Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧ s.readReg64 .x2 = 1#64 ∧
      FitsEnv M lim st (VecVecClone1Env x)⌝ ∗
      arrayAt (prevElem A.repAlloc) 24 x.src [x.enc] ∗ memRegion x.dst 24 ∗
      A.pool lim st s ∗ stackAt s.sp vecVecClone1StackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ VecVecClone1Env x evs⌝ ∗
      arrayAt (prevElem A.repAlloc) 24 x.src [x.enc] ∗
      (∃∗ q' : BitVec 64, prevVecAt A.repAlloc x.dst 1#64 q' [x.enc]) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp vecVecClone1StackX

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget
