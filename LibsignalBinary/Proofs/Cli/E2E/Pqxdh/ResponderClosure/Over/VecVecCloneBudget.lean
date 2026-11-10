/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecClone
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded `<Vec<Vec<u8>> as Clone>::clone` (`len = 1`) Helpers

Provides layout-independent frame predicates, budget-threaded return/panic continuations,
`VecVecClone1Env` projection lemmas, and heap-fold identities for `VecVecClonePlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecCloneBudget

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (arrayAt vecHeader vecU8 vecU8At)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (prevElem prevVecAt)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEvents FitsEnv fitsEvents_append rustAllocEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget (
  vecVecClone1StackX VecVecClone1Ghost
  vecVecClone1Events VecVecClone1Env vecVecClone1SpecX
)

/-! ## Frame and Cell Helpers -/

abbrev vvc1Cells :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vvc1Cells
abbrev vvc1Saved :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vvc1Saved
abbrev vvc1_stack_split :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vvc1_stack_split
abbrev vvc1_saved_cells :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vvc1_saved_cells
abbrev vvc1_mem24_cells :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vvc1_mem24_cells

/-! ## Budget-Threaded Return and Panic Obligations -/

/-- Return continuation for `vecVecClone1SpecX M A lim` at `(x, st)` with frame `R`. -/
def vvc1Q {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : VecVecClone1Ghost) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (vecVecClone1SpecX M A lim).post (x, st) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-- Panic continuation for `vecVecClone1SpecX M A lim` (`onPanic = ⌜False⌝`) with frame `R`. -/
def vvc1Qp {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : VecVecClone1Ghost) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (vecVecClone1SpecX M A lim).onPanic (x, st) s0 sf ∗ R)

theorem vvc1_panic_of_false {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : VecVecClone1Ghost} {st : M.σ} {s0 sf : State} {R P_f : SepProp} (hf : False) :
    vvc1Qp A lim x st s0 R sf P_f :=
  False.elim hf

/-! ## `VecVecClone1Env` and `FitsEvents` Projections -/

theorem fitsEvents_vecVecClone1_of_fitsEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : VecVecClone1Ghost} (h : FitsEnv M lim st (VecVecClone1Env x)) :
    FitsEvents M lim st (vecVecClone1Events x.enc) :=
  h (vecVecClone1Events x.enc) rfl

theorem fitsEvents_outer24_of_fitsEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : VecVecClone1Ghost} (h : FitsEnv M lim st (VecVecClone1Env x)) :
    FitsEvents M lim st (rustAllocEvents 24 8) := by
  have hfe := fitsEvents_vecVecClone1_of_fitsEnv h
  unfold vecVecClone1Events at hfe
  exact (fitsEvents_append M lim _ _ st).mp hfe |>.1

theorem fitsEvents_inner_of_fitsEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : VecVecClone1Ghost} (hpos : 0 < x.enc.length)
    (h : FitsEnv M lim st (VecVecClone1Env x)) :
    FitsEvents M lim (M.stepEvents (rustAllocEvents 24 8) st) (rustAllocEvents x.enc.length 1) := by
  have hfe := fitsEvents_vecVecClone1_of_fitsEnv h
  have hne : x.enc.length ≠ 0 := Nat.ne_of_gt hpos
  unfold vecVecClone1Events at hfe
  simp only [hne, ↓reduceIte] at hfe
  exact (fitsEvents_append M lim _ _ st).mp hfe |>.2

theorem vecVecClone1Env_nil {x : VecVecClone1Ghost} (henc : x.enc = []) :
    VecVecClone1Env x (rustAllocEvents 24 8) := by
  simp [VecVecClone1Env, vecVecClone1Events, henc]

theorem vecVecClone1Env_pos {x : VecVecClone1Ghost} (hpos : 0 < x.enc.length) :
    VecVecClone1Env x (rustAllocEvents 24 8 ++ rustAllocEvents x.enc.length 1) := by
  have hne : x.enc.length ≠ 0 := Nat.ne_of_gt hpos
  simp [VecVecClone1Env, vecVecClone1Events, hne]

theorem stepEvents_vecVecClone1_nil {M : AllocCostModel} (st : M.σ) {enc : List (BitVec 8)}
    (henc : enc = []) :
    M.stepEvents (rustAllocEvents 24 8) st = M.stepEvents (vecVecClone1Events enc) st := by
  simp [vecVecClone1Events, henc]

theorem stepEvents_vecVecClone1_pos {M : AllocCostModel} (st : M.σ) {enc : List (BitVec 8)}
    (hpos : 0 < enc.length) :
    M.stepEvents (rustAllocEvents enc.length 1) (M.stepEvents (rustAllocEvents 24 8) st) =
      M.stepEvents (vecVecClone1Events enc) st := by
  have hne : enc.length ≠ 0 := Nat.ne_of_gt hpos
  simp [vecVecClone1Events, hne, M.stepEvents_append]

/-! ## Budget-Threaded Heap Folds -/

theorem vvc1_src_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (src : BitVec 64) (enc : List (BitVec 8)) :
    arrayAt (prevElem A.repAlloc) 24 src [enc] =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜enc.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          vecHeader src cap ptr (BitVec.ofNat 64 enc.length) ∗
          (if cap = 0 then emp
           else A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ enc) ∗
             memRegion (ptr + BitVec.ofNat 64 enc.length) (cap.toNat - enc.length)) :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vvc1_src_eq A.repAlloc src enc

theorem vvc1_src_fold {M : AllocCostModel} (A : RustCliAllocBudget M)
    (src cap ptr : BitVec 64) (enc : List (BitVec 8))
    (h : enc.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) :
    vecHeader src cap ptr (BitVec.ofNat 64 enc.length) ∗
      (if cap = 0 then emp
       else A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ enc) ∗
         memRegion (ptr + BitVec.ofNat 64 enc.length) (cap.toNat - enc.length)) ⊢
      arrayAt (prevElem A.repAlloc) 24 src [enc] :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vvc1_src_fold A.repAlloc src cap ptr enc h

theorem vvc1_post_fold {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st' : M.σ) (sf : State) (src dst q : BitVec 64) (enc : List (BitVec 8)) (hq : q ≠ 0#64) :
    vecHeader dst 1#64 q 1#64 ∗
      (arrayAt (prevElem A.repAlloc) 24 src [enc] ∗ A.pool lim st' sf ∗
        A.repAlloc.live q 24 8 ∗ vecU8 A.repAlloc q enc) ⊢
      arrayAt (prevElem A.repAlloc) 24 src [enc] ∗
        (∃∗ q' : BitVec 64, prevVecAt A.repAlloc dst 1#64 q' [enc]) ∗ A.pool lim st' sf :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vvc1_post_fold
    (A.atState lim st' sf) src dst q enc hq

theorem vvc1_post_entails {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : VecVecClone1Ghost) (st : M.σ) (evs : List AllocEvent) (s0 sf : State) (q : BitVec 64)
    (htrace : sf.trace = s0.trace) (henv : VecVecClone1Env x evs) (hq : q ≠ 0#64) :
    (vecHeader x.dst 1#64 q 1#64 ∗
      (arrayAt (prevElem A.repAlloc) 24 x.src [x.enc] ∗ A.pool lim (M.stepEvents evs st) sf ∗
        A.repAlloc.live q 24 8 ∗ vecU8 A.repAlloc q x.enc)) ∗
      stackAt s0.sp vecVecClone1StackX ⊢
      (vecVecClone1SpecX M A lim).post (x, st) s0 sf := by
  dsimp only [vecVecClone1SpecX]
  refine Entails.sepExists_right evs ?_
  refine Entails.pure_right ⟨htrace, henv⟩ ?_
  refine Entails.trans (sepConj_mono_left
    (vvc1_post_fold A lim (M.stepEvents evs st) sf x.src x.dst q x.enc hq)) ?_
  exact Entails.of_eq (by sep_ac_rfl)

theorem vvc1_elem_nil {M : AllocCostModel} (A : RustCliAllocBudget M) (q : BitVec 64) :
    (q ↦₆₄ 0#64) ∗ ((q + 8#64) ↦₆₄ 1#64) ∗ ((q + 16#64) ↦₆₄ 0#64) ⊢ vecU8 A.repAlloc q [] :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vvc1_elem_nil A.repAlloc q

theorem vvc1_elem_cons {M : AllocCostModel} (A : RustCliAllocBudget M) (q p : BitVec 64)
    (enc : List (BitVec 8)) (hp : p ≠ 0#64) (hpos : 0 < enc.length) (hlt : enc.length < 2 ^ 63) :
    (q ↦₆₄ BitVec.ofNat 64 enc.length) ∗ ((q + 8#64) ↦₆₄ p) ∗ ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗
      A.repAlloc.live p enc.length 1 ∗ (p ↦ₛ enc) ⊢ vecU8 A.repAlloc q enc :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vvc1_elem_cons
    A.repAlloc q p enc hp hpos hlt

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecCloneBudget
