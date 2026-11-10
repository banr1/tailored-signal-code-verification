/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPost

/-!
# Budget-Threaded Postcondition and Epilogue Predicates for `SpkGetPoll`

Defines `spkPostQ`, `spkPanicQp`, and `spkEpiPre` over `CalleesBudget.spkGetPollInnerSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPostBudget

open Arm64 ProofLib
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule PkPollGhost dirAt)
open CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers
  (words11At spkPollSlack spkSavedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (spkGetPollInnerSpec)

def spkPostQ {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) (x : PkPollGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (spkGetPollInnerSpec rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk).post
          (x, st) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

def spkPanicQp {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) (x : PkPollGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (spkGetPollInnerSpec rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk).onPanic
          (x, st) s0 sf ∗ R)

def spkEpiPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (calleeStk : Nat) (x : PkPollGhost) (st' : M.σ) (s0 s : State)
    (D : SepProp)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64)
    (a0 o7 o8 o9 o10 : BitVec 64)
    (o5 o6 b2 b3 b4 : BitVec 64)
    (c0 c1 c2 c3 c4 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 : BitVec 64)
    (f0 f1 f2 f3 f4 : BitVec 64) : SepProp :=
  D ∗
  words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
  (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
  dirAt A.repAlloc x.self x.dir ∗ A.pool lim st' s ∗
  stackAt (s0.sp - 384#64) calleeStk ∗ spkPollSlack s0.sp ∗
  ((s0.sp - 376#64) ↦₆₄ a0) ∗ ((s0.sp - 368#64) ↦₆₄ o7) ∗ ((s0.sp - 360#64) ↦₆₄ o8) ∗
  ((s0.sp - 352#64) ↦₆₄ o9) ∗ ((s0.sp - 344#64) ↦₆₄ o10) ∗
  ((s0.sp - 336#64) ↦₆₄ o5) ∗ ((s0.sp - 328#64) ↦₆₄ o6) ∗ ((s0.sp - 320#64) ↦₆₄ b2) ∗
  ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4) ∗
  ((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
  ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4) ∗
  ((s0.sp - 248#64) ↦₆₄ d0) ∗ ((s0.sp - 240#64) ↦₆₄ d1) ∗ ((s0.sp - 232#64) ↦₆₄ d2) ∗
  ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4) ∗
  ((s0.sp - 200#64) ↦₆₄ e0) ∗ ((s0.sp - 192#64) ↦₆₄ e1) ∗ ((s0.sp - 184#64) ↦₆₄ e2) ∗
  ((s0.sp - 176#64) ↦₆₄ e3) ∗ ((s0.sp - 168#64) ↦₆₄ e4) ∗ ((s0.sp - 160#64) ↦₆₄ e5) ∗
  ((s0.sp - 152#64) ↦₆₄ f0) ∗ ((s0.sp - 144#64) ↦₆₄ f1) ∗ ((s0.sp - 136#64) ↦₆₄ f2) ∗
  ((s0.sp - 128#64) ↦₆₄ f3) ∗ ((s0.sp - 120#64) ↦₆₄ f4) ∗
  spkSavedAt s0

end LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPostBudget
