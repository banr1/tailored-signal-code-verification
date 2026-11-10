/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WP.Structural

/-!
# Budget-Threaded Relocatable Hop Contracts for `main`

`RustCliAllocBudget M` counterparts of `HopsPlaced.lean` on Block `617` (`MainCalleesBlk617`,
`runSpecTightPlaced`, `retMem`, and `ExitKPlaced`), re-exporting allocator-free hop state predicates
from `HopsPlaced.lean`.
-/

@[expose] public section

set_option autoImplicit false

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs lsFromUtf8Sym)
open CryptoVerification.SignalSession.Cli (RunAnswer)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtRetPlaced RunCall fromUtf8AsciiSpec lsHandleErrorSymMain mProgPlaced mainFrameSize mainOom
   mainSaved strlenSpec)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget

open CryptoVerification.E2E.Pqxdh.Shared (TryAllocateInCall)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget RustLayoutOk)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (TryAllocateInEnv addressSpec reserve16Spec tryAllocateInSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced runSpecAnyPlaced runSpecPlaced)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)

/-- Total-correctness (`FitsEnv`) contract of `try_allocate_in` with `RustLayoutOk`
(`x.align.toNat ≤ 2 ^ 31`), matching `rustCliAllocNoOomSpec` and `finishGrowSpecX`. -/
def tryAllocateInRustSpecOf {M : AllocCostModel} (resStack : Nat) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TryAllocateInCall × M.σ) :=
  { tryAllocateInSpecOf resStack A lim with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.new ∧
        s.readReg64 .x2 = x.align ∧ s.readReg64 .x3 = x.stride ∧
        0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
        FitsEnv M lim st (TryAllocateInEnv x)⌝ ∗
      memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp resStack }

/-- Budget-threaded relocatable `MainCallees` on Block `617` (`address` at Block `580`,
`reserve16`/`reserve1` at Block `561`, and `tryAllocateIn3` at Block `588`). -/
structure MainCalleesBlk617 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (uuidParse : UuidParser) (hookStack resStack : Nat) : Prop where
  alloc : AllocContractsXCliPlaced A lim H
  allocFs : AllocContractsFsPlaced A lim H
  strlen : subroutine_ok (lsProg_617 H) (lsρ "strlen")
    (withLsRoCl lsmpl (withVmPreserved (strlenSpec hookStack)))
  fromUtf8 : subroutine_ok (lsProg_617 H) (lsρ lsFromUtf8Sym)
    (withLsRoCl lsmpl (withVmPreserved (fromUtf8AsciiSpec hookStack)))
  address : subroutine_ok (lsProg_617 H) (lsmpl.base 580)
    (withLsRoCl lsmpl (addressSpec A lim uuidParse resStack))
  reserve16 : subroutine_ok (lsProg_617 H) (lsmpl.base 561)
    (withLsRoCl lsmpl (reserve16Spec A lim resStack))
  reserve1 : subroutine_ok (lsProg_617 H) (lsmpl.base 561)
    (withLsRoCl lsmpl (doReserveSpecOf resStack A lim).keepsFs)
  tryAllocateIn3 : subroutine_ok (lsProg_617 H) (lsmpl.base 588)
    (withLsRoCl lsmpl (tryAllocateInRustSpecOf resStack A lim).keepsFs)
  handleErrorPanic : (lsProg_617 H).externAt? (lsρ lsHandleErrorSymMain) = some Rust.panicked

abbrev runSpecTightPlaced [LibsignalPlacement] := @runSpecPlaced

abbrev runSpecAnyTightPlaced [LibsignalPlacement] := @runSpecAnyPlaced

theorem subroutine_ok_runSpecPlaced_of_tight [LibsignalPlacement] {P : Program} {e : BitVec 64}
    {M : AllocCostModel} {CodeOk : Memory → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop} {uuidParse : UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    (h : subroutine_ok P e (runSpecTightPlaced CodeOk A lim RunEnv uuidParse Run wrOk resStack)) :
    subroutine_ok P e (runSpecPlaced CodeOk A lim RunEnv uuidParse Run wrOk resStack) :=
  h

theorem subroutine_ok_runSpecAnyPlaced_of_tight [LibsignalPlacement] {P : Program} {e : BitVec 64}
    {M : AllocCostModel} {CodeOk : Memory → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {uuidParse : UuidParser} {Run : Inputs → RunAnswer → Prop}
    {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    (h : subroutine_ok P e (runSpecAnyTightPlaced CodeOk A lim uuidParse Run wrOk resStack)) :
    subroutine_ok P e (runSpecAnyPlaced CodeOk A lim uuidParse Run wrOk resStack) :=
  h

/-- Memory owned on entry to `main`'s shared exit block under `RustCliAllocBudget M`
(`A.repAlloc.pool = emp`, absorbing remaining `A.pool lim st s` into `anyHeap`). -/
def retMem {M : AllocCostModel} (A : RustCliAllocBudget M) (s0 : State) (stk : Nat) : SepProp :=
  CryptoVerification.SignalSession.Cli.MainHops.retMem A.repAlloc s0 stk

def ExitKPlaced [LibsignalPlacement] {M : AllocCostModel} (CodeOk : Memory → Prop)
    (H : LibsignalHooks) (A : RustCliAllocBudget M) (s0 : State) (stk : Nat)
    (G : Nat → State → Prop) (Q Qp : State → SepProp → Prop) : Prop :=
  ∀ (s : State) (code : Nat), AtRetPlaced CodeOk s0 s code → G code s →
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s (retMem A s0 stk) Q Qp (mainOom s0)

theorem pool_anyHeap_entails_repPool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ∗ anyHeap ⊢ A.repAlloc.pool ∗ anyHeap := by
  rw [A.repAlloc_pool, emp_sepConj]
  exact entails_anyHeap _

theorem retMem_of_pool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State) (stk : Nat) :
    mainSaved s0 ∗ memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
      A.pool lim st s ∗ anyHeap ⊢
      retMem A s0 stk := by
  unfold retMem CryptoVerification.SignalSession.Cli.MainHops.retMem
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (pool_anyHeap_entails_repPool A lim st s)))

end LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
