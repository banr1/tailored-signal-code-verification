/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.StdStartup.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `M24` ↔ `F3.L4B` `NeedLocks` Specification Equivalences

Establishes definitional and extensional equalities (`=`) and bi-implications (`↔`) between the
`NeedLocks`, `argvAtRO`, `cliProgExtPlacedAt`, `cliStaticsPlacedAt`, `MuslHarnessFineNeedLocksPerInput`,
and `MainOkCliExt*B2NeedLocksPlacedAt` definitions in `M24.{CliElfMallocngHarness,CliStrictPlaced}`
and `F3.L4B.{F3HarnessPlaced,CliStrictPlaced2}`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession (CliHooks CliRun Inputs Outcome cliExternsPlaced cliProcessInputs)
open CryptoVerification.SignalSession.Cli (MainGhost RunAnswer)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (FineBudget)

/-! ## `cStrAtRO`, `argvAtRO`, `B2MainEntryFacts`, and `b2MainSpecTightNeedLocksFineAt` -/

theorem cStrAtRO_eq (p : BitVec 64) (s : List (BitVec 8)) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.cStrAtRO p s =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.cStrAtRO p s :=
  rfl

theorem cStrAtRO_fun_eq :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.cStrAtRO =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.cStrAtRO :=
  rfl

theorem argvAtRO_eq : ∀ (a : BitVec 64) (ss : List (List (BitVec 8))),
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.argvAtRO a ss =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.argvAtRO a ss
  | _, [] => rfl
  | a, s :: ss => by
    simp only [LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.argvAtRO,
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.argvAtRO,
      cStrAtRO_eq, argvAtRO_eq (a + 8#64) ss]

theorem argvAtRO_fun_eq :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.argvAtRO =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.argvAtRO := by
  funext a ss
  exact argvAtRO_eq a ss

theorem B2MainEntryFacts_eq (inputsOf : Inputs → ProcessInputs) (i : Inputs) (s : State) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.B2MainEntryFacts inputsOf i s =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.B2MainEntryFacts inputsOf i s :=
  rfl

theorem B2MainEntryFacts_iff (inputsOf : Inputs → ProcessInputs) (i : Inputs) (s : State) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.B2MainEntryFacts inputsOf i s ↔
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.B2MainEntryFacts inputsOf i s :=
  Iff.rfl

theorem B2MainEntryFacts_fun_eq :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.B2MainEntryFacts =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.B2MainEntryFacts :=
  rfl

theorem b2MainFrameFine_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (stk : Nat) (Statics : SepProp) (i : Inputs) (s : State) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.b2MainFrameFine
        A lim st stk Statics i s =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainFrameFine
        A lim st stk Statics i s := by
  simp only [LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.b2MainFrameFine,
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainFrameFine,
    argvAtRO_eq]

theorem b2MainEntryPreFine_eq (CodeOk : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (stk : Nat)
    (Statics : SepProp) (i : Inputs) (s : State) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.b2MainEntryPreFine
        CodeOk A lim st stk Statics i s =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainEntryPreFine
        CodeOk A lim st stk Statics i s := by
  simp only [LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.b2MainEntryPreFine,
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainEntryPreFine,
    b2MainFrameFine_eq]

theorem b2MainSpecTightNeedLocksFineAt_eq (libcAddr : BitVec 64) (CodeOk : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (stk : Nat) (Statics : SepProp) (Run : Inputs → RunAnswer → Prop)
    (inputsOf : Inputs → ProcessInputs) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.b2MainSpecTightNeedLocksFineAt
        libcAddr CodeOk A lim st stk Statics Run inputsOf =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainSpecTightNeedLocksFineAt
        libcAddr CodeOk A lim st stk Statics Run inputsOf := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.b2MainSpecTightNeedLocksFineAt
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainSpecTightNeedLocksFineAt
  congr 1
  funext g s
  rw [B2MainEntryFacts_eq, b2MainFrameFine_eq]

/-! ## `cliProgExtPlacedAt` and `cliStaticsPlacedAt` -/

theorem cliProgExtPlacedAt_eq (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat) (W : CliHooks) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness.cliProgExtPlacedAt
        mpl ext idx W =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.cliProgExtPlacedAt
        mpl ext idx W :=
  rfl

theorem cliProgExtPlacedSigAt_eq (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat) (W : CliHooks) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness.cliProgExtPlacedSigAt
        mpl ext idx W =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.cliProgExtPlacedSigAt
        mpl ext idx W :=
  rfl

theorem cliRunsToExtOnInputsAt_eq (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat)
    (inputsOf : Inputs → ProcessInputs)
    (elf : ElfImage) (W : CliHooks) (i : Inputs) (o : Outcome) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness.CliRunsToExtOnInputsAt
        mpl ext idx inputsOf elf W i o =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.CliRunsToExtOnInputsAt
        mpl ext idx inputsOf elf W i o :=
  rfl

theorem cliRunsToExtPlacedAt_eq (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat)
    (elf : ElfImage) (W : CliHooks) (i : Inputs) (o : Outcome) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness.CliRunsToExtPlacedAt
        mpl ext idx elf W i o =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.CliRunsToExtPlacedAt
        mpl ext idx elf W i o :=
  rfl

theorem cliRunExtOnInputsSigAt_eq (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat)
    (inputsOf : Inputs → ProcessInputs)
    (elf : ElfImage) (W : CliHooks) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness.cliRunExtOnInputsSigAt
        mpl ext idx inputsOf elf W =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.cliRunExtOnInputsSigAt
        mpl ext idx inputsOf elf W :=
  rfl

theorem cliRunExtPlacedSigAt_eq (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat)
    (elf : ElfImage) (W : CliHooks) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness.cliRunExtPlacedSigAt
        mpl ext idx elf W =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.cliRunExtPlacedSigAt
        mpl ext idx elf W :=
  rfl

theorem coinsStaticsPlacedAt_eq (mpl : Obj.MultiPlacement) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.coinsStaticsPlacedAt mpl =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.coinsStaticsPlacedAt mpl :=
  rfl

theorem tokenInitPlacedAtMpl_eq (mpl : Obj.MultiPlacement) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.tokenInitPlacedAtMpl mpl =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.tokenInitPlacedAtMpl mpl :=
  rfl

theorem lsLogOffAt_eq (mpl : Obj.MultiPlacement) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.lsLogOffAt mpl =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.lsLogOffAt mpl :=
  rfl

theorem cliStaticsPlacedAt_eq (mpl : Obj.MultiPlacement) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.cliStaticsPlacedAt mpl =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.cliStaticsPlacedAt mpl :=
  rfl

/-! ## `subroutine_ok`, `MuslHarnessFineNeedLocksPerInput`, and `MainOkCliExt*` Bridges -/

theorem subroutine_ok_b2MainSpecTightNeedLocksFineAt_eq
    (mpl : Obj.MultiPlacement) (ext : CliHooks → String → Option (State → State))
    (idx : Nat) (W : CliHooks) (pc : BitVec 64)
    (libcAddr : BitVec 64) (CodeOk : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (stk : Nat) (Statics : SepProp) (Run : Inputs → RunAnswer → Prop)
    (inputsOf : Inputs → ProcessInputs) :
    subroutine_ok
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness.cliProgExtPlacedAt
          mpl ext idx W)
        pc
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.b2MainSpecTightNeedLocksFineAt
          libcAddr CodeOk A lim st stk Statics Run inputsOf) =
      subroutine_ok
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.cliProgExtPlacedAt
          mpl ext idx W)
        pc
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainSpecTightNeedLocksFineAt
          libcAddr CodeOk A lim st stk Statics Run inputsOf) := by
  rw [cliProgExtPlacedAt_eq, b2MainSpecTightNeedLocksFineAt_eq]

theorem subroutine_ok_b2MainSpecTightNeedLocksFineAt_iff
    (mpl : Obj.MultiPlacement) (ext : CliHooks → String → Option (State → State))
    (idx : Nat) (W : CliHooks) (pc : BitVec 64)
    (libcAddr : BitVec 64) (CodeOk : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (stk : Nat) (Statics : SepProp) (Run : Inputs → RunAnswer → Prop)
    (inputsOf : Inputs → ProcessInputs) :
    subroutine_ok
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness.cliProgExtPlacedAt
          mpl ext idx W)
        pc
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.b2MainSpecTightNeedLocksFineAt
          libcAddr CodeOk A lim st stk Statics Run inputsOf) ↔
      subroutine_ok
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.cliProgExtPlacedAt
          mpl ext idx W)
        pc
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainSpecTightNeedLocksFineAt
          libcAddr CodeOk A lim st stk Statics Run inputsOf) := by
  rw [subroutine_ok_b2MainSpecTightNeedLocksFineAt_eq]

theorem muslHarnessFineNeedLocksPerInput_eq
    (exitStk : Nat) (libcAddr : BitVec 64) (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs) (mmpl : Obj.MultiPlacement)
    (lim : BudgetLimits) (st : FineBudget) (stk : Nat)
    (CodeOk : Memory → Prop) (Statics : SepProp) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MuslHarnessFineNeedLocksPerInput
        exitStk libcAddr elf P mainPc inputsOf mmpl lim st stk CodeOk Statics =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MuslHarnessFineNeedLocksPerInput
        exitStk libcAddr elf P mainPc inputsOf mmpl lim st stk CodeOk Statics := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MuslHarnessFineNeedLocksPerInput
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MuslHarnessFineNeedLocksPerInput
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.b2MainEntryPreFine
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainEntryPreFine
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.b2MainFrameFine
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainFrameFine
  simp only [argvAtRO_eq]

theorem muslHarnessFineNeedLocksPerInput_iff
    (exitStk : Nat) (libcAddr : BitVec 64) (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs) (mmpl : Obj.MultiPlacement)
    (lim : BudgetLimits) (st : FineBudget) (stk : Nat)
    (CodeOk : Memory → Prop) (Statics : SepProp) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MuslHarnessFineNeedLocksPerInput
        exitStk libcAddr elf P mainPc inputsOf mmpl lim st stk CodeOk Statics ↔
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MuslHarnessFineNeedLocksPerInput
        exitStk libcAddr elf P mainPc inputsOf mmpl lim st stk CodeOk Statics := by
  rw [muslHarnessFineNeedLocksPerInput_eq]

theorem stdMainEntryLr_eq (L : ProofLib.StdStartup.StdBinaryLayout) (sm : State) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.StdMainEntryLr L sm =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.StdMainEntryLr L sm :=
  rfl

theorem stdMainEntryLr_fun_eq :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.StdMainEntryLr =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.StdMainEntryLr :=
  rfl

theorem muslHarnessFineNeedLocksGuardedPerInput_eq
    (exitStk : Nat) (libcAddr : BitVec 64) (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs) (mmpl : Obj.MultiPlacement)
    (lim : BudgetLimits) (st : FineBudget) (stk : Nat)
    (CodeOk : Memory → Prop) (Statics : SepProp) (EntryGuard : State → Prop) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MuslHarnessFineNeedLocksGuardedPerInput
        exitStk libcAddr elf P mainPc inputsOf mmpl lim st stk CodeOk Statics EntryGuard =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MuslHarnessFineNeedLocksGuardedPerInput
        exitStk libcAddr elf P mainPc inputsOf mmpl lim st stk CodeOk Statics EntryGuard := by
  unfold
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MuslHarnessFineNeedLocksGuardedPerInput
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MuslHarnessFineNeedLocksGuardedPerInput
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.b2MainEntryPreFine
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainEntryPreFine
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.b2MainFrameFine
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainFrameFine
  simp only [argvAtRO_eq]

theorem muslHarnessFineNeedLocksGuardedPerInput_iff
    (exitStk : Nat) (libcAddr : BitVec 64) (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs) (mmpl : Obj.MultiPlacement)
    (lim : BudgetLimits) (st : FineBudget) (stk : Nat)
    (CodeOk : Memory → Prop) (Statics : SepProp) (EntryGuard : State → Prop) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MuslHarnessFineNeedLocksGuardedPerInput
        exitStk libcAddr elf P mainPc inputsOf mmpl lim st stk CodeOk Statics EntryGuard ↔
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MuslHarnessFineNeedLocksGuardedPerInput
        exitStk libcAddr elf P mainPc inputsOf mmpl lim st stk CodeOk Statics EntryGuard := by
  rw [muslHarnessFineNeedLocksGuardedPerInput_eq]

theorem mainOkCliExtPqB2NeedLocksPlacedAt_eq
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MainOkCliExtPqB2NeedLocksPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliExtPqB2NeedLocksPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim := by
  simp only [LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MainOkCliExtPqB2NeedLocksPlacedAt,
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliExtPqB2NeedLocksPlacedAt,
    cliProgExtPlacedAt_eq, b2MainSpecTightNeedLocksFineAt_eq, cliStaticsPlacedAt_eq]

theorem mainOkCliExtPqB2NeedLocksPlacedAt_iff
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MainOkCliExtPqB2NeedLocksPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim ↔
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliExtPqB2NeedLocksPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim := by
  rw [mainOkCliExtPqB2NeedLocksPlacedAt_eq]

theorem mainOkCliExtOverB2NeedLocksPlacedAt_eq
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MainOkCliExtOverB2NeedLocksPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliExtOverB2NeedLocksPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim := by
  simp only [LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MainOkCliExtOverB2NeedLocksPlacedAt,
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliExtOverB2NeedLocksPlacedAt,
    cliProgExtPlacedAt_eq, b2MainSpecTightNeedLocksFineAt_eq, cliStaticsPlacedAt_eq]

theorem mainOkCliExtOverB2NeedLocksPlacedAt_iff
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MainOkCliExtOverB2NeedLocksPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim ↔
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliExtOverB2NeedLocksPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim := by
  rw [mainOkCliExtOverB2NeedLocksPlacedAt_eq]

theorem mainOkCliF3PqB2NeedLocksPlacedAt_iff
    (mpl mmpl : Obj.MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MainOkCliExtPqB2NeedLocksPlacedAt
        mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs CodeOk libcAddr brkStart stk
        LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.cliBudgetLimits ↔
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliF3PqB2NeedLocksPlacedAt
        mpl mmpl CodeOk libcAddr brkStart stk :=
  mainOkCliExtPqB2NeedLocksPlacedAt_iff mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    CodeOk libcAddr brkStart stk
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.cliBudgetLimits

theorem mainOkCliF3OverB2NeedLocksPlacedAt_iff
    (mpl mmpl : Obj.MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.MainOkCliExtOverB2NeedLocksPlacedAt
        mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs CodeOk libcAddr brkStart stk
        LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.cliBudgetLimits ↔
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliF3OverB2NeedLocksPlacedAt
        mpl mmpl CodeOk libcAddr brkStart stk :=
  mainOkCliExtOverB2NeedLocksPlacedAt_iff mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    CodeOk libcAddr brkStart stk
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.cliBudgetLimits

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
