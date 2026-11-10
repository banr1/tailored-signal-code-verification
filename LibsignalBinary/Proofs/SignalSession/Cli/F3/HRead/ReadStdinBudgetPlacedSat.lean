/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlacedSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecsHook

/-!
# `HookSat`-Backed `MainIoOfPlacedSat` & `MainIoPlacedSat ∧ MainIoBoundedPlacedSat` (`ReadStdinBudgetPlacedSat`)

- **Role**: `Role::Proof` (outside the TCB). Untrusted groundwork for #1255 (HOOKS-PREP).
- **Overview**:
  `HookSat` sibling of `ReadStdinBudgetPlaced` §6 (`:2038–2156`): constructs `MainIoOfPlacedSat`
  and `MainIoPlacedSat ∧ MainIoBoundedPlacedSat` on `withReadHooks rfh rsh H0` from
  `HookSat H0 lsWriteFileSym (writeFileSpecPlacedSat …)` and
  `HookSat H0 lsWriteStdoutSym (writeStdoutSpecPlacedSat …)` instead of
  `H0 lsWrite*Sym = some write*Hook`, together with exact-hook recovery corollaries via
  `IoHonestSpecsHook`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlacedSat

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement libsignalSessionExterns ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_rocl_of_plain withLsRoCl)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsReadFileSym lsReadStdinSym lsWriteFileSym lsWriteStdoutSym
   writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (ReadStdinEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
  (CompiledReadStdinEnv HookOk.readStdin_mono_env cliGhostExterns_writeFile
   cliGhostExterns_writeStdout compiledReadStdinEnv_sub_bounded
   compiledReadStdinEnv_sub_readStdinEnv hookSat_withReadHooks_readFile
   hookSat_withReadHooks_readStdin readFileAnyBudgetCondSpec readFileAnySpecPlaced
   readFileFullLinkedGhostHook readFileFullLinkedGhostHook_ok_lit readStdinBudgetCondSpec
   readStdinGhostHook readStdinGhostHook_ok_compiled readStdinLinkedGhostHook
   readStdinLinkedGhostHook_ok_compiled withReadHooks withReadHooks_other)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (ReadStdinBoundedEnv readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlacedSat
  (MainIoBoundedPlacedSat MainIoOfPlacedSat mainIoBoundedPlaced_iff_mainIoPlaced_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileSpecPlacedSat writeFileStackFloor writeStdoutSpecPlacedSat writeStdoutStackFloor)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecsHook
  (hookSat_writeFileSpecPlacedSat_of_hook hookSat_writeStdoutSpecPlacedSat_of_hook)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv readFileLitSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudgetSat (MainIoPlacedSat)

private theorem ls_hook_placed_rocl_ok [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ sym) (withLsRoCl lsmpl spec) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hsat hmem

private theorem hookSat_withReadHooks_other {α : Type} (rfh rsh : State → State)
    (H0 : LibsignalHooks) {sym : String} {spec : Spec α}
    (hsat : HookSat H0 sym spec)
    (h1 : sym ≠ lsReadStdinSym := by decide)
    (h2 : sym ≠ lsReadFileSym := by decide) :
    HookSat (withReadHooks rfh rsh H0) sym spec := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f, (withReadHooks_other rfh rsh H0 h1 h2).trans hf, hok⟩

/-- Generic `MainIoOfPlacedSat` constructor on `withReadHooks rfh rsh H0` over any `H0` satisfying
    `HookSat H0 lsWriteFileSym (writeFileSpecPlacedSat …)` and
    `HookSat H0 lsWriteStdoutSym (writeStdoutSpecPlacedSat …)`. -/
theorem mainIoOfPlaced_withReadHooks_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H0 : LibsignalHooks} {rfh rsh : State → State} {stk : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hWriteFile : HookSat H0 lsWriteFileSym (writeFileSpecPlacedSat cliIo A lim stk))
    (hWriteStdout : HookSat H0 lsWriteStdoutSym (writeStdoutSpecPlacedSat A lim stk))
    (hReadFile : HookOk rfh (readFileLitSpecPlaced cliIo A lim stk ReadEnv))
    (hReadStdin : HookOk rsh (readStdinSpecOfPlaced cliIo A lim stk StdinEnv))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    MainIoOfPlacedSat A lim (withReadHooks rfh rsh H0) cliIo stk StdinEnv ReadEnv where
  readStdin := ls_hook_placed_rocl_ok (hookSat_withReadHooks_readStdin rfh rsh H0 hReadStdin)
  readFile := ls_hook_placed_rocl_ok (hookSat_withReadHooks_readFile rfh rsh H0 hReadFile)
  writeFile := ls_hook_placed_rocl_ok (hookSat_withReadHooks_other rfh rsh H0 hWriteFile)
  writeStdout := ls_hook_placed_rocl_ok (hookSat_withReadHooks_other rfh rsh H0 hWriteStdout)
  hWriteFileStack := hwfStk
  hWriteStdoutStack := hwsStk

/-- Exact-hook recovery corollary of `mainIoOfPlaced_withReadHooks_sat` via `IoHonestSpecsHook`. -/
theorem mainIoOfPlaced_withReadHooks_of_hooks_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H0 : LibsignalHooks} {rfh rsh : State → State} {stk : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hWriteFile : H0 lsWriteFileSym = some writeFileHook)
    (hWriteStdout : H0 lsWriteStdoutSym = some writeStdoutHook)
    (hReadFile : HookOk rfh (readFileLitSpecPlaced cliIo A lim stk ReadEnv))
    (hReadStdin : HookOk rsh (readStdinSpecOfPlaced cliIo A lim stk StdinEnv))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    MainIoOfPlacedSat A lim (withReadHooks rfh rsh H0) cliIo stk StdinEnv ReadEnv :=
  mainIoOfPlaced_withReadHooks_sat
    (hookSat_writeFileSpecPlacedSat_of_hook hWriteFile)
    (hookSat_writeStdoutSpecPlacedSat_of_hook hWriteStdout)
    hReadFile hReadStdin hwfStk hwsStk

/-- `HookSat`-parametric simultaneous `MainIoPlacedSat ∧ MainIoBoundedPlacedSat` on
    `withReadHooks rfh rsh H0` over any `H0` satisfying `HookSat` on `lsWriteFileSym` and
    `lsWriteStdoutSym`. -/
theorem mainIoPlaced_and_bounded_withReadHooks_of_hookSat_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H0 : LibsignalHooks} {rfh rsh : State → State} (stk : Nat)
    (hWriteFile : HookSat H0 lsWriteFileSym (writeFileSpecPlacedSat cliIo A lim stk))
    (hWriteStdout : HookSat H0 lsWriteStdoutSym (writeStdoutSpecPlacedSat A lim stk))
    (hReadFile : HookOk rfh (readFileLitSpecPlaced cliIo A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hReadStdin : HookOk rsh (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    MainIoPlacedSat A lim (withReadHooks rfh rsh H0) cliIo stk ∧
    MainIoBoundedPlacedSat A lim (withReadHooks rfh rsh H0) cliIo stk ReadStdinBoundedEnv := by
  have hUnbounded : MainIoBoundedPlacedSat A lim (withReadHooks rfh rsh H0) cliIo stk ReadStdinEnv :=
    mainIoOfPlaced_withReadHooks_sat hWriteFile hWriteStdout hReadFile
      (HookOk.readStdin_mono_env (fun _ _ => compiledReadStdinEnv_sub_readStdinEnv) hReadStdin)
      hwfStk hwsStk
  have hBounded :
      MainIoBoundedPlacedSat A lim (withReadHooks rfh rsh H0) cliIo stk ReadStdinBoundedEnv :=
    mainIoOfPlaced_withReadHooks_sat hWriteFile hWriteStdout hReadFile
      (HookOk.readStdin_mono_env (fun _ _ => compiledReadStdinEnv_sub_bounded) hReadStdin)
      hwfStk hwsStk
  exact ⟨(mainIoBoundedPlaced_iff_mainIoPlaced_sat A lim (withReadHooks rfh rsh H0) cliIo stk).mp
    hUnbounded, hBounded⟩

/-- Exact-table recovery corollary of `mainIoPlaced_and_bounded_withReadHooks_of_hookSat_sat` at
    `H0 := cliGhostExterns g (cliExternsPlaced mmpl W)` via `IoHonestSpecsHook`. -/
theorem mainIoPlaced_and_bounded_withReadHooks_ghost_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {rfh rsh : State → State} (stk : Nat)
    (hReadFile : HookOk rfh (readFileLitSpecPlaced cliIo A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hReadStdin : HookOk rsh (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    MainIoPlacedSat A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk ∧
    MainIoBoundedPlacedSat A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk
      ReadStdinBoundedEnv :=
  mainIoPlaced_and_bounded_withReadHooks_of_hookSat_sat stk
    (hookSat_writeFileSpecPlacedSat_of_hook (cliGhostExterns_writeFile mmpl W g))
    (hookSat_writeStdoutSpecPlacedSat_of_hook (cliGhostExterns_writeStdout mmpl W g))
    hReadFile hReadStdin hwfStk hwsStk

/-- Specialization of `mainIoPlaced_and_bounded_withReadHooks_of_hookSat_sat` to
    `readStdinGhostHook` (call-entry `P_io` form, parametric in `H0` via `HookSat`). -/
theorem mainIoPlaced_and_bounded_of_readStdinGhostHook_of_hookSat_sat [LibsignalPlacement]
    {M : AllocCostModel} {P_io : Program} {entry_stdin : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H0 : LibsignalHooks} {stk : Nat}
    {rfh fbStdin : State → State}
    (hWriteFile : HookSat H0 lsWriteFileSym (writeFileSpecPlacedSat cliIo A lim stk))
    (hWriteStdout : HookSat H0 lsWriteStdoutSym (writeStdoutSpecPlacedSat A lim stk))
    (hReadFile : HookOk rfh (readFileLitSpecPlaced cliIo A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hStdinCond : subroutine_ok P_io entry_stdin (readStdinBudgetCondSpec A lim stk))
    (hFbStdin : HookOk fbStdin (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    let rsh := readStdinGhostHook P_io entry_stdin A lim stk fbStdin
    MainIoPlacedSat A lim (withReadHooks rfh rsh H0) cliIo stk ∧
    MainIoBoundedPlacedSat A lim (withReadHooks rfh rsh H0) cliIo stk ReadStdinBoundedEnv :=
  mainIoPlaced_and_bounded_withReadHooks_of_hookSat_sat stk hWriteFile hWriteStdout hReadFile
    (readStdinGhostHook_ok_compiled hStdinCond hFbStdin) hwfStk hwsStk

/-- Exact-table recovery corollary of `mainIoPlaced_and_bounded_of_readStdinGhostHook_of_hookSat_sat`
    at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem mainIoPlaced_and_bounded_of_readStdinGhostHook_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (g : CliGhostHooks)
    {M : AllocCostModel} {P_io : Program} {entry_stdin : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {rfh fbStdin : State → State}
    (hReadFile : HookOk rfh (readFileLitSpecPlaced cliIo A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hStdinCond : subroutine_ok P_io entry_stdin (readStdinBudgetCondSpec A lim stk))
    (hFbStdin : HookOk fbStdin (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    let rsh := readStdinGhostHook P_io entry_stdin A lim stk fbStdin
    MainIoPlacedSat A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk ∧
    MainIoBoundedPlacedSat A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk
      ReadStdinBoundedEnv :=
  mainIoPlaced_and_bounded_withReadHooks_ghost_sat mmpl W g stk hReadFile
    (readStdinGhostHook_ok_compiled hStdinCond hFbStdin) hwfStk hwsStk

/-- Specialization of `mainIoPlaced_and_bounded_withReadHooks_of_hookSat_sat` to
    `readStdinLinkedGhostHook` + `readFileFullLinkedGhostHook` (`HookSat`-parametric in `H0`). -/
theorem mainIoPlaced_and_bounded_of_linkedReadGhostHooks_of_hookSat_sat [LibsignalPlacement]
    {M : AllocCostModel} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry_file entry_stdin : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H0 : LibsignalHooks} {stk : Nat}
    {fbFile fbStdin : State → State}
    (hWriteFile : HookSat H0 lsWriteFileSym (writeFileSpecPlacedSat cliIo A lim stk))
    (hWriteStdout : HookSat H0 lsWriteStdoutSym (writeStdoutSpecPlacedSat A lim stk))
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hFileCond : subroutine_ok P_sub entry_file (readFileAnyBudgetCondSpec A lim stk))
    (hFbFile : HookOk fbFile (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hFbFileFs : ∀ y R s0,
      SubroutineOutcome (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd))
        y R s0 (fbFile s0) →
        (fbFile s0).fs = s0.fs ∧ (fbFile s0).trace = s0.trace)
    (hStdinCond : subroutine_ok P_sub entry_stdin (readStdinBudgetCondSpec A lim stk))
    (hFbStdin : HookOk fbStdin (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    let rfh := readFileFullLinkedGhostHook keep P_real P_sub entry_file A lim stk fbFile
    let rsh := readStdinLinkedGhostHook keep P_real P_sub entry_stdin A lim stk fbStdin
    MainIoPlacedSat A lim (withReadHooks rfh rsh H0) cliIo stk ∧
    MainIoBoundedPlacedSat A lim (withReadHooks rfh rsh H0) cliIo stk ReadStdinBoundedEnv :=
  mainIoPlaced_and_bounded_withReadHooks_of_hookSat_sat stk hWriteFile hWriteStdout
    (readFileFullLinkedGhostHook_ok_lit hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hFileCond
      hFbFile hFbFileFs)
    (readStdinLinkedGhostHook_ok_compiled hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hStdinCond
      hFbStdin)
    hwfStk hwsStk

/-- Exact-table recovery corollary of
    `mainIoPlaced_and_bounded_of_linkedReadGhostHooks_of_hookSat_sat` at
    `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem mainIoPlaced_and_bounded_of_linkedReadGhostHooks_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (g : CliGhostHooks)
    {M : AllocCostModel} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry_file entry_stdin : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fbFile fbStdin : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hPoolStrip : ∀ st s, A.pool lim st (stripS keep s) = A.pool lim st s)
    (hFileCond : subroutine_ok P_sub entry_file (readFileAnyBudgetCondSpec A lim stk))
    (hFbFile : HookOk fbFile (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hFbFileFs : ∀ y R s0,
      SubroutineOutcome (readFileAnySpecPlaced A lim stk (ReadFileRuleEnv cliIo.rd))
        y R s0 (fbFile s0) →
        (fbFile s0).fs = s0.fs ∧ (fbFile s0).trace = s0.trace)
    (hStdinCond : subroutine_ok P_sub entry_stdin (readStdinBudgetCondSpec A lim stk))
    (hFbStdin : HookOk fbStdin (readStdinSpecOfPlaced cliIo A lim stk CompiledReadStdinEnv))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    let rfh := readFileFullLinkedGhostHook keep P_real P_sub entry_file A lim stk fbFile
    let rsh := readStdinLinkedGhostHook keep P_real P_sub entry_stdin A lim stk fbStdin
    MainIoPlacedSat A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk ∧
    MainIoBoundedPlacedSat A lim
      (withReadHooks rfh rsh (cliGhostExterns g (cliExternsPlaced mmpl W))) cliIo stk
      ReadStdinBoundedEnv :=
  mainIoPlaced_and_bounded_withReadHooks_ghost_sat mmpl W g stk
    (readFileFullLinkedGhostHook_ok_lit hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hFileCond
      hFbFile hFbFileFs)
    (readStdinLinkedGhostHook_ok_compiled hsvc_real hsvc_sub hreal_no hsub_no hPoolStrip hStdinCond
      hFbStdin)
    hwfStk hwsStk

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlacedSat
