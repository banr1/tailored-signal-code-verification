/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.MainOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.LitsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainOkProofPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `main` Instantiation at `A0` (`[LibsignalPlacement]`, Block `617`)

Instantiates `MainCalleesBlk617`, `MainIoPlaced`, `mainSpecTightPlaced`, and `mainSpecPlaced` on
Block `617` at `E2E.HooksE.A0` and `cliGhostExterns g (cliExternsPlaced mmpl W)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns cliGhostExterns_alloc cliGhostExterns_dealloc
   cliGhostExterns_other cliGhostExterns_realloc cliGhostExterns_shim)

private theorem cliGhostExterns_other_decide (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {sym : String}
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ CryptoVerification.SignalSession.lsReadFileSym := by decide)
    (h8 : sym ≠ CryptoVerification.SignalSession.lsReadStdinSym := by decide)
    (h9 : sym ≠ lsMemsetSym := by decide)
    (h10 : sym ≠ lsMemcpySym := by decide) :
    cliGhostExterns g baseExt sym = baseExt sym :=
  cliGhostExterns_other g baseExt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

/-- Legacy `A0` bump-allocator ghost-hook assignment on `CliGhostHooks`. -/
def CliGhostHooksA0 (g : CliGhostHooks) : Prop :=
  g.shim = hookNoop ∧
  g.alloc = E2E.allocHook0 ∧
  g.dealloc = E2E.deallocHook ∧
  g.realloc = E2E.reallocHook0

/-- Discharges `AllocContractsFsPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W))`
from `Slots.CliGhostA0Hooks E2E.HooksE.A0 g`. -/
theorem allocContractsFs_cliGhost_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 g) :
    AllocContractsFsPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  Slots.allocContractsFsPlaced_cli mmpl g W hG

/-- Discharges `AllocContractsXCliPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W))`
from `Slots.CliGhostA0Hooks E2E.HooksE.A0 g`. -/
theorem allocContractsX_cliGhost_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 g) :
    AllocContractsXCliPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  (allocContractsFs_cliGhost_placed mmpl g W hG).toAllocContractsX

/-- `MainIoPlaced` on `cliGhostExterns g (cliExternsPlaced mmpl W)` from `readStdin` and `readFile`
`subroutine_ok` hypotheses, discharging `writeFile` and `writeStdout` unconditionally from rows `5`
and `6` of the 39-row `cliHookTablePlaced mmpl W`. -/
theorem mainIo_of_cliGhostExterns_placed [LibsignalPlacement] {A : RustAlloc}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (stk : Nat)
    (hReadStdin : subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadStdinSym) (withLsRoCl lsmpl (readStdinSpecPlaced cliIo A stk)))
    (hReadFile : subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A stk))) :
    MainIoPlaced A (cliGhostExterns g (cliExternsPlaced mmpl W)) cliIo stk where
  readStdin := hReadStdin
  readFile := hReadFile
  writeFile := writeFile_rocl_ok_of_lookup stk
    ((cliGhostExterns_other_decide g (cliExternsPlaced mmpl W)).trans
      (cliExternsPlaced_writeFile mmpl W))
  writeStdout := writeStdout_rocl_ok_of_lookup stk
    ((cliGhostExterns_other_decide g (cliExternsPlaced mmpl W)).trans
      (cliExternsPlaced_writeStdout mmpl W))

/-- `MainIoPlaced` on `cliGhostExterns g (cliExternsPlaced mmpl W)` from `HookSat` read hypotheses. -/
theorem mainIo_of_hookSat_placed [LibsignalPlacement] {A : RustAlloc}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (stk : Nat)
    (hReadStdin : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadStdinSym
      (readStdinSpecPlaced cliIo A stk))
    (hReadFile : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileLitSpecPlaced cliIo A stk)) :
    MainIoPlaced A (cliGhostExterns g (cliExternsPlaced mmpl W)) cliIo stk :=
  mainIo_of_lookup_placed stk hReadStdin hReadFile
    ((cliGhostExterns_other_decide g (cliExternsPlaced mmpl W)).trans
      (cliExternsPlaced_writeFile mmpl W))
    ((cliGhostExterns_other_decide g (cliExternsPlaced mmpl W)).trans
      (cliExternsPlaced_writeStdout mmpl W))

/-- `MainCalleesBlk617` at `A0 / cliGhostExterns g (cliExternsPlaced mmpl W) / cliResStack` from
`hAllocFs : AllocContractsFsPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W))`,
with `address` as a hypothesis. -/
theorem mainA1_callees_of_addr_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) (hookStack : Nat)
    (hAllocFs : AllocContractsFsPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (haddr : subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec E2E.HooksE.A0 uuidTryParse cliResStack))) :
    MainCalleesBlk617 E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W))
      uuidTryParse hookStack cliResStack :=
  have hpanBase :
      cliExternsPlaced mmpl W "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" =
        some Rust.panicked := by
    simp only [cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
      List.contains_cons, beq_self_eq_true, Bool.true_or, Bool.or_true, ↓reduceIte]
  have hpan :
      cliGhostExterns g (cliExternsPlaced mmpl W)
        "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked :=
    (cliGhostExterns_other_decide g (cliExternsPlaced mmpl W)).trans hpanBase
  { alloc := hAllocFs.toAllocContractsX
    allocFs := hAllocFs
    strlen := strlen_ok_placed
      ((cliGhostExterns_other_decide g (cliExternsPlaced mmpl W)).trans
        (cliExternsPlaced_strlen mmpl W))
    fromUtf8 := fromUtf8Ascii_ok_placed (err := W.utf8Err)
      ((cliGhostExterns_other_decide g (cliExternsPlaced mmpl W)).trans
        (cliExternsPlaced_fromUtf8 mmpl W))
    address := haddr
    reserve16 := reserve16_placed_ok hAllocFs cli_resStack_callees.2.1 hpan
    reserve1 := reserve1_placed_ok hAllocFs cli_resStack_callees.2.1 hpan
    tryAllocateIn3 := tryAllocateIn3_placed_okFs hAllocFs
      cli_resStack_callees.1 cli_resStack_callees.2.2.2
    handleErrorPanic :=
      (ls_externAt?_of_mem
        (prog := lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 617)
        (by decide)).trans hpan }

/-- All `MainCalleesBlk617` fields at `A0 / cliGhostExterns g (cliExternsPlaced mmpl W) / cliResStack`;
`address` discharged via `address_placed_ok_a1_of_hooks`. -/
theorem mainA1_callees_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) (hookStack : Nat)
    (hAllocFs : AllocContractsFsPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    MainCalleesBlk617 E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W))
      uuidTryParse hookStack cliResStack :=
  have hpan580 :
      cliGhostExterns g (cliExternsPlaced mmpl W) Address.Helpers.lsHandleErrorSym580 =
        some Rust.panicked :=
    (cliGhostExterns_other_decide g (cliExternsPlaced mmpl W)).trans (by
      simp only [cliExternsPlaced, Address.Helpers.lsHandleErrorSym580, isCliPanicSymbolPlaced,
        cliPanicSymbolsPlaced, List.contains_cons, beq_self_eq_true, Bool.true_or, Bool.or_true,
        ↓reduceIte])
  mainA1_callees_of_addr_placed mmpl g W hookStack hAllocFs
    (address_placed_ok_a1_of_hooks hAllocFs hpan580
      ((cliGhostExterns_other_decide g (cliExternsPlaced mmpl W)).trans
        (cliExternsPlaced_memrchr mmpl W))
      cli_resStack_callees.2.2.1 cli_resStack_callees.2.2.2)

/-- Tightened `main`'s contract (`mainSpecTightPlaced`) at
`A0 / cliGhostExterns g (cliExternsPlaced mmpl W) / cliMainStk` for any `CodeOk` (`[LsCodeInv CodeOk]`). -/
theorem main_ok_a1_tight_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {Run : Inputs → RunAnswer → Prop}
    (hAllocFs : AllocContractsFsPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hReadStdin : subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadStdinSym) (withLsRoCl lsmpl (readStdinSpecPlaced cliIo E2E.HooksE.A0 cliHookStack)))
    (hReadFile : subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo E2E.HooksE.A0 cliHookStack)))
    (hrun : subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 579)
      (runSpecTightPlaced CodeOk E2E.HooksE.A0 uuidTryParse Run
        (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32) cliResStack))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecTightPlaced CodeOk E2E.HooksE.A0 cliMainStk cliStaticsPlaced Run) :=
  main_ok_tight_placed_proof (mainA1_callees_placed mmpl g W cliHookStack hAllocFs)
    (mainIo_of_cliGhostExterns_placed mmpl g W cliHookStack hReadStdin hReadFile)
    ⟨cliIo_stdin, cliIo_coinsPath, cliIo_coins, cliIo_commit⟩
    hrun (hparse_of_domains hdom) cli_hstk cli_hstk64

theorem main_ok_a1_tight_placed_of_hookSat [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {Run : Inputs → RunAnswer → Prop}
    (hAllocFs : AllocContractsFsPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hReadStdin : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadStdinSym
      (readStdinSpecPlaced cliIo E2E.HooksE.A0 cliHookStack))
    (hReadFile : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileLitSpecPlaced cliIo E2E.HooksE.A0 cliHookStack))
    (hrun : subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 579)
      (runSpecTightPlaced CodeOk E2E.HooksE.A0 uuidTryParse Run
        (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32) cliResStack))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecTightPlaced CodeOk E2E.HooksE.A0 cliMainStk cliStaticsPlaced Run) :=
  main_ok_a1_tight_placed mmpl g W hAllocFs
    (readStdin_rocl_ok_of_hookSat hReadStdin)
    (readFile_rocl_ok_of_hookSat hReadFile)
    hrun hdom

/-- `main`'s contract (`mainSpecPlaced`) at
`A0 / cliGhostExterns g (cliExternsPlaced mmpl W) / cliMainStk` for any `CodeOk` (`[LsCodeInv CodeOk]`). -/
theorem main_ok_a1_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {Run : Inputs → RunAnswer → Prop}
    (hAllocFs : AllocContractsFsPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hReadStdin : subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadStdinSym) (withLsRoCl lsmpl (readStdinSpecPlaced cliIo E2E.HooksE.A0 cliHookStack)))
    (hReadFile : subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo E2E.HooksE.A0 cliHookStack)))
    (hrun : subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 579)
      (runSpecPlaced CodeOk E2E.HooksE.A0 uuidTryParse Run
        (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32) cliResStack))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecPlaced CodeOk E2E.HooksE.A0 cliMainStk cliStaticsPlaced Run) :=
  main_ok_placed_proof (mainA1_callees_placed mmpl g W cliHookStack hAllocFs)
    (mainIo_of_cliGhostExterns_placed mmpl g W cliHookStack hReadStdin hReadFile)
    ⟨cliIo_stdin, cliIo_coinsPath, cliIo_coins, cliIo_commit⟩
    hrun (hparse_of_domains hdom) cli_hstk cli_hstk64

theorem main_ok_a1_placed_of_hookSat [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {Run : Inputs → RunAnswer → Prop}
    (hAllocFs : AllocContractsFsPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hReadStdin : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadStdinSym
      (readStdinSpecPlaced cliIo E2E.HooksE.A0 cliHookStack))
    (hReadFile : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileLitSpecPlaced cliIo E2E.HooksE.A0 cliHookStack))
    (hrun : subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 579)
      (runSpecPlaced CodeOk E2E.HooksE.A0 uuidTryParse Run
        (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32) cliResStack))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecPlaced CodeOk E2E.HooksE.A0 cliMainStk cliStaticsPlaced Run) :=
  main_ok_a1_placed mmpl g W hAllocFs
    (readStdin_rocl_ok_of_hookSat hReadStdin)
    (readFile_rocl_ok_of_hookSat hReadFile)
    hrun hdom

theorem mProgPlaced_eq_cliProgPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks) :
    mProgPlaced (cliExternsPlaced mmpl W) = cliProgPlaced mmpl W :=
  (instIsLsBlockProg_617 (cliExternsPlaced mmpl W)).eq_blockProgram

end CryptoVerification.SignalSession.Cli.MainHops
