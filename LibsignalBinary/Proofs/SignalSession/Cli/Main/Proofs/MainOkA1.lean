/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliImgBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3

/-!
# `main` Instantiation at Concrete `A0` Hooks and `CliExternsOk`

Instantiates `main_ok_of_hops` at `E2E.HooksE.A0` and `cliExterns W` (`main_ok_a1`,
`main_ok_a1_tight`) from proved callee and hop contracts, and generalizes to arbitrary `(P, A, ext)`
satisfying `CliExternsOk P A ext` (`main_ok_ext`, `main_ok_ext_tight`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- `MainCallees` at `A0 / cliExterns W / cliResStack` from the proved callee lemmas, with
`address` as a hypothesis. -/
theorem mainA1_callees_of_addr (W : CliHooks) (img : Obj.Image) (hookStack : Nat)
    (haddr : subroutine_ok (mProg img (cliExterns W))
      ((mProg img (cliExterns W)).fnAddr addressName)
      ((addressSpec E2E.HooksE.A0 uuidTryParse cliResStack).inImage img)) :
    MainCallees img E2E.HooksE.A0 (cliExterns W) uuidTryParse hookStack cliResStack :=
  { alloc := allocContractsX_cli W img
    allocFs := allocContractsFs_cli W img
    strlen := strlen_ok_cliExterns W
    fromUtf8 := fromUtf8Ascii_ok_cliExterns W
    address := haddr
    reserve16 := reserve16Cap_ok (allocContractsFs_cli W img) cli_resStack_callees.2.1
    reserve1 := reserve1_ok (allocContractsFs_cli W img) cli_resStack_callees.2.1
    tryAllocateIn3 := tryAllocateIn3_okFs (allocContractsFs_cli W img) cli_resStack_callees.1
      cli_resStack_callees.2.2.2 }

/-- All eight `MainCallees` fields at `A0 / cliExterns W / cliResStack`; `address` from
`address_ok_a1`. -/
theorem mainA1_callees (W : CliHooks) (img : Obj.Image) (hookStack : Nat) :
    MainCallees img E2E.HooksE.A0 (cliExterns W) uuidTryParse hookStack cliResStack :=
  mainA1_callees_of_addr W img hookStack
    (address_ok_a1 (allocContractsFs_cli W img) (cliExterns_memrchr W) cli_resStack_callees.2.2.1
      cli_resStack_callees.2.2.2)

/-- `main`'s contract at `A0 / cliExterns W / cliMainStk`, composed by `main_ok_of_hops` from the
proved M1–M5 hop contracts. -/
theorem main_ok_a1 (W : CliHooks) {img : Obj.Image} {Run : Inputs → RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hrun : subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr runName)
      ((runSpec E2E.HooksE.A0 img uuidTryParse Run (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32)
        cliResStack).inImage img))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (cliProg img (cliExterns W)) (entryOf img mainName)
      (mainSpec E2E.HooksE.A0 img cliMainStk (cliStatics img) Run) :=
  CliImgBridge.main_ok_a1_bridge W himg hrun hdom

/-- Tightened `main`'s contract (`mainSpecTight`) at `A0 / cliExterns W / cliMainStk`
from `hrun : subroutine_ok ... (runSpecTight ...).inImage img`. -/
theorem main_ok_a1_tight (W : CliHooks) {img : Obj.Image} {Run : Inputs → RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hrun : subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr runName)
      ((runSpecTight E2E.HooksE.A0 img uuidTryParse Run
        (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32) cliResStack).inImage img))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (cliProg img (cliExterns W)) (entryOf img mainName)
      (mainSpecTight E2E.HooksE.A0 img cliMainStk (cliStatics img) Run) :=
  CliImgBridge.main_ok_a1_tight_bridge W himg hrun hdom

/-! ## Extern-Contract (`CliExternsOk`) Generalizations -/

/-- Generalizes `mainA1_callees` to arbitrary `(P, A, ext)` given `AllocContractsX` and
`AllocContractsFs` on `cliExternsWith ext` and `CliExternsOk P A ext`, for any stack budget
`extHookStack ≤ hookStack ≤ 2 ^ 64`. -/
theorem mainCallees_of_alloc_and_cliExternsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (hAX : AllocContractsX img A (cliExternsWith ext))
    (hAF : AllocContractsFs img A (cliExternsWith ext))
    (hOk : CliExternsOk P A ext)
    (hookStack : Nat := extHookStack)
    (hle : extHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    MainCallees img A (cliExternsWith ext) uuidTryParse hookStack cliResStack :=
  { alloc := hAX
    allocFs := hAF
    strlen := strlen_ok_ext hOk img hookStack hle hmax
    fromUtf8 := fromUtf8_ok_ext hOk img hookStack hle hmax
    address := address_ok_ext hAF hOk cli_resStack_callees.2.2.1 cli_resStack_callees.2.2.2
    reserve16 := reserve16Cap_ok hAF cli_resStack_callees.2.1
    reserve1 := reserve1_ok hAF cli_resStack_callees.2.1
    tryAllocateIn3 := tryAllocateIn3_okFs hAF cli_resStack_callees.1 cli_resStack_callees.2.2.2 }

/-- All eight `MainCallees` fields on `cliExternsWith ext` directly from `CliExternsOk P A ext`. -/
theorem mainCallees_of_cliExternsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (hookStack : Nat := extHookStack)
    (hle : extHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    MainCallees img A (cliExternsWith ext) uuidTryParse hookStack cliResStack :=
  mainCallees_of_alloc_and_cliExternsOk
    (allocContractsX_of_externsOk img hOk)
    (allocContractsFs_of_externsOk img hOk)
    hOk hookStack hle hmax

/-- Generalizes `main_ok_a1` to arbitrary `(P, A, ext)` satisfying `CliExternsOk P A ext` with
`AllocContractsX` and `AllocContractsFs` factored out as hypotheses. -/
theorem main_ok_ext_of_alloc {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {img : Obj.Image} {Run : Inputs → RunAnswer → Prop}
    (hOk : CliExternsOk P A ext)
    (hAX : AllocContractsX img A (cliExternsWith ext))
    (hAF : AllocContractsFs img A (cliExternsWith ext))
    (himg : Obj.Loads libsignalSessionImage img)
    (hrun : subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr runName)
      ((runSpec A img uuidTryParse Run (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32)
        cliResStack).inImage img))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (cliProg img (cliExternsWith ext)) (entryOf img mainName)
      (mainSpec A img cliMainStk (cliStatics img) Run) :=
  CliImgBridge.main_ok_ext_of_alloc_bridge hOk hAX hAF himg hrun hdom

/-- Generalizes `main_ok_a1_tight` to arbitrary `(P, A, ext)` satisfying `CliExternsOk P A ext`
with `AllocContractsX` and `AllocContractsFs` factored out. -/
theorem main_ok_ext_tight_of_alloc {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {img : Obj.Image} {Run : Inputs → RunAnswer → Prop}
    (hOk : CliExternsOk P A ext)
    (hAX : AllocContractsX img A (cliExternsWith ext))
    (hAF : AllocContractsFs img A (cliExternsWith ext))
    (himg : Obj.Loads libsignalSessionImage img)
    (hrun : subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr runName)
      ((runSpecTight A img uuidTryParse Run
        (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32) cliResStack).inImage img))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (cliProg img (cliExternsWith ext)) (entryOf img mainName)
      (mainSpecTight A img cliMainStk (cliStatics img) Run) :=
  CliImgBridge.main_ok_ext_tight_of_alloc_bridge hOk hAX hAF himg hrun hdom

/-- `main`'s contract (`mainSpec`) at `(A, cliExternsWith ext, cliMainStk)` from
`CliExternsOk P A ext`. -/
theorem main_ok_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {img : Obj.Image} {Run : Inputs → RunAnswer → Prop}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hrun : subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr runName)
      ((runSpec A img uuidTryParse Run (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32)
        cliResStack).inImage img))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (cliProg img (cliExternsWith ext)) (entryOf img mainName)
      (mainSpec A img cliMainStk (cliStatics img) Run) :=
  main_ok_ext_of_alloc hOk (allocContractsX_of_externsOk img hOk)
    (allocContractsFs_of_externsOk img hOk) himg hrun hdom

/-- Tightened `main` contract (`mainSpecTight`) at `(A, cliExternsWith ext, cliMainStk)` from
`CliExternsOk P A ext`. -/
theorem main_ok_ext_tight {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {img : Obj.Image} {Run : Inputs → RunAnswer → Prop}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hrun : subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr runName)
      ((runSpecTight A img uuidTryParse Run
        (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32) cliResStack).inImage img))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (cliProg img (cliExternsWith ext)) (entryOf img mainName)
      (mainSpecTight A img cliMainStk (cliStatics img) Run) :=
  main_ok_ext_tight_of_alloc hOk (allocContractsX_of_externsOk img hOk)
    (allocContractsFs_of_externsOk img hOk) himg hrun hdom

#print axioms mainA1_callees_of_addr
#print axioms mainA1_callees
#print axioms main_ok_a1
#print axioms main_ok_a1_tight

end CryptoVerification.SignalSession.Cli.MainHops
