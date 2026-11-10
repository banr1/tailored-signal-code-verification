/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliImgPlacement
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainCalleesExtHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainOkComposeCut
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

/-! # `CliImgBridgeExt`: Placed-to-`cliProg` Bridge for Parametric `CliExternsOk P A ext` -/
namespace CryptoVerification.SignalSession.Cli.MainHops.CliImgBridge

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.MainHops.CliImgPlacement
open CryptoVerification.SignalSession.Cli.MainHops.MainOkComposeCut

set_option linter.unusedVariables false in
theorem main_ok_ext_tight_of_alloc_ext_proof {P : E2E.PEParams} {A : RustAlloc}
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
      (mainSpecTight A img cliMainStk (cliStatics img) Run) := by
  letI : LibsignalFullPlacement := instLibsignalFullPlacementOfLoads img himg
  have hcio := mainCalleesAndIo_of_fullLookup
    (base_align4_of_loads himg) (extFullLookup_H_ext img ext) hOk
  exact main_ok_tight_bridge_of_placed
    (H := H_ext img ext) (Y := Y_ext img ext) (ext := cliExternsWith ext)
    himg
    (fun _ => rfl)
    (Y_ext_isSome_eq img ext)
    Y_ext_agree_of_callInv
    hcio.1
    hcio.2
    ⟨cliIo_stdin, cliIo_coinsPath, cliIo_coins, cliIo_commit⟩
    hrun
    (hparse_of_domains hdom)
    cli_hstk
    cli_hstk64

set_option linter.unusedVariables false in
theorem main_ok_ext_of_alloc_ext_proof {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {img : Obj.Image} {Run : Inputs → RunAnswer → Prop}
    (hOk : CliExternsOk P A ext)
    (hAX : AllocContractsX img A (cliExternsWith ext))
    (hAF : AllocContractsFs img A (cliExternsWith ext))
    (himg : Obj.Loads libsignalSessionImage img)
    (hrun : subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr runName)
      ((runSpec A img uuidTryParse Run
        (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32) cliResStack).inImage img))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (cliProg img (cliExternsWith ext)) (entryOf img mainName)
      (mainSpec A img cliMainStk (cliStatics img) Run) :=
  subroutine_ok_mainSpec_of_tight
    (main_ok_ext_tight_of_alloc_ext_proof hOk hAX hAF himg hrun hdom)

end CryptoVerification.SignalSession.Cli.MainHops.CliImgBridge
