/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliImgPlacement
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliImgLift
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliImgBridgeExt
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainOkComposeCut
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainOkProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1
import LibsignalBinary.Proofs.SignalSession.Cli.CliExternsWitness

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace CryptoVerification.SignalSession.Cli.MainHops.CliImgBridge

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.MainHops.CliImgPlacement
open CryptoVerification.SignalSession.Cli.MainHops.MainOkComposeCut
open CryptoVerification.LibsignalPublicApi.StoreKit

theorem main_ok_a1_tight_bridge (W : CliHooks) {img : Obj.Image} {Run : Inputs → RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hrun : subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr runName)
      ((runSpecTight E2E.HooksE.A0 img uuidTryParse Run
        (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32) cliResStack).inImage img))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (cliProg img (cliExterns W)) (entryOf img mainName)
      (mainSpecTight E2E.HooksE.A0 img cliMainStk (cliStatics img) Run) :=
  main_ok_ext_tight_of_alloc_ext_proof
    (cliExterns_ok W)
    (allocContractsX_of_externsOk img (cliExterns_ok W))
    (allocContractsFs_of_externsOk img (cliExterns_ok W))
    himg hrun hdom

theorem main_ok_a1_bridge (W : CliHooks) {img : Obj.Image} {Run : Inputs → RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hrun : subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr runName)
      ((runSpec E2E.HooksE.A0 img uuidTryParse Run
        (fun p => cliIo.pathOk p ∧ p.length < 2 ^ 32) cliResStack).inImage img))
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    subroutine_ok (cliProg img (cliExterns W)) (entryOf img mainName)
      (mainSpec E2E.HooksE.A0 img cliMainStk (cliStatics img) Run) :=
  subroutine_ok_mainSpec_of_tight (main_ok_a1_tight_bridge W himg hrun hdom)

theorem main_ok_ext_tight_of_alloc_bridge {P : E2E.PEParams} {A : RustAlloc}
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
  main_ok_ext_tight_of_alloc_ext_proof hOk hAX hAF himg hrun hdom

theorem main_ok_ext_of_alloc_bridge {P : E2E.PEParams} {A : RustAlloc}
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
  main_ok_ext_of_alloc_ext_proof hOk hAX hAF himg hrun hdom

end CryptoVerification.SignalSession.Cli.MainHops.CliImgBridge
