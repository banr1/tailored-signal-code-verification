/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit
import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactC
import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactG
import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactGr
import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactL

/-!
# Guarded-Tight `W1` (`encrypt` `@109`) Exact Slot Assembly

**Checked by Lean.**

Assembles `ckx2_w1EncExact_phaseCredit`, `ckx2_w1EncExact_groupSpec`, and
`ckx2_w1EncExact_singleSlotFineSpec` for `ckx2_cliEncryptBinaryKitSlotEnvExact` from
`w1x_guard`, `w1xl_lift`, `w1x_creditCore`, and `w1x_gr_groupCore`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm

open Arm64.Process (bytesOfString)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall parseArgs)
open LibsignalBinary.Heap (AllocCostModel RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactGr (w1x_gr_groupCore)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactL (w1xl_lift)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit
  (ckx2_w1EncExact_groupSpec_of_w1x ckx2_w1EncExact_phaseCredit_of_w1x w1x_creditCore_Stmt)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_cliEncryptBinaryKitSlotEnvExact ckx2_w1EncExact_groupSpec_Stmt
   ckx2_w1EncExact_phaseCredit_Stmt ckx2_w1EncExact_singleSlotFineSpec_of_stmts)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (W1BinarySendDom W1BinarySendParams)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)

private theorem w1x_asm_creditCore [LibsignalPlacement] (W : CliHooks) :
    w1x_creditCore_Stmt W :=
  CliKitW1EncExactC.w1x_creditCore W

/-- `PhaseCreditSpec` for `ckx2_cliEncryptBinaryKitSlotEnvExact`. -/
theorem ckx2_w1EncExact_phaseCredit [LibsignalPlacement] (W : CliHooks) :
    ckx2_w1EncExact_phaseCredit_Stmt W :=
  ckx2_w1EncExact_phaseCredit_of_w1x W
    (CliKitW1EncExactG.w1x_guard W)
    w1xl_lift
    (w1x_asm_creditCore W)

/-- `PhaseGroupSpec` for `ckx2_cliEncryptBinaryKitSlotEnvExact`. -/
theorem ckx2_w1EncExact_groupSpec [LibsignalPlacement] (W : CliHooks) :
    ckx2_w1EncExact_groupSpec_Stmt W :=
  ckx2_w1EncExact_groupSpec_of_w1x W
    (CliKitW1EncExactG.w1x_guard W)
    w1xl_lift
    (w1x_gr_groupCore W)

/-- Bundled `SingleSlotFineSpec` for `ckx2_cliEncryptBinaryKitSlotEnvExact`. -/
def ckx2_w1EncExact_singleSlotFineSpec [LibsignalPlacement] (W : CliHooks)
    (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (w1R : W1BinarySendParams)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV))
    (hc : g.c = .send peerV)
    (hrep : w1R.repAlloc = A.repAlloc)
    (hdom : W1BinarySendDom (.send peerV) g.i w1R) :
    SingleSlotFineSpec (ckx2_cliEncryptBinaryKitSlotEnvExact W A w1R.B w1R.x) :=
  ckx2_w1EncExact_singleSlotFineSpec_of_stmts W
    (ckx2_w1EncExact_phaseCredit W)
    (ckx2_w1EncExact_groupSpec W)
    g peerV M A w1R hi hp hc hrep hdom

end LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
