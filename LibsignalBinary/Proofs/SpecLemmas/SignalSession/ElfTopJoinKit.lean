/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
import LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0PostBob
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget

/-!
# Post-Bob `prev1` Whole-`main` `FitsEnv` and `RunEnv` Inclusion

**Checked by Lean.**

Proves `FitsEnv fineCostModel cliBudgetLimits` and whole-`run` `RunEnv` inclusion at
`cliDecPkCanonSlotEnvExact' X W` under `CliPqxdhInputs ⟨W.C, W.Q⟩`, discharging
`PeerSpqrStateTight640` and `SessionGetPrev0Guard` at every prekey `recv` call site.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinKit

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall cliIo inputOf parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost RunSem addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (encDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
  (ckx2_w1EncExact_groupSpec ckx2_w1EncExact_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv RealCliMainBinaryEnvOf cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact (hmx_binaryKitRunSlotEnvsSlotOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (CanonicalOrFallbackPksmEnv)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter (ValidPostSetupWitness)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom (cliDecPkCanonSlotEnvExact')
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0PostBob
  (cliDecPkCanonSlotEnvExact'_groupSpec_of_cliPqOrD3RecvDom
   cliDecPkCanonSlotEnvExact'_phaseCredit_of_cliPqOrD3RecvDom)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
  (fits2_mkBinaryKitRealCalleeEnvsDecPk fits2_realCliMainBinaryKitEnvOfDecPk
   fits2_realCliMainBinaryKitEnvOfDecPk_fitsEnv_of_w1_and_w4 fits2_realCliRunBinaryKitEnvOfDecPk
   fits2_runEnvDecPk_sub_runBinaryKitEnvOfDecPk fits2_zbDom0Prime_fits_oneGiB_109)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact)

/-- Whole-`main` `FitsEnv` at `cliBudgetLimits` for `fits2_realCliMainBinaryKitEnvOfDecPk (cliDecPkCanonSlotEnvExact' X W)` under `CliPqxdhInputs`. -/
theorem realCliMainBinaryKitEnvOfExact'_fitsEnv_cliBudgetLimits_closed [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (fits2_realCliMainBinaryKitEnvOfDecPk (cliDecPkCanonSlotEnvExact' X W) img S X W i) :=
  fits2_realCliMainBinaryKitEnvOfDecPk_fitsEnv_of_w1_and_w4
    (cliDecPkCanonSlotEnvExact' X W) img S X W i hi
    (ckx2_w1EncExact_phaseCredit W)
    (ckx2_w1EncExact_groupSpec W)
    (fun _g _peerV _meV _rest _pm hi_g hp _hin _hc _hstdin _hpk hct =>
      cliDecPkCanonSlotEnvExact'_phaseCredit_of_cliPqOrD3RecvDom
        X W (Or.inl hi_g) hp rfl rfl hct)
    (Nat.le_refl _)
    (fun _g _peerV _meV _rest _pm hi_g hp _hin _hc _hstdin _hpk hct =>
      cliDecPkCanonSlotEnvExact'_groupSpec_of_cliPqOrD3RecvDom
        X W (Or.inl hi_g) hp rfl rfl hct)
    fits2_zbDom0Prime_fits_oneGiB_109

/-- Whole-`run` `RunEnv` inclusion into `fits2_realCliRunBinaryKitEnvOfDecPk (cliDecPkCanonSlotEnvExact' X W)` under `CliPqxdhInputs`. -/
theorem hole_hmain_runEnvExact'_sub_binaryKit_closed [LibsignalPlacement]
    {M : AllocCostModel}
    {FallbackEnv : PksmGhost → List AllocEvent → Prop}
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {g : RunCall}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W A B (realCliInitBinarySlotEnvFixed W)
            (cliDecPkCanonSlotEnvExact' X W))
          (CanonicalOrFallbackPksmEnv FallbackEnv)
          S)
        g evs →
      fits2_realCliRunBinaryKitEnvOfDecPk (cliDecPkCanonSlotEnvExact' X W) img S X W g evs :=
  fits2_runEnvDecPk_sub_runBinaryKitEnvOfDecPk
    (cliDecPkCanonSlotEnvExact' X W) img S X W A B hi hparse hin hS_enc hS_pksm

private example (g : RunCall) (meV peerV : AddrV) (pm : PreKeySignalMessage) :
    (r3bDecPkGhost g meV peerV pm).peer.val = addrValOf peerV ∧
      (r3bDecPkGhost g meV peerV pm).F = runFiles g.i :=
  ⟨rfl, rfl⟩

private example (i : Inputs) (w : ValidPostSetupWitness i) (peerV : AddrV)
    (hgc : w.g.c = .recv peerV) :
    w.g.i = i ∧
      parseArgs uuidTryParse (w.g.i.argv.map bytesOfString) = some (.recv peerV) :=
  ⟨w.g_i, hgc ▸ w.parse_ok⟩

private example [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs) :
    RealCliMainBinaryEnvOf
      (fits2_mkBinaryKitRealCalleeEnvsDecPk (cliDecPkCanonSlotEnvExact' X W) img S X W) i =
    fits2_realCliMainBinaryKitEnvOfDecPk (cliDecPkCanonSlotEnvExact' X W) img S X W i :=
  rfl

private example [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks) (g : RunCall) :
    CliRunBinaryEnv cliIo.rd
      (fits2_mkBinaryKitRealCalleeEnvsDecPk (cliDecPkCanonSlotEnvExact' X W) img S X W g)
      sessionCapBytes g =
    fits2_realCliRunBinaryKitEnvOfDecPk (cliDecPkCanonSlotEnvExact' X W) img S X W g :=
  rfl

private example [LibsignalPlacement] {M : AllocCostModel}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets) :
    binaryKitRunSlotEnvsExact W A B (realCliInitBinarySlotEnvFixed W)
      (cliDecPkCanonSlotEnvExact' X W) =
    hmx_binaryKitRunSlotEnvsSlotOf
      (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
      (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
      A B (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W) :=
  rfl

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinKit
