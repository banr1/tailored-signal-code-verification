/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInstK
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArmsOfIfaces
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KDecPkPollKits
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot464
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520Untyped
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot521

/-!
# Partial `H2KGhostArms` Integration Over Slots `464`, `521`, and `520-Untyped` (`ElfSlicesPqOomH2KM1PreC6`)

**Checked by Lean.**

Instantiates `ElfSlicesPqOomH2KGhostArmsOfIfaces.h2k_ghostArms_of_slots_and_spineBCallees` with
the closed contracts for Slot `464` (`ElfSlicesPqOomH2KSlot464`), Slot `521`
(`ElfSlicesPqOomH2KSlot521`), and Slot `520` untyped (`ElfSlicesPqOomH2KSlot520Untyped` +
`ElfSlicesPqOomH2KDecPkPollKits`), parameterized over the remaining public/pure-`fs` callee and
slot interfaces.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1PreC6

open Arm64 (GhostName)
open Arm64.Obj (MultiPlacement)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets cliRunBudgets_placed)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem addrValOf)
open CryptoVerification.SignalSession.Cli.RunGlue (cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Heap.Fine (fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (CanonicalOrFallbackPksmEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom (cliDecPkCanonSlotEnvExact')
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
  (CliPubCalleesFrozenPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KAssembly
  (h2ka_branch2HookReplaysK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinOverD3
  (h2kd3_W4OverD3Slot520OkK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinPathB
  (h2kd3_W4PathBSlot520OkK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinValidMatch
  (h2kd3_W4ValidMatchSlot520OkK h2kd3_witnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KDecPkPollKits
  (h2k_cliDecPkPollKitsPlacedOkFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
  (H2KGhostArms h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArmsOfIfaces
  (h2k_ghostArms_of_slots_and_spineBCallees)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (h2ki_W2DecryptSignalSlot463OkK h2ki_W4DecPkCanonSlot520OkK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot464
  (h2k_w1EncryptSlot464OkK_mkWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520Untyped
  (h2ki_UntypedDecPkSlot520OkK_mkWitness_of_kitInstPollKits)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot521
  (h2k_w3InitSlot521Ok_mkWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineB
  (SpineBPureFsCallees h2ksb_untypedSlotEnvs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
  (CliPqBinaryV2OomF3BytesPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open VerifiedLibraries (mallocngLib)

/-- Instantiates `h2k_ghostArms_of_slots_and_spineBCallees` with `Slot464`, `Slot521`, and
`Slot520Untyped` (`h2k_cliDecPkPollKitsPlacedOkFds`). -/
theorem h2k_ghostArms_of_gaps_and_c6
    (hpubCanon :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (_hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
          CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
              (binaryKitRunSlotEnvsExact W
                (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
                (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
              (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
            W)
    (hpureFsCanon :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (_hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
          SpineBPureFsCallees
            (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
            (cliRunSemD2c_placed X W)
            (cliDecryptPrekeyNeed cliRunBudgets))
    (hpubUntyped :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (_hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
          CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
            (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
              (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv)
            W)
    (hpureFsUntyped :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (_hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
          SpineBPureFsCallees
            (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
            (cliRunSemD3 W)
            (cliDecryptPrekeyNeed cliRunBudgets_placed))
    (hpubD3 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (_hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64) (sEnvs : RunSlotEnvs),
          (∀ g d2 fsp,
            sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64)) →
          (∀ g peerV (peerG : AddrGhost) meG fsp,
            peerG.val = addrValOf peerV →
            sEnvs.encrypt (r2EncGhost g peerG meG fsp) =
              sEnvs.encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64)) →
          (∀ g fsp w peerV meG msgG m,
            sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
              sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m)) →
          (∀ x y : DecPkGhost,
            x.peer.val = y.peer.val → x.me.val = y.me.val →
            x.stores = y.stores → x.coinsP = y.coinsP →
            x.F = y.F → x.coins = y.coins → x.msg = y.msg →
            sEnvs.decryptPrekey x = sEnvs.decryptPrekey y) →
          CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            sEnvs
            (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) sEnvs PksmTryFromEnv)
            W)
    (hpureFsD3 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (_hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        ∀ (S : RunSem) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) (sEnvs : RunSlotEnvs),
          S.pksmParse = pksmParse →
          SpineBPureFsCallees
            (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            sEnvs PksmTryFromEnv S
            (cliDecryptPrekeyNeed cliRunBudgets))
    (hW4Canon :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W4DecPkCanonSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW2 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W2DecryptSignalSlot463OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4OverD3 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2kd3_W4OverD3Slot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4PathB :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2kd3_W4PathBSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4ValidMatch :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2kd3_W4ValidMatchSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm)) :
    H2KGhostArms :=
  h2k_ghostArms_of_slots_and_spineBCallees
    hpubCanon
    hpureFsCanon
    hpubUntyped
    hpureFsUntyped
    hpubD3
    hpureFsD3
    (fun mpl mmpl hLs hMm =>
      h2k_w1EncryptSlot464OkK_mkWitnessK mpl mmpl hLs hMm
        (h2ka_branch2HookReplaysK mpl mmpl hLs hMm))
    hW2
    (fun mpl mmpl hLs hMm =>
      h2k_w3InitSlot521Ok_mkWitnessK mpl mmpl hLs hMm
        (h2ka_branch2HookReplaysK mpl mmpl hLs hMm))
    hW4Canon
    (fun mpl mmpl hLs hMm =>
      h2ki_UntypedDecPkSlot520OkK_mkWitness_of_kitInstPollKits mpl mmpl hLs hMm
        (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
        (h2k_cliDecPkPollKitsPlacedOkFds mpl mmpl hLs hMm))
    hW4OverD3
    hW4PathB
    hW4ValidMatch

theorem h2k_cliPqBinaryV2OomF3BytesPlaced_cliElf_of_gaps_and_c6
    (hpubCanon :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (_hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
          CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
              (binaryKitRunSlotEnvsExact W
                (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
                (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
              (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
            W)
    (hpureFsCanon :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (_hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
          SpineBPureFsCallees
            (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
            (cliRunSemD2c_placed X W)
            (cliDecryptPrekeyNeed cliRunBudgets))
    (hpubUntyped :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (_hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
          CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
            (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
              (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv)
            W)
    (hpureFsUntyped :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (_hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
          SpineBPureFsCallees
            (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
            (cliRunSemD3 W)
            (cliDecryptPrekeyNeed cliRunBudgets_placed))
    (hpubD3 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (_hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64) (sEnvs : RunSlotEnvs),
          (∀ g d2 fsp,
            sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64)) →
          (∀ g peerV (peerG : AddrGhost) meG fsp,
            peerG.val = addrValOf peerV →
            sEnvs.encrypt (r2EncGhost g peerG meG fsp) =
              sEnvs.encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64)) →
          (∀ g fsp w peerV meG msgG m,
            sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
              sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m)) →
          (∀ x y : DecPkGhost,
            x.peer.val = y.peer.val → x.me.val = y.me.val →
            x.stores = y.stores → x.coinsP = y.coinsP →
            x.F = y.F → x.coins = y.coins → x.msg = y.msg →
            sEnvs.decryptPrekey x = sEnvs.decryptPrekey y) →
          CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            sEnvs
            (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) sEnvs PksmTryFromEnv)
            W)
    (hpureFsD3 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (_hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        ∀ (S : RunSem) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) (sEnvs : RunSlotEnvs),
          S.pksmParse = pksmParse →
          SpineBPureFsCallees
            (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            sEnvs PksmTryFromEnv S
            (cliDecryptPrekeyNeed cliRunBudgets))
    (hW4Canon :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W4DecPkCanonSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW2 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W2DecryptSignalSlot463OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4OverD3 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2kd3_W4OverD3Slot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4PathB :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2kd3_W4PathBSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4ValidMatch :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2kd3_W4ValidMatchSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm)) :
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf
    (h2k_ghostArms_of_gaps_and_c6
      hpubCanon hpureFsCanon hpubUntyped hpureFsUntyped hpubD3 hpureFsD3
      hW4Canon hW2 hW4OverD3 hW4PathB hW4ValidMatch)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1PreC6
