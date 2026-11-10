/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInstK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1PreC6 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KPubCallees
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot463
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520Canon
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520OverD3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520PathB
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520Vm

/-!
# Closed K-Route Ghost-Arms and `CliPqBinaryV2OomF3BytesPlaced` Assembly (`ElfSlicesPqOomH2KM1`)

**Checked by Lean.**

Instantiates `ElfSlicesPqOomH2KM1PreC6.h2k_ghostArms_of_gaps_and_c6` with all remaining slot
closers (`ElfSlicesPqOomH2KSlot463`, `ElfSlicesPqOomH2KSlot520OverD3`,
`ElfSlicesPqOomH2KSlot520PathB`, `ElfSlicesPqOomH2KSlot520Vm`, `ElfSlicesPqOomH2KSlot520Canon`)
and public/pure-`fs` callee dischargers (`ElfSlicesPqOomH2KPubCallees`), proving `H2KGhostArms`
and `CliPqBinaryV2OomF3BytesPlaced cliElfBytes` unconditionally.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1

open Arm64 (GhostName)
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
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinValidMatch
  (h2kd3_witnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
  (H2KGhostArms h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (h2ki_W4DecPkCanonSlot520OkK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1PreC6
  (h2k_ghostArms_of_gaps_and_c6)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KPubCallees
  (h2k_gap2_pubCanon h2k_gap2_pubD3 h2k_gap2_pubUntyped h2k_gap2_pureFsCanon h2k_gap2_pureFsD3
    h2k_gap2_pureFsUntyped)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot463
  (h2k463_w2DecryptSignalSlot463OkK_mkWitness)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520Canon
  (h2k520c_w4DecPkCanonSlot520OkK_mkWitness)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520OverD3
  (h2k520od3_w4OverD3Slot520OkK_mkWitness)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520PathB
  (h2k520pb_w4PathBSlot520OkK_mkWitness)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520Vm
  (h2k520vm_w4ValidMatchSlot520OkK_mkWitness)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineB
  (SpineBPureFsCallees h2ksb_untypedSlotEnvs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
  (CliPqBinaryV2OomF3BytesPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open VerifiedLibraries (mallocngLib)

/-- Discharges the `canon'` Slot-`520` obligation via `h2k520c_w4DecPkCanonSlot520OkK_mkWitness`
and `h2ka_branch2HookReplaysK`. -/
theorem h2k_w4Canon
    (mpl mmpl : Arm64.Obj.MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    h2ki_W4DecPkCanonSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm) :=
  h2k520c_w4DecPkCanonSlot520OkK_mkWitness hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)

/-- Proves `H2KGhostArms` from the six public/pure-`fs` callee obligations (`hpub*`,
`hpureFs*`) and `hW4Canon`, instantiating Slots `464`, `463`, `521`, `520-Untyped`, `520-OverD3`,
`520-PathB`, and `520-ValidMatch`. -/
theorem h2k_ghostArms_closed_of_gaps
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
        h2ki_W4DecPkCanonSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm)) :
    H2KGhostArms :=
  h2k_ghostArms_of_gaps_and_c6
    hpubCanon
    hpureFsCanon
    hpubUntyped
    hpureFsUntyped
    hpubD3
    hpureFsD3
    hW4Canon
    (fun mpl mmpl hLs hMm =>
      h2k463_w2DecryptSignalSlot463OkK_mkWitness hLs hMm
        (h2ka_branch2HookReplaysK mpl mmpl hLs hMm))
    (fun mpl mmpl hLs hMm =>
      h2k520od3_w4OverD3Slot520OkK_mkWitness hLs hMm
        (h2ka_branch2HookReplaysK mpl mmpl hLs hMm))
    (fun mpl mmpl hLs hMm =>
      h2k520pb_w4PathBSlot520OkK_mkWitness hLs hMm
        (h2ka_branch2HookReplaysK mpl mmpl hLs hMm))
    (fun mpl mmpl hLs hMm =>
      h2k520vm_w4ValidMatchSlot520OkK_mkWitness hLs hMm
        (h2ka_branch2HookReplaysK mpl mmpl hLs hMm))

theorem h2k_cliPqBinaryV2OomF3BytesPlaced_cliElf_of_gaps
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
        h2ki_W4DecPkCanonSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm)) :
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf
    (h2k_ghostArms_closed_of_gaps
      hpubCanon hpureFsCanon hpubUntyped hpureFsUntyped hpubD3 hpureFsD3 hW4Canon)

/-- Proves `H2KGhostArms` from the six public/pure-`fs` callee obligations (`hpub*`,
`hpureFs*`), discharging all eight Spine-C slot obligations. -/
theorem h2k_ghostArms_closed_of_gap2
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
            (cliDecryptPrekeyNeed cliRunBudgets)) :
    H2KGhostArms :=
  h2k_ghostArms_closed_of_gaps
    hpubCanon hpureFsCanon hpubUntyped hpureFsUntyped hpubD3 hpureFsD3 h2k_w4Canon

/-- Unconditional proof of `H2KGhostArms` across all valid `(mpl, mmpl)` placements of
`cliElfBytes`. -/
theorem h2k_ghostArms_closed : H2KGhostArms :=
  h2k_ghostArms_closed_of_gap2
    h2k_gap2_pubCanon
    h2k_gap2_pureFsCanon
    h2k_gap2_pubUntyped
    h2k_gap2_pureFsUntyped
    h2k_gap2_pubD3
    h2k_gap2_pureFsD3

/-- Unconditional proof of `CliPqBinaryV2OomF3BytesPlaced cliElfBytes`. -/
theorem h2k_cliPqBinaryV2OomF3BytesPlaced_cliElf :
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf h2k_ghostArms_closed

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1
