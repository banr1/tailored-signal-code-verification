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
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinOverD3
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinPathB
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinValidMatch
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineB

/-!
# 6-Arm `H2KGhostArms` Join from Spine-B and Spine-C Interfaces (`ElfSlicesPqOomH2KGhostArmsOfIfaces`)

**Checked by Lean.**

Joins all six `h2asm_GhostMainArmsK` obligations (`hmain`, `hinitSem`, `huntyped`, `hoverD3`,
`hpathB`, `hvalidMatch`) at `h2kd3_witnessK mpl mmpl hLs hMm` from the Spine-B (`Block 579`) and
Spine-C (`Slots 464, 463, 521, 520`) interfaces, and provides `h2k_ghostArms_of_slots_and_spineBCallees`
wiring Spine-B public/pure-`fs` callee bundles with the eight slot contracts.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArmsOfIfaces

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
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm (h2asm_GhostMainArmsK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KAssembly
  (h2ka_branch2HookReplaysK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinOverD3
  (h2kd3_W4OverD3Slot520OkK h2kd3_ghostMainOkOverD3K_of_ifaces)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinPathB
  (h2kd3_W4PathBSlot520OkK h2kd3_ghostMainOkPathBK_of_ifaces)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinValidMatch
  (h2kd3_SpineBD3SlotsRunTightK h2kd3_W4ValidMatchSlot520OkK
   h2kd3_ghostMainOkValidMatchK_of_ifaces h2kd3_witnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
  (H2KGhostArms h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (h2ki_SpineBCanonSliceK h2ki_SpineBRunTightOfSemK h2ki_UntypedDecPkSlot520OkK
   h2ki_W1EncryptSlot464OkK h2ki_W2DecryptSignalSlot463OkK h2ki_W3InitSlot521OkK
   h2ki_W4DecPkCanonSlot520OkK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA
  (h2k_ghost_hinitSem_cliElfK h2k_ghost_hmain_cliElfK h2k_ghost_huntyped_cliElfK
   h2k_untypedRunEnvAt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineB
  (SpineBPureFsCallees h2ksb_hole2_hHooksBundleFd h2ksb_runTightAt579PreFd_of_slots
   h2ksb_spineBCanonSlice_mkWitnessK h2ksb_spineBUntyped_mkWitnessK h2ksb_untypedSlotEnvs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
  (CliPqBinaryV2OomF3BytesPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open VerifiedLibraries (mallocngLib)

/-! ## Interface Assemblers for `H2KGhostArms` -/

/-- Per-placement 6-arm `h2asm_GhostMainArmsK mpl mmpl` assembler from Spine-B and Spine-C
interfaces at `h2kd3_witnessK mpl mmpl hLs hMm`. -/
theorem h2k_ghostMainArmsK_of_ifaces
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hSpineBCanon : h2ki_SpineBCanonSliceK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hSpineBUntyped :
      h2ki_SpineBRunTightOfSemK (h2kd3_witnessK mpl mmpl hLs hMm) cliRunSemD3
        (h2k_untypedRunEnvAt (mmpl := mmpl) (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)))
    (hSpineBD3 : h2kd3_SpineBD3SlotsRunTightK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW1 : h2ki_W1EncryptSlot464OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW2 : h2ki_W2DecryptSignalSlot463OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW3 : h2ki_W3InitSlot521OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4OverD3 : h2kd3_W4OverD3Slot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4PathB : h2kd3_W4PathBSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4ValidMatch : h2kd3_W4ValidMatchSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm)) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainArmsK mpl mmpl :=
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  { hmain := h2k_ghost_hmain_cliElfK mpl mmpl hLs hMm hSpineBCanon
    hoverD3 :=
      h2kd3_ghostMainOkOverD3K_of_ifaces mpl mmpl hLs hMm hSpineBD3 hW1 hW2 hW3 hW4OverD3
    huntyped := h2k_ghost_huntyped_cliElfK mpl mmpl hLs hMm hSpineBUntyped
    hpathB :=
      h2kd3_ghostMainOkPathBK_of_ifaces mpl mmpl hLs hMm hSpineBD3 hW1 hW2 hW3 hW4PathB
    hvalidMatch :=
      h2kd3_ghostMainOkValidMatchK_of_ifaces mpl mmpl hLs hMm hSpineBD3 hW1 hW2 hW3 hW4ValidMatch
    hinitSem := h2k_ghost_hinitSem_cliElfK mpl mmpl hLs hMm hSpineBCanon }

/-- Combines all six `h2asm_GhostMainArmsK` arms into `H2KGhostArms` from Spine-B and Spine-C
interfaces. -/
theorem h2k_ghostArms_of_ifaces
    (hSpineBCanon :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_SpineBCanonSliceK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hSpineBUntyped :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_SpineBRunTightOfSemK (h2kd3_witnessK mpl mmpl hLs hMm) cliRunSemD3
          (h2k_untypedRunEnvAt (mmpl := mmpl) (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)))
    (hSpineBD3 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2kd3_SpineBD3SlotsRunTightK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW1 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W1EncryptSlot464OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW2 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W2DecryptSignalSlot463OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW3 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W3InitSlot521OkK (h2kd3_witnessK mpl mmpl hLs hMm))
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
  fun mpl mmpl hLs hMm =>
    h2k_ghostMainArmsK_of_ifaces mpl mmpl hLs hMm
      (hSpineBCanon mpl mmpl hLs hMm)
      (hSpineBUntyped mpl mmpl hLs hMm)
      (hSpineBD3 mpl mmpl hLs hMm)
      (hW1 mpl mmpl hLs hMm)
      (hW2 mpl mmpl hLs hMm)
      (hW3 mpl mmpl hLs hMm)
      (hW4OverD3 mpl mmpl hLs hMm)
      (hW4PathB mpl mmpl hLs hMm)
      (hW4ValidMatch mpl mmpl hLs hMm)

theorem h2k_cliPqBinaryV2OomF3BytesPlaced_cliElf_of_ifaces
    (hSpineBCanon :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_SpineBCanonSliceK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hSpineBUntyped :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_SpineBRunTightOfSemK (h2kd3_witnessK mpl mmpl hLs hMm) cliRunSemD3
          (h2k_untypedRunEnvAt (mmpl := mmpl) (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)))
    (hSpineBD3 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2kd3_SpineBD3SlotsRunTightK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW1 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W1EncryptSlot464OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW2 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W2DecryptSignalSlot463OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW3 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W3InitSlot521OkK (h2kd3_witnessK mpl mmpl hLs hMm))
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
    (h2k_ghostArms_of_ifaces hSpineBCanon hSpineBUntyped hSpineBD3
      hW1 hW2 hW3 hW4OverD3 hW4PathB hW4ValidMatch)

/-! ## Spine-B Callee and 8-Slot Wiring -/

/-- Closes `h2kd3_SpineBD3SlotsRunTightK (h2kd3_witnessK mpl mmpl hLs hMm)` from `hpub` and
`hpureFs` via `h2ksb_runTightAt579PreFd_of_slots` and `h2ksb_hole2_hHooksBundleFd`. -/
theorem h2kd3_spineBD3Slots_mkWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hpubD3 :
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
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (S : RunSem) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) (sEnvs : RunSlotEnvs),
        S.pksmParse = pksmParse →
        SpineBPureFsCallees
          (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          sEnvs PksmTryFromEnv S
          (cliDecryptPrekeyNeed cliRunBudgets)) :
    h2kd3_SpineBD3SlotsRunTightK (h2kd3_witnessK mpl mmpl hLs hMm) := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro h547 S W γ tp sEnvs hpksm hinit_addr henc_addr hdec_ghost hdp_ghost
    _A _H _needs henc hdecSig hinit hdecPk
  exact h2ksb_runTightAt579PreFd_of_slots hLs (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    (h2k_ghFixedK mpl mmpl)
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
    W sEnvs
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) sEnvs PksmTryFromEnv)
    S (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets)
    h547
    (h2ksb_hole2_hHooksBundleFd mpl mmpl hLs hMm W γ tp)
    (hpubD3 W γ tp sEnvs hinit_addr henc_addr hdec_ghost hdp_ghost)
    henc hdecSig hinit (by decide) hdecPk
    (hpureFsD3 S W γ tp sEnvs hpksm)

/-- Per-placement `h2asm_GhostMainArmsK` assembler from public/pure-`fs` callee bundles
(`hpub*`, `hpureFs*`) and the eight Spine-C slot contracts. -/
theorem h2k_ghostMainArmsK_of_slots_and_spineBCallees
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hpubCanon :
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
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (S : RunSem) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) (sEnvs : RunSlotEnvs),
        S.pksmParse = pksmParse →
        SpineBPureFsCallees
          (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          sEnvs PksmTryFromEnv S
          (cliDecryptPrekeyNeed cliRunBudgets))
    (hW1 : h2ki_W1EncryptSlot464OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW2 : h2ki_W2DecryptSignalSlot463OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW3 : h2ki_W3InitSlot521OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4Canon : h2ki_W4DecPkCanonSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4Untyped : h2ki_UntypedDecPkSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4OverD3 : h2kd3_W4OverD3Slot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4PathB : h2kd3_W4PathBSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4ValidMatch : h2kd3_W4ValidMatchSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm)) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainArmsK mpl mmpl :=
  h2k_ghostMainArmsK_of_ifaces mpl mmpl hLs hMm
    (h2ksb_spineBCanonSlice_mkWitnessK mpl mmpl hLs hMm
      (h2ka_branch2HookReplaysK mpl mmpl hLs hMm) hpubCanon hpureFsCanon hW1 hW2 hW3 hW4Canon)
    (h2ksb_spineBUntyped_mkWitnessK mpl mmpl hLs hMm
      (h2ka_branch2HookReplaysK mpl mmpl hLs hMm) hpubUntyped hpureFsUntyped hW1 hW2 hW3 hW4Untyped)
    (h2kd3_spineBD3Slots_mkWitnessK mpl mmpl hLs hMm hpubD3 hpureFsD3)
    hW1 hW2 hW3 hW4OverD3 hW4PathB hW4ValidMatch

/-- Global `H2KGhostArms` assembler from public/pure-`fs` callee bundles (`hpub*`, `hpureFs*`)
and the eight Spine-C slot contracts (`464`, `463`, `521`, and the five Slot-`520` slices). -/
theorem h2k_ghostArms_of_slots_and_spineBCallees
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
    (hW1 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W1EncryptSlot464OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW2 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W2DecryptSignalSlot463OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW3 :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W3InitSlot521OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4Canon :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_W4DecPkCanonSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4Untyped :
      ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
        (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
        h2ki_UntypedDecPkSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm))
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
  fun mpl mmpl hLs hMm =>
    h2k_ghostMainArmsK_of_slots_and_spineBCallees mpl mmpl hLs hMm
      (hpubCanon mpl mmpl hLs hMm)
      (hpureFsCanon mpl mmpl hLs hMm)
      (hpubUntyped mpl mmpl hLs hMm)
      (hpureFsUntyped mpl mmpl hLs hMm)
      (hpubD3 mpl mmpl hLs hMm)
      (hpureFsD3 mpl mmpl hLs hMm)
      (hW1 mpl mmpl hLs hMm)
      (hW2 mpl mmpl hLs hMm)
      (hW3 mpl mmpl hLs hMm)
      (hW4Canon mpl mmpl hLs hMm)
      (hW4Untyped mpl mmpl hLs hMm)
      (hW4OverD3 mpl mmpl hLs hMm)
      (hW4PathB mpl mmpl hLs hMm)
      (hW4ValidMatch mpl mmpl hLs hMm)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArmsOfIfaces
