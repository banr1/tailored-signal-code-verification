/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.Fine.ClientIntegration
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.CliPubCalleesInstPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bPub
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineB
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3PksmAux
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliMemcpyRowSat

/-!
# Public and Pure-`fs` Callees Discharger at `h2k_ghFixedK` (`ElfSlicesPqOomH2KPubCallees`)

**Checked by Lean.**

Instantiates `CliPubCalleesInstPlacedBudgetFd` at `ghFixed := h2k_ghFixedK mpl mmpl`,
`fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart`, and `cliBudgetLimits` to close the
six `CliPubCalleesFrozenPlacedFd` and `SpineBPureFsCallees` obligations (`hpubCanon`,
`hpureFsCanon`, `hpubUntyped`, `hpureFsUntyped`, `hpubD3`, `hpureFsD3`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KPubCallees

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
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (CanonicalOrFallbackPksmEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
  (cliDecPkCanonSlotEnvExact' cliDecPkCanonSlotEnvExact'_ghost_congr)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (PqxdhAcceptBadKemErrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.CliPubCalleesInstPlacedBudgetFd
  (cliPubCallees_d2c_frozen_placed_fd kemDeserialize_slotWithFdsGe3Closed_cli_placed
   pksmSlot_okFs_fine_cli_placed_at_579 pksmSlot_okFs_of_subsetA4_fine_cli_placed_at_579
   tryFrom_okFs_fine_cli_placed_at_579)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
  (CliPubCalleesFrozenPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bPub
  (g5bp_decPkD3UntypedEnvOf_ghost_congr)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges (h2kb_hole2_hG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineB
  (SpineBPureFsCallees h2ksb_hole2_hHooksBundleFd h2ksb_untypedSlotEnvs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact hole3_canonOrFallbackPksmEnv_congr hole3_decSigEnv_r3a_congr
   hole3_encEnv_r2_congr hole3_initEnv_r1c_congr hole3_pksmTryFromEnv_congr)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3PksmAux
  (subsetA4PksmTryFromPlaced_canonOrFallback)
open VerifiedLibraries (mallocngLib)

/-- `CliPubCalleesFrozenPlacedFd` at `h2k_ghFixedK mpl mmpl`,
`binaryKitRunSlotEnvsExact … (cliDecPkCanonSlotEnvExact' X W)`, and
`CanonicalOrFallbackPksmEnv PksmTryFromEnv`. -/
theorem hpubCanon
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
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
        W := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro X W γ tp
  exact cliPubCallees_d2c_frozen_placed_fd mmpl (h2k_ghFixedK mpl mmpl) W
    (h2ksb_hole2_hHooksBundleFd mpl mmpl hLs hMm W γ tp)
    (hole3_initEnv_r1c_congr W)
    (hole3_encEnv_r2_congr W (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
    (hole3_decSigEnv_r3a_congr W (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
    hole3_canonOrFallbackPksmEnv_congr
    (cliDecPkCanonSlotEnvExact'_ghost_congr X W)

private theorem h2k_ghFixedK_memcpyStripKeepsFrozen [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (f : Arm64.State → Arm64.State)
    (hf : (h2k_ghFixedK mpl mmpl).memcpy = some f) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferCoreFd.MemcpyStripKeepsFrozen
      f := by
  dsimp only [h2k_ghFixedK] at hf
  injection hf with hfeq
  subst hfeq
  rw [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow_eq_narrow]
  exact
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliMemcpyRowSat.memcpyStripKeepsFrozen_memcpyGhostHook
      _ _ _ _

/-- `SpineBPureFsCallees` at `h2k_ghFixedK mpl mmpl`,
`CanonicalOrFallbackPksmEnv PksmTryFromEnv`, and `cliRunSemD2c_placed X W`. -/
theorem hpureFsCanon
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
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
        (cliDecryptPrekeyNeed cliRunBudgets) := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro X W γ tp
  have hG := h2kb_hole2_hG mpl mmpl hLs hMm γ tp
  exact
    { kemDeserialize :=
        kemDeserialize_slotWithFdsGe3Closed_cli_placed mmpl (h2k_ghFixedK mpl mmpl) W hG _ _ _
      tryFrom :=
        tryFrom_okFs_fine_cli_placed_at_579 γ mmpl tp cliElfImage.brkStart cliBudgetLimits
          (h2k_ghFixedK mpl mmpl) W hG (h2k_ghFixedK_memcpyStripKeepsFrozen mpl mmpl)
      pksmTryFrom :=
        pksmSlot_okFs_of_subsetA4_fine_cli_placed_at_579 γ mmpl tp cliElfImage.brkStart
          cliBudgetLimits (h2k_ghFixedK mpl mmpl) W hG
          (h2k_ghFixedK_memcpyStripKeepsFrozen mpl mmpl)
          (fun hC => subsetA4PksmTryFromPlaced_canonOrFallback hC)
          (fun _ => rfl) }

/-- `CliPubCalleesFrozenPlacedFd` at `h2k_ghFixedK mpl mmpl`, `h2ksb_untypedSlotEnvs W γ tp`,
and `PksmTryFromEnv`. -/
theorem hpubUntyped
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv)
        W := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro W γ tp
  exact cliPubCallees_d2c_frozen_placed_fd mmpl (h2k_ghFixedK mpl mmpl) W
    (h2ksb_hole2_hHooksBundleFd mpl mmpl hLs hMm W γ tp)
    (hole3_initEnv_r1c_congr W)
    (hole3_encEnv_r2_congr W (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
    (hole3_decSigEnv_r3a_congr W (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
    hole3_pksmTryFromEnv_congr
    (g5bp_decPkD3UntypedEnvOf_ghost_congr cliRunBudgets_placed
      (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv)

/-- `SpineBPureFsCallees` at `h2k_ghFixedK mpl mmpl`, `h2ksb_untypedSlotEnvs W γ tp`,
`PksmTryFromEnv`, and `cliRunSemD3 W`. -/
theorem hpureFsUntyped
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      SpineBPureFsCallees
        (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
        (cliRunSemD3 W)
        (cliDecryptPrekeyNeed cliRunBudgets_placed) := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro W γ tp
  have hG := h2kb_hole2_hG mpl mmpl hLs hMm γ tp
  exact
    { kemDeserialize :=
        kemDeserialize_slotWithFdsGe3Closed_cli_placed mmpl (h2k_ghFixedK mpl mmpl) W hG _ _ _
      tryFrom :=
        tryFrom_okFs_fine_cli_placed_at_579 γ mmpl tp cliElfImage.brkStart cliBudgetLimits
          (h2k_ghFixedK mpl mmpl) W hG (h2k_ghFixedK_memcpyStripKeepsFrozen mpl mmpl)
      pksmTryFrom :=
        pksmSlot_okFs_fine_cli_placed_at_579 γ mmpl tp cliElfImage.brkStart cliBudgetLimits
          (h2k_ghFixedK mpl mmpl) W hG (h2k_ghFixedK_memcpyStripKeepsFrozen mpl mmpl)
          (fun _ => rfl) }

/-- `CliPubCalleesFrozenPlacedFd` at `h2k_ghFixedK mpl mmpl` and `PksmTryFromEnv` for any D3
`RunSlotEnvs` satisfying the four ghost-erasure congruences. -/
theorem hpubD3
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
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
        W := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro W γ tp sEnvs hinit henc hdec hdp
  exact cliPubCallees_d2c_frozen_placed_fd mmpl (h2k_ghFixedK mpl mmpl) W
    (h2ksb_hole2_hHooksBundleFd mpl mmpl hLs hMm W γ tp)
    hinit henc hdec hole3_pksmTryFromEnv_congr hdp

/-- `SpineBPureFsCallees` at `h2k_ghFixedK mpl mmpl` and `PksmTryFromEnv` for any D3
`S : RunSem` with `S.pksmParse = pksmParse`. -/
theorem hpureFsD3
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (S : RunSem) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) (sEnvs : RunSlotEnvs),
      S.pksmParse = pksmParse →
      SpineBPureFsCallees
        (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        sEnvs PksmTryFromEnv S
        (cliDecryptPrekeyNeed cliRunBudgets) := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro S W γ tp sEnvs hParse
  have hG := h2kb_hole2_hG mpl mmpl hLs hMm γ tp
  exact
    { kemDeserialize :=
        kemDeserialize_slotWithFdsGe3Closed_cli_placed mmpl (h2k_ghFixedK mpl mmpl) W hG
          sEnvs S (cliDecryptPrekeyNeed cliRunBudgets)
      tryFrom :=
        tryFrom_okFs_fine_cli_placed_at_579 γ mmpl tp cliElfImage.brkStart cliBudgetLimits
          (h2k_ghFixedK mpl mmpl) W hG (h2k_ghFixedK_memcpyStripKeepsFrozen mpl mmpl)
      pksmTryFrom :=
        pksmSlot_okFs_fine_cli_placed_at_579 γ mmpl tp cliElfImage.brkStart cliBudgetLimits
          (h2k_ghFixedK mpl mmpl) W hG (h2k_ghFixedK_memcpyStripKeepsFrozen mpl mmpl)
          (fun b => congrFun hParse b) }

/-! ## `h2k_gap2_*` Aliases -/

theorem h2k_gap2_pubCanon
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
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
        W :=
  hpubCanon mpl mmpl hLs hMm

theorem h2k_gap2_pureFsCanon
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
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
        (cliDecryptPrekeyNeed cliRunBudgets) :=
  hpureFsCanon mpl mmpl hLs hMm

theorem h2k_gap2_pubUntyped
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv)
        W :=
  hpubUntyped mpl mmpl hLs hMm

theorem h2k_gap2_pureFsUntyped
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      SpineBPureFsCallees
        (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
        (cliRunSemD3 W)
        (cliDecryptPrekeyNeed cliRunBudgets_placed) :=
  hpureFsUntyped mpl mmpl hLs hMm

theorem h2k_gap2_pubD3
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
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
        W :=
  hpubD3 mpl mmpl hLs hMm

theorem h2k_gap2_pureFsD3
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (S : RunSem) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) (sEnvs : RunSlotEnvs),
      S.pksmParse = pksmParse →
      SpineBPureFsCallees
        (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        sEnvs PksmTryFromEnv S
        (cliDecryptPrekeyNeed cliRunBudgets) :=
  hpureFsD3 mpl mmpl hLs hMm

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KPubCallees
