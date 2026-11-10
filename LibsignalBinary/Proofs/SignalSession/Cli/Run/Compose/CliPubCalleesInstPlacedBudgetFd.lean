/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.SpecBudgetFine
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserializeOkFsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `CliPubCalleesPlacedFd` / `CliPubCalleesFrozenPlacedFd` and Pure-`fs` Callee Dischargers

Instantiates `CliPubCalleesFrozenPlacedFd` (`cliPubCallees_d2c_frozen_placed_fd`) and discharges
the three `fs`-preserving callees on Block `579`:
- Block `590` (`kemDeserialize_slotWithFdsGe3Closed_cli_placed`),
- Block `85` (`tryFrom_okFs_mallocng_cli_placed_at_579`, `tryFrom_okFs_fine_cli_placed_at_579`),
- Block `111` (`pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579`,
  `pksmSlot_okFs_of_subsetA4_fine_cli_placed_at_579`, `pksmSlot_okFs_fine_cli_placed_at_579`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.CliPubCalleesInstPlacedBudgetFd

open Arm64
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPl_111 lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (doReserveStackX extHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets cliRunNeeds cliWrOk handleErrorSymCli)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_590 lsProg_563 lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost PksmGhost RunSem addrValOf)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced pathNeed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits MallocngCostModelIface MallocngCostModelSound
   RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineCostModelIface fineCostModelSound)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (fineHookRustCliAllocBudget mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudgetFd
  (path_placed_caller_ok_of_allocFs_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (lsReadFile_withLsCodeRoLoaded_of_hookSat)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetFd
  (bundleRead_placed_caller_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
  (cliRunArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudgetFd
  (cliPubCallees_frozen_placed_fd_of_pre_init1_init2)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (pksmSlotSpecPlacedOkFs tryFromPlacedSpecOkFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetFd
  (run_hop_pre_of_slots_placed_ok_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetFd
  (run_hop_init1_of_slots_placed_ok_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudgetFd
  (r1b_step_deser_clone_of_kem_placed_env_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudgetFd
  (r1b_step_tail_25f4_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudgetFd
  (r1b_step_reg_spk_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetFd
  (run_hop_init2_of_slots_placed_ok_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
  (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
  (CliPubCalleesFrozenPlacedFd CliRunHooksBundleFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferCoreFd
  (MemcpyStripKeepsFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferPlacedBudgetFd
  (pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579_impl
   tryFrom_okFs_mallocng_cli_placed_at_579_impl)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlacedBudget
  (subsetA4PksmTryFromPlaced_of_codecHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserializeOkFsPlacedBudgetFd
  (kemDeserialize_slotWithFdsGe3Closed_cli_placed_impl)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (SubsetA4PksmTryFromPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (slotWithFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (bundleReadSpecPlaced pathSpecPlaced)

theorem bundleReadNeed_stack_le :
    0x50 + max (max pathNeed cliRunBudgets.readFile) extHookStack ≤
      cliRunBudgets.bundleReadNeed := by
  decide

/-- Discharges `path` on `lsProg_589` calling Block `596` from `CliRunHooksBundleFd`. -/
theorem path589_cli_placed_fd [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (W : CliHooks)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim ReadEnv) :
    subroutine_ok (lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv pathNeed)) :=
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  let hh := hHooks.runHooks
  path_placed_caller_ok_of_allocFs_fd
    (callerProg := lsProg_589 H) (i := 589)
    (resStack := doReserveStackX)
    hh.allocFs (by decide) (by decide)
    (hh.panics handleErrorSymCli (by decide))
    (by decide)

/-- Discharges `bundleRead` on `lsProg_579` from `CliRunHooksBundleFd`. -/
theorem bundleRead_cli_placed_fd [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (W : CliHooks)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim ReadEnv)
    {stk : Nat} (hstk : cliRunBudgets.bundleReadNeed ≤ stk) :
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 563)
      (withFdsGe3Closed
        (bundleReadSpecPlaced cliIo.rd cliWrOk A lim (cliRunCalleesEnvs ReadEnv).bundleRead stk)) :=
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  let hh := hHooks.runHooks
  bundleRead_placed_caller_ok_of_deps_fd
    (callerProg := lsProg_579 H) (i := 579)
    (pathProg := lsProg_563 H) (jPath := 563)
    (readProg := lsProg_563 H) (jRead := 563)
    (fun _ hp => hp.2) hh.allocFs
    (by decide) (by decide)
    (path_placed_caller_ok_of_allocFs_fd (callerProg := lsProg_563 H) (i := 563)
      (resStack := doReserveStackX) hh.allocFs (by decide) (by decide)
      (hh.panics handleErrorSymCli (by decide)) (by decide))
    (by decide) (by decide)
    (lsReadFile_withLsCodeRoLoaded_of_hookSat (callerProg := lsProg_563 H) (i := 563)
      hHooks.readFileSat (by decide) (by decide))
    (hh.fs (lsProg_563 H) 563)
    (Nat.le_trans bundleReadNeed_stack_le hstk)
    (by decide)

/-- Discharges `kemDeserialize` (`slotWithFdsGe3Closed`, Block `590`) on `lsProg_579` from
`CliGhostAllocHooks`. -/
theorem kemDeserialize_slotWithFdsGe3Closed_cli_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (sEnvs : RunSlotEnvs) (S : RunSem) (decPkNeed : Nat) :
    (slotWithFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).kemDeserialize).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_590).base :=
  kemDeserialize_slotWithFdsGe3Closed_cli_placed_impl mmpl g W hG sEnvs S (cliRunNeeds decPkNeed)

/-- Discharges all 7 fields of `CliPubCalleesFrozenPlacedFd` at `cliRunCalleesEnvs ReadEnv` and
`cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmEnv` from `CliRunHooksBundleFd`. -/
theorem cliPubCallees_d2c_frozen_placed_fd [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmEnv : PksmGhost → List AllocEvent → Prop}
    (W : CliHooks)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim ReadEnv)
    (hinit_addr : ∀ g d2 fsp,
      sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64) := by
      intros; rfl)
    (henc_addr : ∀ g peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) =
        sEnvs.encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64) := by
      intros; rfl)
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) := by
      intros; rfl)
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmEnv x = PksmEnv y := by
      intros; rfl)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y := by intros; rfl) :
    CliPubCalleesFrozenPlacedFd mmpl g A lim (cliRunCalleesEnvs ReadEnv) sEnvs
      (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmEnv) W :=
  cliPubCallees_frozen_placed_fd_of_pre_init1_init2 mmpl g W hHooks
    (path589_cli_placed_fd mmpl g W hHooks)
    (fun hstk => bundleRead_cli_placed_fd mmpl g W hHooks hstk)
    (fun S decPkNeed =>
      run_hop_pre_of_slots_placed_ok_fd
        (slots := slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed))
        (sEnvs := sEnvs) (needs := cliRunNeeds decPkNeed) rfl)
    (fun S decPkNeed =>
      run_hop_init1_of_slots_placed_ok_fd
        (slots := slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed))
        (sEnvs := sEnvs) (needs := cliRunNeeds decPkNeed) rfl)
    (fun S decPkNeed =>
      run_hop_init2_of_slots_placed_ok_fd
        (slots := slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed))
        (sEnvs := sEnvs) (needs := cliRunNeeds decPkNeed)
        (fun hh hc hdrop hbnd he hok hfds hx28 =>
          r1b_step_reg_spk_placed_fd hh hc hdrop hbnd he hok hfds hx28)
        r1b_step_deser_clone_of_kem_placed_env_fd
        r1b_step_tail_25f4_placed_fd
        rfl rfl)
    hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost

/-- Discharges `tryFromPlacedSpecOkFs` (Block `85`) on `lsProg_579` at
`mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart` from `CliGhostAllocHooks`. -/
theorem tryFrom_okFs_mallocng_cli_placed_at_579 [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hMcSkf : ∀ f, g.memcpy = some f → MemcpyStripKeepsFrozen f) :
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpecOkFs (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim)) :=
  tryFrom_okFs_mallocng_cli_placed_at_579_impl I hS γ mmpl tp brkStart lim g W hG hMcSkf

theorem tryFrom_okFs_fine_cli_placed_at_579 [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim g)
    (hMcSkf : ∀ f, g.memcpy = some f → MemcpyStripKeepsFrozen f) :
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpecOkFs (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :=
  tryFrom_okFs_mallocng_cli_placed_at_579 _ _ γ mmpl tp brkStart lim g W hG hMcSkf

/-- Discharges `pksmSlotSpecPlacedOkFs` (Block `111`) on `lsProg_579` at
`mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart` for any envelope `PksmEnv` constructible
from `CodecHooksPlaced`. -/
theorem pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579 [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks)
    {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hMcSkf : ∀ f, g.memcpy = some f → MemcpyStripKeepsFrozen f)
    (hSub : ∀ {A' : RustCliAllocBudget M} {H' : LibsignalHooks},
      CodecHooksPlaced M A' lim H' → SubsetA4PksmTryFromPlaced M A' lim PksmEnv H')
    (hParse : ∀ b, S.pksmParse b = pksmParse b) :
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim PksmEnv S) :=
  pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579_impl I hS γ mmpl tp brkStart lim g W hG
    hMcSkf hSub hParse

/-- `fineHookRustCliAllocBudget` specialization of
`pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579` (instantiate `hSub` with
`Hole3PksmAux.subsetA4PksmTryFromPlaced_canonOrFallback` for `CanonicalOrFallbackPksmEnv PksmTryFromEnv`). -/
theorem pksmSlot_okFs_of_subsetA4_fine_cli_placed_at_579 [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks)
    {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    (hG : CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim g)
    (hMcSkf : ∀ f, g.memcpy = some f → MemcpyStripKeepsFrozen f)
    (hSub : ∀ {A' : RustCliAllocBudget fineCostModel} {H' : LibsignalHooks},
      CodecHooksPlaced fineCostModel A' lim H' →
        SubsetA4PksmTryFromPlaced fineCostModel A' lim PksmEnv H')
    (hParse : ∀ b, S.pksmParse b = pksmParse b) :
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) blkPl_111.base
      (pksmSlotSpecPlacedOkFs fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim PksmEnv S) :=
  pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579 _ _ γ mmpl tp brkStart lim g W hG hMcSkf
    hSub hParse

/-- Ready-to-apply `PksmTryFromEnv` specialization of `pksmSlot_okFs_of_subsetA4_fine_cli_placed_at_579`
(for `hpureFsUntyped` and `hpureFsD3`). -/
theorem pksmSlot_okFs_fine_cli_placed_at_579 [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks)
    {S : RunSem}
    (hG : CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim g)
    (hMcSkf : ∀ f, g.memcpy = some f → MemcpyStripKeepsFrozen f)
    (hParse : ∀ b, S.pksmParse b = pksmParse b) :
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) blkPl_111.base
      (pksmSlotSpecPlacedOkFs fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim PksmTryFromEnv S) :=
  pksmSlot_okFs_of_subsetA4_fine_cli_placed_at_579 γ mmpl tp brkStart lim g W hG hMcSkf
    (fun hC => subsetA4PksmTryFromPlaced_of_codecHooks hC) hParse

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.CliPubCalleesInstPlacedBudgetFd
