/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded `RunArmsPlacedFd` and `CliPubCalleesPlacedFd` Aggregator

Assembles the file-descriptor-preserving (`FdsGe3Closed`) arm hop contracts on Block `579`
(`signal_session::run`) into `RunArmsPlacedFd`, `CliPubCalleesPlacedFd`, and their `LibsignalFrozen`
counterparts.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalFrozen LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles LibsignalCodeRoLoaded)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliResStack cliRunBudgets cliRunNeeds cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost PksmGhost RunNeeds RunSem addrValOf)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets pathNeed)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
  (cliRunArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (RunHopInit1PlacedFd RunHopInit1PlacedFdOf RunHopInit2PlacedFd RunHopInit2PlacedFdOf
   RunHopPrePlacedFd RunHopPrePlacedFdOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlacedBudget
  (run_hop_join_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget (PreEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget (Init1Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget (Init2Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
  (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudgetFd
  (run_hop_init3_of_slots_placed_ok_fd run_hop_init3_placed_ok_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudgetFd
  (run_hop_send_of_slots_placed_ok_fd run_hop_send_placed_ok_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetFd
  (run_hop_recvW_frozen_placed_ok_fd run_hop_recvW_placed_ok_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget
  (run_hop_recvBad_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudgetFd
  (run_hop_recvP_frozen_placed_ok_fd run_hop_recvP_placed_ok_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
  (CliPubCalleesFrozenPlacedFd CliPubCalleesPlacedFd CliRunHooksBundleFd
   cliPubCallees_of_arms_frozen_placed_fd cliPubCallees_of_arms_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudgetFd
  (RunArmsFrozenPlacedFd RunArmsPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunCalleesEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (bundleReadSpecPlaced pathSpecPlaced)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
  (cliRunArmEnvs cliRunCalleesEnvs)

/-! ## `LibsignalCodeRoLoaded` Aggregators -/

/-- Discharges `join`, `init3`, `send`, `recvW`, `recvP`, and `recvBad` on Block `579`, reducing `RunArmsPlacedFd` to `pre`, `init1`, and `init2`. -/
theorem runArmsPlacedFd_of_pre_init1_init2 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hpre : RunHopPrePlacedFd (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs (PreEnv cEnvs)
      H B S needs resStack)
    (hinit1 : RunHopInit1PlacedFd (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs (Init1Env cEnvs)
      H B S needs resStack)
    (hinit2 : RunHopInit2PlacedFd (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs (Init2Env cEnvs)
      H B S needs resStack)
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
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmTryFromEnv x = PksmTryFromEnv y := by
      intros; rfl)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y := by intros; rfl) :
    RunArmsPlacedFd (LibsignalCodeRoLoaded lsmpl) A lim
      cEnvs sEnvs (cliRunArmEnvs cEnvs sEnvs PksmTryFromEnv S) H B S needs resStack :=
  { join := run_hop_join_placed_ok
    pre := hpre
    init1 := hinit1
    init2 := hinit2
    init3 := run_hop_init3_placed_ok_fd hinit_addr
    send := run_hop_send_placed_ok_fd henc_addr
    recvW := run_hop_recvW_placed_ok_fd hdec_ghost
    recvP := run_hop_recvP_placed_ok_fd hpksm_addr hdp_ghost
    recvBad := run_hop_recvBad_placed_ok }

/-- Assembles `CliPubCalleesPlacedFd` from `CliRunHooksBundleFd`, `hPath589`, `hBundleRead`, `pre`, `init1`, and `init2`. -/
theorem cliPubCallees_placed_fd_of_pre_init1_init2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (W : CliHooks)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim ReadEnv)
    (hPath589 : subroutine_ok
      (lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv pathNeed)))
    (hBundleRead : ∀ {stk : Nat}, cliRunBudgets.bundleReadNeed ≤ stk →
      subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 563)
        (withFdsGe3Closed
          (bundleReadSpecPlaced cliIo.rd cliWrOk A lim (cliRunCalleesEnvs ReadEnv).bundleRead stk)))
    (hpre : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopPrePlacedFd (LibsignalCodeRoLoaded lsmpl) A lim (cliRunCalleesEnvs ReadEnv) sEnvs
        (PreEnv (cliRunCalleesEnvs ReadEnv))
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
        cliResStack)
    (hinit1 : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopInit1PlacedFd (LibsignalCodeRoLoaded lsmpl) A lim (cliRunCalleesEnvs ReadEnv) sEnvs
        (Init1Env (cliRunCalleesEnvs ReadEnv))
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
        cliResStack)
    (hinit2 : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopInit2PlacedFd (LibsignalCodeRoLoaded lsmpl) A lim (cliRunCalleesEnvs ReadEnv) sEnvs
        (Init2Env (cliRunCalleesEnvs ReadEnv))
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
        cliResStack)
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
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmTryFromEnv x = PksmTryFromEnv y := by
      intros; rfl)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y := by intros; rfl) :
    CliPubCalleesPlacedFd mmpl g A lim (cliRunCalleesEnvs ReadEnv) sEnvs
      (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv) W :=
  cliPubCallees_of_arms_placed_fd mmpl g W hHooks hPath589 hBundleRead fun S decPkNeed =>
    runArmsPlacedFd_of_pre_init1_init2
      (hpre S decPkNeed) (hinit1 S decPkNeed) (hinit2 S decPkNeed)
      hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost

/-! ## `LibsignalFrozen` Aggregators -/

/-- Discharges `join`, `joinRo`, `init3`, `send`, `recvW`, `recvP`, and `recvBad` at `slotsOfSigPkFrozenPlaced`, reducing `RunArmsFrozenPlacedFd` to `pre`, `init1`, and `init2`. -/
theorem runArmsFrozenPlacedFd_of_pre_init1_init2 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hpre : RunHopPrePlacedFdOf (LibsignalFrozen lsmpl) A lim cEnvs (PreEnv cEnvs) H B S
      (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) resStack)
    (hinit1 : RunHopInit1PlacedFdOf (LibsignalCodeRoLoaded lsmpl) A lim cEnvs (Init1Env cEnvs) H B S
      (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) resStack)
    (hinit2 : RunHopInit2PlacedFdOf (LibsignalCodeRoLoaded lsmpl) A lim cEnvs (Init2Env cEnvs) H B S
      (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) resStack)
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
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmTryFromEnv x = PksmTryFromEnv y := by
      intros; rfl)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y := by intros; rfl) :
    RunArmsFrozenPlacedFd A lim cEnvs sEnvs (cliRunArmEnvs cEnvs sEnvs PksmTryFromEnv S) H B S
      needs resStack :=
  { join := run_hop_join_placed_ok
    joinRo := run_hop_join_placed_ok
    pre := hpre
    init1 := hinit1
    init2 := hinit2
    init3 :=
      run_hop_init3_of_slots_placed_ok_fd
        (slots := slotsOfSigPkFrozenPlaced A lim sEnvs S needs)
        (sEnvs := sEnvs) (needs := needs) rfl rfl hinit_addr
    send :=
      run_hop_send_of_slots_placed_ok_fd
        (slots := slotsOfSigPkFrozenPlaced A lim sEnvs S needs)
        (sEnvs := sEnvs) (needs := needs) rfl rfl henc_addr
    recvW := run_hop_recvW_frozen_placed_ok_fd hdec_ghost
    recvP := run_hop_recvP_frozen_placed_ok_fd hpksm_addr hdp_ghost
    recvBad := run_hop_recvBad_placed_ok }

/-- Assembles `CliPubCalleesFrozenPlacedFd` from `CliRunHooksBundleFd`, `hPath589`, `hBundleRead`, `pre`, `init1`, and `init2`. -/
theorem cliPubCallees_frozen_placed_fd_of_pre_init1_init2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (W : CliHooks)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim ReadEnv)
    (hPath589 : subroutine_ok
      (lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv pathNeed)))
    (hBundleRead : ∀ {stk : Nat}, cliRunBudgets.bundleReadNeed ≤ stk →
      subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 563)
        (withFdsGe3Closed
          (bundleReadSpecPlaced cliIo.rd cliWrOk A lim (cliRunCalleesEnvs ReadEnv).bundleRead stk)))
    (hpre : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopPrePlacedFdOf (LibsignalFrozen lsmpl) A lim (cliRunCalleesEnvs ReadEnv)
        (PreEnv (cliRunCalleesEnvs ReadEnv))
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S
        (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)) cliResStack)
    (hinit1 : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopInit1PlacedFdOf (LibsignalCodeRoLoaded lsmpl) A lim (cliRunCalleesEnvs ReadEnv)
        (Init1Env (cliRunCalleesEnvs ReadEnv))
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S
        (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)) cliResStack)
    (hinit2 : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopInit2PlacedFdOf (LibsignalCodeRoLoaded lsmpl) A lim (cliRunCalleesEnvs ReadEnv)
        (Init2Env (cliRunCalleesEnvs ReadEnv))
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S
        (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)) cliResStack)
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
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmTryFromEnv x = PksmTryFromEnv y := by
      intros; rfl)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y := by intros; rfl) :
    CliPubCalleesFrozenPlacedFd mmpl g A lim (cliRunCalleesEnvs ReadEnv) sEnvs
      (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv) W :=
  cliPubCallees_of_arms_frozen_placed_fd mmpl g W hHooks hPath589 hBundleRead fun S decPkNeed =>
    runArmsFrozenPlacedFd_of_pre_init1_init2
      (hpre S decPkNeed) (hinit1 S decPkNeed) (hinit2 S decPkNeed)
      hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudgetFd
