/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommit
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `RunArmsPlaced` and `CliPubCalleesPlaced` Aggregator

Assembles all nine budget-threaded arm hop contracts and the six non-slot public/directory callee
contracts on Block `579` (`signal_session::run`) into `RunArmsPlaced`, `CliPubCalleesPlacedAt`, and
`CliPubCalleesPlaced`, along with their `LibsignalFrozen` counterparts.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliResStack cliRunBudgets cliRunNeeds cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPl_553 lsProg_563 lsProg_589 lsProg_592 lsProg_593)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost PksmGhost RunNeeds RunSem addrValOf)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunSkeleton
  (RunBudgets pathNeed splitIdNeed splitSignedNeed)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudget (dirGet_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudget
  (BundleReadEnv bundleRead_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofPlacedBudget
  (cliDropSpe_placed_caller_ok_x)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudget
  (SplitIdEnv splitId_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudget
  (SplitSignedEnv splitSigned_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlacedBudget
  (run_hop_join_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
  (PreEnv run_hop_pre_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget
  (Init1Env run_hop_init1_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget
  (Init2Env run_hop_init2_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
  (R1cInit3Env r1cInitGhost run_hop_init3_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2PlacedBudget (RunHopSendPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (R2SendEnv r2EncGhost r2PeerGhost0 run_hop_send_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (R3aRecvWEnv r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost run_hop_recvW_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget
  (run_hop_recvBad_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget
  (RunHopRecvBadPlaced RunHopRecvPPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
  (R3bRecvPEnv run_hop_recvP_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunArmEnvs RunArmsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (dropSpeSpecStkPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced dropSpeX_placed_ok dropSpe_placed_ok path_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv bundleReadSpecPlaced dirGetSpecPlaced readFileSpecPlaced splitIdSpecPlaced
   splitSignedSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)

/-- Non-slot callee allocation-event envelopes on Block `579`, parameterized by `ReadEnv`. -/
def cliRunCalleesEnvs
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop :=
      ReadFileRuleEnv cliIo.rd) : RunCalleesEnvs where
  readFile := ReadEnv
  dirGet := DirGetEnv PathEnv ReadEnv cliIo.rd
  bundleRead := BundleReadEnv cliIo.rd PathEnv ReadEnv
  splitId := SplitIdEnv
  splitSigned := SplitSignedEnv SplitIdEnv

/-- Arm allocation-event envelopes on Block `579` over `cEnvs`, `sEnvs`, `PksmTryFromEnv`, and `S`. -/
def cliRunArmEnvs (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) (S : RunSem) : RunArmEnvs where
  pre := PreEnv cEnvs
  init1 := Init1Env cEnvs
  init2 := Init2Env cEnvs
  init3 := R1cInit3Env sEnvs
  send := R2SendEnv sEnvs S
  recvW := R3aRecvWEnv sEnvs
  pksmTryFrom := PksmTryFromEnv
  recvP := R3bRecvPEnv S sEnvs PksmTryFromEnv

/-- Extern-parametric budget-threaded public/directory callee obligations and `RunArmsPlaced` on Block `579`. -/
structure CliPubCalleesPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (sEnvs : RunSlotEnvs) (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) : Prop where
  readFile : subroutine_ok (lsProg_579 H) (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile
      (cliRunCalleesEnvs ReadEnv).readFile)
  dirGet : ∀ {stk : Nat}, cliRunBudgets.dirGetNeed ≤ stk →
    subroutine_ok (lsProg_579 H) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (cliRunCalleesEnvs ReadEnv).dirGet stk)
  bundleRead : ∀ {stk : Nat}, cliRunBudgets.bundleReadNeed ≤ stk →
    subroutine_ok (lsProg_579 H) (lsmpl.base 563)
      (bundleReadSpecPlaced cliIo.rd cliWrOk A lim (cliRunCalleesEnvs ReadEnv).bundleRead stk)
  splitId : ∀ {stk : Nat}, splitIdNeed ≤ stk →
    subroutine_ok (lsProg_579 H) (lsmpl.base 593)
      (splitIdSpecPlaced A lim (cliRunCalleesEnvs ReadEnv).splitId stk)
  splitSigned : ∀ {stk : Nat}, splitSignedNeed ≤ stk →
    subroutine_ok (lsProg_579 H) (lsmpl.base 592)
      (splitSignedSpecPlaced A lim (cliRunCalleesEnvs ReadEnv).splitSigned stk)
  dropSpeX : subroutine_ok (lsProg_579 H) (blkPl_553).base
    (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim))
  dropSpe : ∀ (stk : Nat), 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_579 H) (blkPl_553).base
      (dropSpeSpecStkPlaced A lim stk)
  arms : ∀ (S : RunSem) (decPkNeed : Nat),
    RunArmsPlaced (LibsignalCodeRoLoaded lsmpl) A lim
      (cliRunCalleesEnvs ReadEnv) sEnvs
      (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv S)
      H cliRunBudgets S (cliRunNeeds decPkNeed) cliResStack

/-- Specialization of `CliPubCalleesPlacedAt` to `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
abbrev CliPubCalleesPlaced [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (sEnvs : RunSlotEnvs) (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) : Prop :=
  CliPubCalleesPlacedAt (cliGhostExterns g (cliExternsPlaced mmpl W)) A lim ReadEnv sEnvs
    PksmTryFromEnv

abbrev CliPubCalleesPlacedLinked [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (sEnvs : RunSlotEnvs) (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) : Prop :=
  CliPubCalleesPlacedAt (cliExternsPlaced mmpl W) A lim ReadEnv sEnvs PksmTryFromEnv

/-- Discharges all non-arm fields of `CliPubCalleesPlacedAt` from `RunHooksPlaced` and `hRead`. -/
theorem cliPubCalleesAt_of_arms_placed [LibsignalPlacement] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok (lsProg_579 H) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (harms : ∀ (S : RunSem) (decPkNeed : Nat),
      RunArmsPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        (cliRunCalleesEnvs ReadEnv) sEnvs
        (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv S)
        H cliRunBudgets S (cliRunNeeds decPkNeed) cliResStack) :
    CliPubCalleesPlacedAt H A lim ReadEnv sEnvs PksmTryFromEnv :=
  { readFile := hRead
    dirGet := fun {_stk} hstk =>
      dirGet_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        (pathProg := lsProg_589 H) (jPath := 589)
        (readProg := lsProg_579 H) (jRead := 579)
        (fun _ hp => hp.2) hh.alloc hh.memcpyRO hh.bcmp
        (by decide) (by decide)
        (path_placed_ok (callerProg := lsProg_589 H) (i := 589)
          hh (Nat.le_refl pathNeed) (by decide))
        (by decide) (by decide)
        (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
        (hh.fs (lsProg_589 H) 589) hstk
        (fun _ _ _ _ h => h) (by decide)
    bundleRead := fun {_stk} hstk =>
      bundleRead_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        (pathProg := lsProg_563 H) (jPath := 563)
        (readProg := lsProg_579 H) (jRead := 579)
        (fun _ hp => hp.2) hh.alloc
        (by decide) (by decide)
        (path_placed_ok (callerProg := lsProg_563 H) (i := 563)
          hh (Nat.le_refl pathNeed) (by decide))
        (by decide) (by decide)
        (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
        (hh.fs (lsProg_563 H) 563) hstk (by decide)
    splitId := fun {_stk} hstk =>
      splitId_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        hh.alloc
        (cliDropSpe_placed_caller_ok_x
          (callerProg := lsProg_593 H) (i := 593) hh.alloc (by decide))
        hstk (by decide)
    splitSigned := fun {_stk} hstk =>
      splitSigned_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        hh.alloc
        (splitId_placed_caller_ok_of_deps
          (callerProg := lsProg_592 H) (i := 592)
          hh.alloc
          (cliDropSpe_placed_caller_ok_x
            (callerProg := lsProg_593 H) (i := 593) hh.alloc (by decide))
          (Nat.le_refl splitIdNeed) (by decide))
        (cliDropSpe_placed_caller_ok_x
          (callerProg := lsProg_592 H) (i := 592) hh.alloc (by decide))
        hstk (by decide)
    dropSpeX := dropSpeX_placed_ok
      (callerProg := lsProg_579 H) (i := 579) hh (by decide)
    dropSpe := fun stk hstk hstk64 =>
      dropSpe_placed_ok
        (callerProg := lsProg_579 H) (i := 579)
        hh stk hstk hstk64 (by decide)
    arms := harms }

theorem cliPubCallees_of_arms_placed [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (harms : ∀ (S : RunSem) (decPkNeed : Nat),
      RunArmsPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        (cliRunCalleesEnvs ReadEnv) sEnvs
        (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv S)
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
        cliResStack) :
    CliPubCalleesPlaced mmpl g W A lim ReadEnv sEnvs PksmTryFromEnv :=
  cliPubCalleesAt_of_arms_placed hh hRead harms

/-- Reduces `RunArmsPlaced` to the `send`, `recvP`, and `recvBad` arm obligations. -/
theorem runArmsPlaced_of_send_recvP_recvBad [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hsend : RunHopSendPlaced (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs sEnvs (R2SendEnv sEnvs S) H B S needs resStack)
    (hrecvP : RunHopRecvPPlaced (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs sEnvs PksmTryFromEnv (R3bRecvPEnv S sEnvs PksmTryFromEnv)
      H B S needs resStack)
    (hrecvBad : RunHopRecvBadPlaced (LibsignalCodeRoLoaded lsmpl)
      A lim sEnvs H B S needs resStack)
    (hinit_addr : ∀ g d2 fsp,
      sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64) := by
      intros; rfl)
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) := by
      intros; rfl) :
    RunArmsPlaced (LibsignalCodeRoLoaded lsmpl) A lim
      cEnvs sEnvs (cliRunArmEnvs cEnvs sEnvs PksmTryFromEnv S) H B S needs resStack :=
  { join := run_hop_join_placed_ok
    pre := run_hop_pre_placed_ok
    init1 := run_hop_init1_placed_ok
    init2 := run_hop_init2_placed_ok
    init3 := run_hop_init3_placed_ok hinit_addr
    send := hsend
    recvW := run_hop_recvW_placed_ok hdec_ghost
    recvP := hrecvP
    recvBad := hrecvBad }

theorem cliPubCalleesAt_placed_of_send_recvP_recvBad [LibsignalPlacement] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok (lsProg_579 H) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hsend : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopSendPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        (cliRunCalleesEnvs ReadEnv) sEnvs (R2SendEnv sEnvs S)
        H cliRunBudgets S (cliRunNeeds decPkNeed) cliResStack)
    (hrecvP : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopRecvPPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv
        (R3bRecvPEnv S sEnvs PksmTryFromEnv)
        H cliRunBudgets S (cliRunNeeds decPkNeed) cliResStack)
    (hrecvBad : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopRecvBadPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        sEnvs H cliRunBudgets S (cliRunNeeds decPkNeed) cliResStack)
    (hinit_addr : ∀ g d2 fsp,
      sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64) := by
      intros; rfl)
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) := by
      intros; rfl) :
    CliPubCalleesPlacedAt H A lim ReadEnv sEnvs PksmTryFromEnv :=
  cliPubCalleesAt_of_arms_placed hh hRead fun S decPkNeed =>
    runArmsPlaced_of_send_recvP_recvBad
      (hsend S decPkNeed) (hrecvP S decPkNeed) (hrecvBad S decPkNeed)
      hinit_addr hdec_ghost

theorem cliPubCallees_placed_of_send_recvP_recvBad [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hsend : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopSendPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        (cliRunCalleesEnvs ReadEnv) sEnvs (R2SendEnv sEnvs S)
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
        cliResStack)
    (hrecvP : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopRecvPPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv
        (R3bRecvPEnv S sEnvs PksmTryFromEnv)
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
        cliResStack)
    (hrecvBad : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopRecvBadPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        sEnvs (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
        cliResStack)
    (hinit_addr : ∀ g d2 fsp,
      sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64) := by
      intros; rfl)
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) := by
      intros; rfl) :
    CliPubCalleesPlaced mmpl g W A lim ReadEnv sEnvs PksmTryFromEnv :=
  cliPubCalleesAt_placed_of_send_recvP_recvBad hh hRead hsend hrecvP hrecvBad hinit_addr hdec_ghost

/-- Assembles all nine budget-threaded arm hop contracts on Block `579` into `RunArmsPlaced`. -/
theorem runArmsPlaced_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
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
    RunArmsPlaced (LibsignalCodeRoLoaded lsmpl) A lim
      cEnvs sEnvs (cliRunArmEnvs cEnvs sEnvs PksmTryFromEnv S) H B S needs resStack :=
  runArmsPlaced_of_send_recvP_recvBad
    (run_hop_send_placed_ok henc_addr)
    (run_hop_recvP_placed_ok hpksm_addr hdp_ghost)
    run_hop_recvBad_placed_ok
    hinit_addr hdec_ghost

/-- Proves `CliPubCalleesPlacedAt` from `RunHooksPlaced` and `hRead`. -/
theorem cliPubCalleesAt_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok (lsProg_579 H) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
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
    CliPubCalleesPlacedAt H A lim ReadEnv sEnvs PksmTryFromEnv :=
  cliPubCalleesAt_of_arms_placed hh hRead fun _ _ =>
    runArmsPlaced_ok hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost

theorem cliPubCallees_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
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
    CliPubCalleesPlaced mmpl g W A lim ReadEnv sEnvs PksmTryFromEnv :=
  cliPubCalleesAt_placed_ok hh hRead hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost


/-! ## `LibsignalFrozen` Aggregators -/

/-- Extern-parametric `LibsignalFrozen` public/directory callee obligations and `RunArmsFrozenPlaced` on Block `579`. -/
structure CliPubCalleesFrozenPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (sEnvs : RunSlotEnvs) (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) : Prop where
  readFile : subroutine_ok (lsProg_579 H) (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile
      (cliRunCalleesEnvs ReadEnv).readFile)
  dirGet : ∀ {stk : Nat}, cliRunBudgets.dirGetNeed ≤ stk →
    subroutine_ok (lsProg_579 H) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (cliRunCalleesEnvs ReadEnv).dirGet stk)
  bundleRead : ∀ {stk : Nat}, cliRunBudgets.bundleReadNeed ≤ stk →
    subroutine_ok (lsProg_579 H) (lsmpl.base 563)
      (bundleReadSpecPlaced cliIo.rd cliWrOk A lim (cliRunCalleesEnvs ReadEnv).bundleRead stk)
  splitId : ∀ {stk : Nat}, splitIdNeed ≤ stk →
    subroutine_ok (lsProg_579 H) (lsmpl.base 593)
      (splitIdSpecPlaced A lim (cliRunCalleesEnvs ReadEnv).splitId stk)
  splitSigned : ∀ {stk : Nat}, splitSignedNeed ≤ stk →
    subroutine_ok (lsProg_579 H) (lsmpl.base 592)
      (splitSignedSpecPlaced A lim (cliRunCalleesEnvs ReadEnv).splitSigned stk)
  dropSpeX : subroutine_ok (lsProg_579 H) (blkPl_553).base
    (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim))
  dropSpe : ∀ (stk : Nat), 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_579 H) (blkPl_553).base
      (dropSpeSpecStkPlaced A lim stk)
  arms : ∀ (S : RunSem) (decPkNeed : Nat),
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget.RunArmsFrozenPlaced
      A lim (cliRunCalleesEnvs ReadEnv) sEnvs
      (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv S)
      H cliRunBudgets S (cliRunNeeds decPkNeed) cliResStack

/-- Specialization of `CliPubCalleesFrozenPlacedAt` to `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
abbrev CliPubCalleesFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (sEnvs : RunSlotEnvs) (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) : Prop :=
  CliPubCalleesFrozenPlacedAt (cliGhostExterns g (cliExternsPlaced mmpl W)) A lim ReadEnv sEnvs
    PksmTryFromEnv

abbrev CliPubCalleesFrozenPlacedLinked [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (sEnvs : RunSlotEnvs) (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) : Prop :=
  CliPubCalleesFrozenPlacedAt (cliExternsPlaced mmpl W) A lim ReadEnv sEnvs PksmTryFromEnv

/-- Discharges all non-arm fields of `CliPubCalleesFrozenPlacedAt` from `RunHooksPlaced` and `hRead`. -/
theorem cliPubCalleesAt_of_arms_frozen_placed [LibsignalPlacement] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok (lsProg_579 H) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (harms : ∀ (S : RunSem) (decPkNeed : Nat),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget.RunArmsFrozenPlaced
        A lim (cliRunCalleesEnvs ReadEnv) sEnvs
        (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv S)
        H cliRunBudgets S (cliRunNeeds decPkNeed) cliResStack) :
    CliPubCalleesFrozenPlacedAt H A lim ReadEnv sEnvs PksmTryFromEnv :=
  { readFile := hRead
    dirGet := fun {_stk} hstk =>
      dirGet_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        (pathProg := lsProg_589 H) (jPath := 589)
        (readProg := lsProg_579 H) (jRead := 579)
        (fun _ hp => hp.2) hh.alloc hh.memcpyRO hh.bcmp
        (by decide) (by decide)
        (path_placed_ok (callerProg := lsProg_589 H) (i := 589)
          hh (Nat.le_refl pathNeed) (by decide))
        (by decide) (by decide)
        (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
        (hh.fs (lsProg_589 H) 589) hstk
        (fun _ _ _ _ h => h) (by decide)
    bundleRead := fun {_stk} hstk =>
      bundleRead_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        (pathProg := lsProg_563 H) (jPath := 563)
        (readProg := lsProg_579 H) (jRead := 579)
        (fun _ hp => hp.2) hh.alloc
        (by decide) (by decide)
        (path_placed_ok (callerProg := lsProg_563 H) (i := 563)
          hh (Nat.le_refl pathNeed) (by decide))
        (by decide) (by decide)
        (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
        (hh.fs (lsProg_563 H) 563) hstk (by decide)
    splitId := fun {_stk} hstk =>
      splitId_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        hh.alloc
        (cliDropSpe_placed_caller_ok_x
          (callerProg := lsProg_593 H) (i := 593) hh.alloc (by decide))
        hstk (by decide)
    splitSigned := fun {_stk} hstk =>
      splitSigned_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        hh.alloc
        (splitId_placed_caller_ok_of_deps
          (callerProg := lsProg_592 H) (i := 592)
          hh.alloc
          (cliDropSpe_placed_caller_ok_x
            (callerProg := lsProg_593 H) (i := 593) hh.alloc (by decide))
          (Nat.le_refl splitIdNeed) (by decide))
        (cliDropSpe_placed_caller_ok_x
          (callerProg := lsProg_592 H) (i := 592) hh.alloc (by decide))
        hstk (by decide)
    dropSpeX := dropSpeX_placed_ok
      (callerProg := lsProg_579 H) (i := 579) hh (by decide)
    dropSpe := fun stk hstk hstk64 =>
      dropSpe_placed_ok
        (callerProg := lsProg_579 H) (i := 579)
        hh stk hstk hstk64 (by decide)
    arms := harms }

theorem cliPubCallees_of_arms_frozen_placed [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (harms : ∀ (S : RunSem) (decPkNeed : Nat),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget.RunArmsFrozenPlaced
        A lim (cliRunCalleesEnvs ReadEnv) sEnvs
        (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv S)
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
        cliResStack) :
    CliPubCalleesFrozenPlaced mmpl g W A lim ReadEnv sEnvs PksmTryFromEnv :=
  cliPubCalleesAt_of_arms_frozen_placed hh hRead harms

/-- Assembles all `LibsignalFrozen` arm hop contracts at `slotsOfSigPkFrozenPlaced` on Block `579`. -/
theorem runArmsFrozenPlaced_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
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
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget.RunArmsFrozenPlaced
      A lim cEnvs sEnvs (cliRunArmEnvs cEnvs sEnvs PksmTryFromEnv S) H B S needs resStack :=
  { join := run_hop_join_placed_ok
    joinRo := run_hop_join_placed_ok
    pre :=
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget.run_hop_pre_of_slots_placed_ok
        (CodeOk := CryptoVerification.LibsignalFrozen lsmpl)
        (slots := LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
          A lim sEnvs S needs)
        (sEnvs := sEnvs) (needs := needs) rfl
    init1 :=
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget.run_hop_init1_of_slots_placed_ok
        (slots := LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
          A lim sEnvs S needs)
        (sEnvs := sEnvs) (needs := needs) rfl
    init2 :=
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget.run_hop_init2_of_slots_placed_ok
        (slots := LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
          A lim sEnvs S needs)
        (sEnvs := sEnvs) (needs := needs) rfl rfl
    init3 :=
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget.run_hop_init3_of_slots_placed_ok
        (slots := LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
          A lim sEnvs S needs)
        (sEnvs := sEnvs) (needs := needs) rfl rfl hinit_addr
    send :=
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget.run_hop_send_of_slots_placed_ok
        (slots := LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
          A lim sEnvs S needs)
        (sEnvs := sEnvs) (needs := needs) rfl rfl henc_addr
    recvW :=
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget.run_hop_recvW_frozen_placed_ok
        hdec_ghost
    recvP :=
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget.run_hop_recvP_frozen_placed_ok
        hpksm_addr hdp_ghost
    recvBad := run_hop_recvBad_placed_ok }

/-- Proves `CliPubCalleesFrozenPlacedAt` from `RunHooksPlaced` and `hRead`. -/
theorem cliPubCalleesAt_frozen_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok (lsProg_579 H) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
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
    CliPubCalleesFrozenPlacedAt H A lim ReadEnv sEnvs PksmTryFromEnv :=
  cliPubCalleesAt_of_arms_frozen_placed hh hRead fun _ _ =>
    runArmsFrozenPlaced_ok hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost

theorem cliPubCallees_frozen_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
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
    CliPubCalleesFrozenPlaced mmpl g W A lim ReadEnv sEnvs PksmTryFromEnv :=
  cliPubCalleesAt_frozen_placed_ok hh hRead hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
