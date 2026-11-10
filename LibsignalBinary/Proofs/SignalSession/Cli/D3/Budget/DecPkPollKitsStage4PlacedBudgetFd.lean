/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `hRead`-Free CLI Poll Stage-P4 Mark/Remove Store Kits from Block-`589` `dirGetSpecPlaced`

Proves `cliPollKpk_markKitPlacedOk_of_dirGet` (`KyberPreKeyMarkKitPlacedOk`) and
`cliPollPk_removeKitPlacedOk_of_dirGet` (`PreKeyRemoveKitPlacedOk`) directly from `RunHooksPlaced`
and block-`589` `dirGetSpecPlaced`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage4PlacedBudgetFd

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded kpkMarkPollOutAt
   ls_subroutine_ok_rocl_of_block preKeyRemovePollOutAt subroutine_ok_rocl_of_withLsCodeRoLoaded
   unitSpePollOutAt withEnvPre withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsDropOffPlaced lsDropOffPlaced_eq)
open CryptoVerification.SignalSession.Cli
  (DirGhost KyberGhost PkPollGhost dirAt keyName kpkMarkBoxAt kpkMarkOf pkBoxAt pkRemoveFutVtSym
   pkRemoveOf pkRemoveOutAt)
open CryptoVerification.SignalSession.Cli.KitInst
  (CliKpkInv CliKpkMarkErr CliPkInv cliKpkGetSide cliKpkMarkErrSpec cliKpkStoreAt cliKpkStoreSpec
   cliKpkStoreSpecPlaced cliKyberPreKeyStoreSpec cliPkStoreAt cliPreKeyStoreSpec
   kpkMarkBoxAt_memRegion pkBoxAt_memRegion pkRemoveOutAt_entails_pollOut_placed)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed
  (lsProg_570 lsProg_575 lsProg_578 lsProg_589 lsProg_597 lsProg_610)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (CliKpkInvFull cliKitStk cliKpkStoreAtFull cliKpkStoreSpecFullPlaced cliPollKpkKitPlaced
   cliPollPkKitPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget
  (KyberPreKeyMarkKitPlacedOk)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget
  (PreKeyRemoveKitPlacedOk)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
  (KyberPreKeyStoreBudgetEnv kitKpkMarkPollSpec kitKpkMarkPollSpecE kitKpkMarkShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (BoxAllocEnv kitPreKeyRemovePollSpec kitPreKeyRemovePollSpecE kitPreKeyRemoveShimSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdFutDrop_rocl_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlacedBudget
  (cliKpkMarkShim_placed_ok cliKpkStoreBudgetEnvPlaced cliKpkStoreSpecPlaced_markPoll_of_env)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliDecimal_placed_ok cliDirPut_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
  (cliPollKpkBudgetEnv cliPollKpkMarkPollEnv cliPollPkBudgetEnv cliPollPkRemovePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced dirGetSpecPlaced pkRemovePollSpecPlaced pkShimSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudget
  (CliKpkMarkPollEnv kpkMarkPoll_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (CliPkRemovePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudget
  (pkRemovePoll_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget
  (pkRemoveShim_placed_ok_of_deps)

private theorem toSkeletonRunHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

private theorem cliPollKpk_markShim_rocl_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B)
    subroutine_ok callerProg (0#64 + kpkKit.markShimOff)
      (withLsRoCl lsmpl (kitKpkMarkShimSpec M A lim kpkKit)) := by
  intro kpkKit
  have h613 := cliKpkMarkShim_placed_ok (rd := cliIo.rd) (F0 := F0) (pathOk := cliWrOk)
    (kid := kpkId) (ksid := spkId) (kbk := kbk)
    (cliKpkGetSide A.repAlloc cliIo.rd F0 cliWrOk kpkId)
    (s1 := (cliKitStk B).kpkGetShim) (s2 := (cliKitStk B).kpkGetPoll)
    (s3 := (cliKitStk B).kpkMarkShim) (s4 := (cliKitStk B).kpkMarkPoll)
    pkBoxAt_memRegion kpkMarkBoxAt_memRegion hh.alloc (by dsimp [cliKitStk]; omega)
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 613)
    h613 hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 613) _
  rw [BitVec.zero_add]
  exact hrocl

private theorem cliPollKpk_markPoll_rocl_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B)
    subroutine_ok callerProg (0#64 + kpkKit.markPollOff)
      (withLsRoCl lsmpl
        (kitKpkMarkPollSpecE M A lim kpkKit
          (cliPollKpkBudgetEnv A.repAlloc F0 kpkId spkId kbk (cliKitStk B) ReadEnv))) := by
  intro kpkKit
  let hhSkel := toSkeletonRunHooks hh
  have hDecimal := cliDecimal_placed_ok hhSkel
  have hPut := cliDirPut_placed_ok hhSkel
  have hhop := kpkMarkPoll_placed_caller_ok_of_deps
    (callerProg := callerProg) (callerBlk := callerBlk)
    (decProg := lsProg_597 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decBlk := 597)
    (getProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (getBlk := 589)
    (putProg := lsProg_570 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (putBlk := 570)
    (stk := (cliKitStk B).kpkMarkPoll)
    hh.alloc hh.panics hh.bcmp hDecimal hGet hPut
    (hh.fs (lsProg_578 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 578)
    (Nat.le_refl _) hblk
  let baseKit := cliKpkStoreSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk kpkId spkId kbk
    (cliKpkGetSide A.repAlloc cliIo.rd F0 cliWrOk kpkId)
    (cliKitStk B).kpkGetShim (cliKitStk B).kpkGetPoll
    (cliKitStk B).kpkMarkShim (cliKitStk B).kpkMarkPoll pkBoxAt_memRegion kpkMarkBoxAt_memRegion
  let baseEnv : KyberPreKeyStoreBudgetEnv baseKit :=
    cliKpkStoreBudgetEnvPlaced (fun _ _ => (· = [])) (cliPollKpkMarkPollEnv ReadEnv F0)
  have hbase := subroutine_ok_rocl_of_withLsCodeRoLoaded
    (cliKpkStoreSpecPlaced_markPoll_of_env
      (cliKpkGetSide A.repAlloc cliIo.rd F0 cliWrOk kpkId)
      (s1 := (cliKitStk B).kpkGetShim) (s2 := (cliKitStk B).kpkGetPoll)
      (s3 := (cliKitStk B).kpkMarkShim) (s4 := (cliKitStk B).kpkMarkPoll)
      pkBoxAt_memRegion kpkMarkBoxAt_memRegion
      (CliKpkMarkPollEnv cliIo.rd DecimalEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) DirPutEnv)
      baseEnv (fun _ _ _ _ _ _ hm => hm) hhop)
  change subroutine_ok callerProg (0#64 + lsmpl.base 578) _
  rw [BitVec.zero_add]
  refine subroutine_ok_map_panic hbase ?_
  rintro ⟨⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0, st⟩ R s0 hpre
  change KyberGhost at st0
  dsimp only [withLsRoCl, kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec, kpkKit,
    cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced,
    CryptoVerification.SignalSession.Cli.KitInst.cliKyberPreKeyStoreSpecPlaced,
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced,
    cliKyberPreKeyStoreSpec, cliKpkStoreSpec, cliKpkStoreAtFull, cliPollKpkBudgetEnv] at hpre
  have hp1 : s0.mem ⊨ ⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
      (kid' = kpkId ∧ ksid' = spkId ∧ kbk' = kbk) ∧
      FitsEnv M lim st (cliPollKpkMarkPollEnv ReadEnv F0 st0 kid' ksid' kbk')⌝ ∗
    (⌜CliKpkInvFull cliIo.rd F0 cliWrOk kpkId spkId kbk st0⌝ ∗
      (⌜s0.fs.files = F0⌝ ∗ kpkMarkBoxAt fut self baseKeyA kid' ksid' 0#8 ∗
        dirAt A.repAlloc self st0.oneTime ∗ dirAt A.repAlloc (self + 0x28#64) st0.lastResort ∗
        memRegion out 48 ∗ (baseKeyA ↦ₛ kbk'.bytes.toList) ∗ A.pool lim st s0 ∗
        stackAt s0.sp (cliKitStk B).kpkMarkPoll ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R)) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hp1
  obtain ⟨⟨hb0, hx0, hx8, ⟨rfl, rfl, rfl⟩, hfit⟩, hp1⟩ := hp1
  rw [satisfies_pure_sepConj] at hp1
  obtain ⟨hinv, hp1⟩ := hp1
  have hpre' : s0.mem ⊨ (withLsRoCl lsmpl (kitKpkMarkPollSpecE M A lim baseKit baseEnv)).pre
      (⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0, st) s0 ∗ R := by
    dsimp only [withLsRoCl, kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec, baseKit, baseEnv,
      cliKpkStoreBudgetEnvPlaced, cliKpkStoreSpecPlaced, cliKpkStoreSpec, cliKpkStoreAt]
    have hp2 : s0.mem ⊨ ⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        (kid' = kid' ∧ ksid' = ksid' ∧ kbk' = kbk') ∧
        FitsEnv M lim st (cliPollKpkMarkPollEnv ReadEnv F0 st0 kid' ksid' kbk')⌝ ∗
      (⌜CliKpkInv cliIo.rd F0 cliWrOk kid' ksid' kbk' st0⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗ kpkMarkBoxAt fut self baseKeyA kid' ksid' 0#8 ∗
          dirAt A.repAlloc self st0.oneTime ∗ dirAt A.repAlloc (self + 0x28#64) st0.lastResort ∗
          memRegion out 48 ∗ (baseKeyA ↦ₛ kbk'.bytes.toList) ∗ A.pool lim st s0 ∗
          stackAt s0.sp (cliKitStk B).kpkMarkPoll ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R)) :=
      (satisfies_pure_sepConj ..).mpr ⟨⟨hb0, hx0, hx8, ⟨rfl, rfl, rfl⟩, hfit⟩,
        (satisfies_pure_sepConj ..).mpr ⟨hinv.markInv, hp1⟩⟩
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hp2
  refine ⟨(⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0, st), R, hpre', ?_,
    fun _ hpan => hpan⟩
  intro sf hpost
  dsimp only [withLsRoCl, kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec, kpkKit, baseKit,
    baseEnv, cliKpkStoreBudgetEnvPlaced, cliPollKpkBudgetEnv, cliPollKpkKitPlaced,
    cliKpkStoreSpecFullPlaced,
    CryptoVerification.SignalSession.Cli.KitInst.cliKyberPreKeyStoreSpecPlaced,
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced,
    cliKpkStoreSpecPlaced, cliKyberPreKeyStoreSpec, cliKpkStoreSpec,
    cliKpkStoreAtFull, cliKpkStoreAt, kpkMarkPollOutAt] at hpost ⊢
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
  let relProp (a : Except CliKpkMarkErr Unit) : Prop :=
    match a with
    | .ok () => (kpkMarkOf cliIo.rd F0 st0 kid' ksid' kbk').1 = .ok
    | .error e => (kpkMarkOf cliIo.rd F0 st0 kid' ksid' kbk').1 = e.ans
  obtain ⟨ans, evs, hm⟩ := hpost
  refine ⟨ans, evs, ?_⟩
  have hm1 : sf.mem ⊨ ⌜CliKpkInv cliIo.rd F0 cliWrOk kid' ksid' kbk'
      (kpkMarkOf cliIo.rd F0 st0 kid' ksid' kbk').2⌝ ∗
    (⌜LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗
      ⌜relProp ans ∧ sf.trace = s0.trace ++ [] ∧
        cliPollKpkMarkPollEnv ReadEnv F0 st0 kid' ksid' kbk' evs⌝ ∗
      kpkMarkBoxAt fut self baseKeyA kid' ksid' 1#8 ∗
      dirAt A.repAlloc self (kpkMarkOf cliIo.rd F0 st0 kid' ksid' kbk').2.oneTime ∗
      dirAt A.repAlloc (self + 0x28#64) (kpkMarkOf cliIo.rd F0 st0 kid' ksid' kbk').2.lastResort ∗
      unitSpePollOutAt (cliKpkMarkErrSpec A.repAlloc) out ans ∗
      (baseKeyA ↦ₛ kbk'.bytes.toList) ∗ A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp (cliKitStk B).kpkMarkPoll ∗ R) :=
    Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [relProp]; sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  exact Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [relProp]; sep_ac_rfl))
    ((satisfies_pure_sepConj ..).mpr ⟨hinv.mark, hm1.2⟩)

/-- Discharges `KyberPreKeyMarkKitPlacedOk` for `cliPollKpkKitPlaced` from `RunHooksPlaced` and block-`589` `dirGetSpecPlaced`. -/
theorem cliPollKpk_markKitPlacedOk_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed)) :
    KyberPreKeyMarkKitPlacedOk A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
      (cliPollKpkBudgetEnv A.repAlloc F0 kpkId spkId kbk (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  markShim hblk := cliPollKpk_markShim_rocl_of_hooks mmpl gh W B F0 kpkId spkId kbk hh hblk
  markPoll hblk := cliPollKpk_markPoll_rocl_of_dirGet mmpl gh W B F0 kpkId spkId kbk hh hGet hblk
  markFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_rocl_placed_ok hblk

private theorem cliPollPk_removeShim_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_610 H) (lsmpl.base 610)
      (withLsCodeRoLoaded lsmpl
        (kitPreKeyRemoveShimSpec M A lim
          (cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)))) := by
  let pkKit := cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)
  have hshim := pkRemoveShim_placed_ok_of_deps (stk := (cliKitStk B).pkRemoveShim)
    hC (by dsimp [cliKitStk]; omega)
  refine subroutine_ok.of_codeLoaded fun ⟨⟨self, id⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = self ∧ s0.readReg32 .x1 = id ∧
        FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗
      A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).pkRemoveShim) ∗ R at hpre1
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨_, hx0, hx1, hfit⟩, hmem⟩ := hpre1
  have hpre_shim : s0.mem ⊨
      (pkShimSpecPlaced pkRemoveFutVtSym A lim (cliKitStk B).pkRemoveShim).pre
        (⟨self, id⟩, st) s0 ∗ R := by
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hfit⟩, hmem⟩
  refine subroutine_ok.mono_outcome hshim (⟨self, id⟩, st) R s0 hpc hrun hpre_shim hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, kitPreKeyRemoveShimSpec, pkKit, cliPollPkKitPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
      cliPreKeyStoreSpec]
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded] at hpost
    simpa only [BitVec.zero_add] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem cliPollPk_removeShim_rocl_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + pkKit.removeShimOff)
      (withLsRoCl lsmpl (kitPreKeyRemoveShimSpec M A lim pkKit)) := by
  intro pkKit
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 610)
    (cliPollPk_removeShim_placed_ok_of_hooks B F0 pkId hh.alloc) hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 610) _
  rw [BitVec.zero_add]
  exact hrocl

private theorem cliPollPk_removePoll_rocl_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + pkKit.removePollOff)
      (withLsRoCl lsmpl
        (kitPreKeyRemovePollSpecE M A lim pkKit
          (cliPollPkBudgetEnv A.repAlloc F0 pkId (cliKitStk B) ReadEnv))) := by
  intro pkKit
  let pkEnv := cliPollPkBudgetEnv A.repAlloc F0 pkId (cliKitStk B) ReadEnv
  let hhSkel := toSkeletonRunHooks hh
  have hDecimal := cliDecimal_placed_ok hhSkel
  have hPut := cliDirPut_placed_ok hhSkel
  have hhop := pkRemovePoll_placed_caller_ok_of_deps
    (callerProg := callerProg) (callerBlk := callerBlk)
    (decProg := lsProg_597 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decBlk := 597)
    (getProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (getBlk := 589)
    (putProg := lsProg_570 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (putBlk := 570)
    (stk := (cliKitStk B).pkRemovePoll)
    hh.alloc hDecimal hGet hPut
    (hh.fs (lsProg_575 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 575)
    (Nat.le_refl _) hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 575) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨fut, out, self, id⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  change DirGhost at st0
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0⌝ ∗
      ((kitPreKeyRemovePollSpec M A lim pkKit pkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0 ∗ R) := by
    change s0.mem ⊨ (⌜s0.fs.files = F0⌝ ∗
      (kitPreKeyRemovePollSpec M A lim pkKit pkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0) ∗ R at hpre1
    simpa only [sepConj_assoc] using hpre1
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨hfiles, hpre3⟩ := hpre2
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        id = pkId ∧ FitsEnv M lim st (cliPollPkRemovePollEnv ReadEnv F0 st0 id)⌝ ∗
      pkBoxAt fut self id 0#8 ∗
      (⌜CliPkInv cliIo.rd F0 cliWrOk pkId st0⌝ ∗ dirAt A.repAlloc self st0) ∗
      memRegion out 48 ∗ A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).pkRemovePoll) ∗ R at hpre3
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
  obtain ⟨⟨_, hx0, hx8, rfl, hfit_kit⟩, hpre4⟩ := hpre3
  have hpre5 : s0.mem ⊨ ⌜CliPkInv cliIo.rd F0 cliWrOk id st0⌝ ∗
      (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0 ∗ memRegion out 48 ∗
        A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).pkRemovePoll ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre4
  rw [satisfies_pure_sepConj] at hpre5
  obtain ⟨hinv, hspatial⟩ := hpre5
  let xg : PkPollGhost := ⟨fut, out, self, id, st0⟩
  let RemEnv := CliPkRemovePollEnv cliIo.rd DecimalEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) DirPutEnv
  have hfit_hop : FitsEnv M lim st (RemEnv s0.fs.files xg) := fun evs hm => by
    rw [hfiles] at hm
    exact hfit_kit evs hm
  have hpre_hop : s0.mem ⊨
      (pkRemovePollSpecPlaced cliIo.rd cliWrOk A lim RemEnv (cliKitStk B).pkRemovePoll).pre
        (xg, st) s0 ∗ R := by
    dsimp only [pkRemovePollSpecPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hinv.nameOk, hinv.oneLt.1, hfit_hop⟩, ?_⟩
    simpa only [sepConj_assoc] using hspatial
  refine subroutine_ok.mono_outcome hhop (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left ?_) hpost⟩
    show (pkRemovePollSpecPlaced cliIo.rd cliWrOk A lim RemEnv (cliKitStk B).pkRemovePoll).post
        (xg, st) s0 sf ⊢
      (kitPreKeyRemovePollSpec M A lim pkKit pkEnv).post (⟨fut, out, self, id⟩, st0, st) s0 sf
    dsimp only [pkRemovePollSpecPlaced, kitPreKeyRemovePollSpec, pkKit, pkEnv, cliPollPkBudgetEnv,
      cliPollPkKitPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
      cliPreKeyStoreSpec, cliPkStoreAt, xg]
    refine Entails.sepExists_elim fun evs => ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun res => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hres, htr, hmenv⟩ => ?_
    rw [hfiles] at hres hmenv
    subst hres
    set m := pkRemoveOf st0 (keyName id) (st0.get cliIo.rd F0 (keyName id))
    have hent0 := pkRemoveOutAt_entails_pollOut_placed A.repAlloc cliIo.rd F0 cliWrOk id
      (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
      (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll st0 id out
    dsimp only at hent0
    have hout_eq : preKeyRemovePollOutAt
        (CryptoVerification.SignalSession.Cli.KitInst.cliPreKeyStoreSpecPlaced
          A.repAlloc cliIo.rd F0 cliWrOk id
          (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
          (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll) out =
      preKeyRemovePollOutAt pkKit out := by
      funext ans
      cases ans <;> rfl
    rw [hout_eq] at hent0
    refine Entails.trans (Entails.of_eq (show _ = pkRemoveOutAt A.repAlloc out m.1 ∗
      (dirAt A.repAlloc self m.2 ∗ pkBoxAt fut self id 1#8 ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (cliKitStk B).pkRemovePoll) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hent0) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ans => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hrel, heq2⟩ => ?_
    rw [heq2]
    refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
    refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hmenv⟩ ?_
    exact Entails.trans (Entails.pure_right hinv.removePreKey (Entails.refl _))
      (Entails.of_eq (by sep_ac_rfl))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- Discharges `PreKeyRemoveKitPlacedOk` for `cliPollPkKitPlaced` from `RunHooksPlaced` and block-`589` `dirGetSpecPlaced`. -/
theorem cliPollPk_removeKitPlacedOk_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed)) :
    PreKeyRemoveKitPlacedOk A lim
      (cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B))
      (cliPollPkBudgetEnv A.repAlloc F0 pkId (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  removeShim hblk := cliPollPk_removeShim_rocl_of_hooks mmpl gh W B F0 pkId hh hblk
  removePoll hblk := cliPollPk_removePoll_rocl_of_dirGet mmpl gh W B F0 pkId hh hGet hblk
  removeFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_rocl_placed_ok hblk

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage4PlacedBudgetFd
