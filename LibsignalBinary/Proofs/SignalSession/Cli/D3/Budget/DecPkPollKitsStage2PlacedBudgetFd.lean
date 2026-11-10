/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CliCBudget
import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsSelfPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage4PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `hRead`-Free 6-Kit CLI `decrypt_prekey` Poll Bundle from Block-`589` `dirGetSpecPlaced`

Proves `cliPollSpk_kitPlacedOk_of_dirGet`, `cliPollPk_kitPlacedOk_of_dirGet`,
`cliPollKpk_kitPlacedOk_of_dirGet`, and `cliDecPkPollKitsPlacedOk_of_dirGet` directly from
`RunHooksPlaced`, block-`589` `dirGetSpecPlaced`, and block-`46` `sessDeserializeSpecPlaced`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage2PlacedBudgetFd

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded kpkGetPollOutAt
   ls_subroutine_ok_rocl_of_block preKeyGetPollOutAt spkGetPollOutAt
   subroutine_ok_rocl_of_withLsCodeRoLoaded withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.RecordCodecs.Placed (lsProg_65 lsProg_595)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsDropOffPlaced lsDropOffPlaced_eq)
open CryptoVerification.SignalSession.Cli
  (DirGhost KpkPollGhost KyberGhost PkPollGhost dirAt keyName kpkGetFutVtSym pkBoxAt pkGetFutVtSym
   spkGetFutVtSym)
open CryptoVerification.SignalSession.Cli.KitInst
  (CliKpkInv CliPkInv CliSpkInv cliKpkStoreSpec cliKyberPreKeyStoreSpec cliPkStoreAt
   cliPreKeyStoreSpec cliSignedPreKeyStoreSpec cliSpkStoreAt kpkAnsAt_entails_pollOut_placed
   pkGetAnsAt_entails_pollOut_placed spkAnsAt_entails_pollOut_placed)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed
  (lsProg_553 lsProg_571 lsProg_573 lsProg_576 lsProg_589 lsProg_597 lsProg_606 lsProg_608
   lsProg_611)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (CliKpkInvFull cliKitStk cliKpkStoreAtFull cliKpkStoreSpecFullPlaced cliPollKpkKitPlaced
   cliPollPkKitPlaced cliPollSpkKitPlaced dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.CliCBudget
  (signedHooksPlaced_of_codecHooks signedPortDepsPlaced_ok)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
  (kitKpkGetPollSpec kitKpkGetPollSpecE kitKpkGetShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (KyberPreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOk SignedPreKeyStoreKitPlacedOk)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (BoxAllocEnv kitPreKeyGetPollSpec kitPreKeyGetPollSpecE kitPreKeyGetShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
  (kitSpkGetPollSpec kitSpkGetPollSpecE kitSpkGetShimSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget
  (CliDecPkPollKitsPlacedOk)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd
  (cliPollId_kitPlacedOkI_untrusted_of_dirGet cliPollSess_kitPlacedOkSE_untrusted_of_dirGet)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsSelfPlacedBudgetFd
  (cliPollSelf_kitPlacedOk_of_dirGet)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage4PlacedBudgetFd
  (cliPollKpk_markKitPlacedOk_of_dirGet cliPollPk_removeKitPlacedOk_of_dirGet)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdFutDrop_rocl_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliDecimal_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecsPlacedBudget
  (cliDecodeKyberPreKey_placed_ok cliDecodeSignedPreKey_placed_ok cliPreKeyDeserialize_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
  (CliPkDecodeEnv CliSpkDecodeEnv cliPollKpkFullBudgetEnv cliPollKpkGetPollEnv
   cliPollPkFullBudgetEnv cliPollPkGetPollEnv cliPollSpkFullBudgetEnv cliPollSpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced dirGetSpecPlaced kpkGetPollSpecPlaced pkGetPollSpecOfPlaced
   pkGetPollSpecPlaced pkShimSpecPlaced sessDeserializeSpecPlaced spkGetPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlacedBudget
  (dropSpeWord_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget (CliKpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlacedBudget
  (kpkGetPoll_placed_fs_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (CliPkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlacedBudget
  (pkGetPoll_placed_fs_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget
  (kpkGetShim_placed_ok_of_deps pkGetShim_placed_ok_of_deps spkGetShim_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (CliSpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudget
  (spkGetPoll_placed_fs_caller_ok_of_deps)

private theorem toSkeletonRunHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

/-! ## 1. Shims (`606`, `608`, `611`) -/

private theorem cliPollSpk_getShim_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (B : RunBudgets) (F0 : FsFiles) (spkId : BitVec 32)
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_606 H) (lsmpl.base 606)
      (withLsCodeRoLoaded lsmpl
        (kitSpkGetShimSpec M A lim
          (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B)))) := by
  let spkKit := cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B)
  have hshim := spkGetShim_placed_ok_of_deps (stk := (cliKitStk B).spkGetShim)
    hC (by dsimp [cliKitStk]; omega)
  refine subroutine_ok.of_codeLoaded fun ⟨⟨self, id⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = self ∧ s0.readReg32 .x1 = id ∧
        FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗
      A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).spkGetShim) ∗ R at hpre1
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨_, hx0, hx1, hfit⟩, hmem⟩ := hpre1
  have hpre_shim : s0.mem ⊨
      (pkShimSpecPlaced spkGetFutVtSym A lim (cliKitStk B).spkGetShim).pre
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
    dsimp only [withLsCodeRoLoaded, kitSpkGetShimSpec, spkKit, cliPollSpkKitPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliSignedPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpec]
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded] at hpost
    simpa only [BitVec.zero_add] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem cliPollSpk_getShim_rocl_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (spkId : BitVec 32)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let spkKit := cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + spkKit.getShimOff)
      (withLsRoCl lsmpl (kitSpkGetShimSpec M A lim spkKit)) := by
  intro spkKit
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 606)
    (cliPollSpk_getShim_placed_ok_of_hooks B F0 spkId hh.alloc) hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 606) _
  rw [BitVec.zero_add]
  exact hrocl

private theorem cliPollPk_getShim_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_608 H) (lsmpl.base 608)
      (withLsCodeRoLoaded lsmpl
        (kitPreKeyGetShimSpec M A lim
          (cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)))) := by
  let pkKit := cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)
  have hshim := pkGetShim_placed_ok_of_deps (stk := (cliKitStk B).pkGetShim)
    hC (by dsimp [cliKitStk]; omega)
  refine subroutine_ok.of_codeLoaded fun ⟨⟨self, id⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = self ∧ s0.readReg32 .x1 = id ∧
        FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗
      A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).pkGetShim) ∗ R at hpre1
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨_, hx0, hx1, hfit⟩, hmem⟩ := hpre1
  have hpre_shim : s0.mem ⊨
      (pkShimSpecPlaced pkGetFutVtSym A lim (cliKitStk B).pkGetShim).pre
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
    dsimp only [withLsCodeRoLoaded, kitPreKeyGetShimSpec, pkKit, cliPollPkKitPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
      cliPreKeyStoreSpec]
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded] at hpost
    simpa only [BitVec.zero_add] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem cliPollPk_getShim_rocl_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + pkKit.getShimOff)
      (withLsRoCl lsmpl (kitPreKeyGetShimSpec M A lim pkKit)) := by
  intro pkKit
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 608)
    (cliPollPk_getShim_placed_ok_of_hooks B F0 pkId hh.alloc) hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 608) _
  rw [BitVec.zero_add]
  exact hrocl

private theorem cliPollKpk_getShim_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_611 H) (lsmpl.base 611)
      (withLsCodeRoLoaded lsmpl
        (kitKpkGetShimSpec M A lim
          (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B)))) := by
  let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B)
  have hshim := kpkGetShim_placed_ok_of_deps (stk := (cliKitStk B).kpkGetShim)
    hC (by dsimp [cliKitStk]; omega)
  refine subroutine_ok.of_codeLoaded fun ⟨⟨self, id⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = self ∧ s0.readReg32 .x1 = id ∧
        FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗
      A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).kpkGetShim) ∗ R at hpre1
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨_, hx0, hx1, hfit⟩, hmem⟩ := hpre1
  have hpre_shim : s0.mem ⊨
      (pkShimSpecPlaced kpkGetFutVtSym A lim (cliKitStk B).kpkGetShim).pre
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
    dsimp only [withLsCodeRoLoaded, kitKpkGetShimSpec, kpkKit, cliPollKpkKitPlaced,
      cliKpkStoreSpecFullPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliKyberPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced,
      cliKyberPreKeyStoreSpec, cliKpkStoreSpec]
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded] at hpost
    simpa only [BitVec.zero_add] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem cliPollKpk_getShim_rocl_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B)
    subroutine_ok callerProg (0#64 + kpkKit.getShimOff)
      (withLsRoCl lsmpl (kitKpkGetShimSpec M A lim kpkKit)) := by
  intro kpkKit
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 611)
    (cliPollKpk_getShim_placed_ok_of_hooks B F0 kpkId spkId kbk hh.alloc) hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 611) _
  rw [BitVec.zero_add]
  exact hrocl

/-! ## 2. Poll Closures (`571`, `573`, `576`) & Store-Kit Bundles -/

private theorem cliPollSpk_getPoll_rocl_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (spkId : BitVec 32)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let spkKit := cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + spkKit.getPollOff)
      (withLsRoCl lsmpl
        (kitSpkGetPollSpecE M A lim spkKit
          (cliPollSpkFullBudgetEnv A.repAlloc F0 spkId (cliKitStk B) ReadEnv))) := by
  intro spkKit
  let spkEnv := cliPollSpkFullBudgetEnv A.repAlloc F0 spkId (cliKitStk B) ReadEnv
  let hhSkel := toSkeletonRunHooks hh
  have hDecimal := cliDecimal_placed_ok hhSkel
  have hSpkDec := cliDecodeSignedPreKey_placed_ok A lim mmpl gh W
    (signedHooksPlaced_of_codecHooks hh.codecHooks) (signedPortDepsPlaced_ok hh.codecHooks)
  have hhop := spkGetPoll_placed_fs_caller_ok_of_deps
    (callerProg := callerProg) (i := callerBlk)
    (decProg := lsProg_597 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decBlk := 597)
    (getProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (getBlk := 589)
    (spkDecProg := lsProg_595 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (spkDecBlk := 595)
    (dropProg := lsProg_553 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (dropBlk := 553)
    (stk := (cliKitStk B).spkGetPoll)
    hh.alloc hDecimal hGet hSpkDec (dropSpeWord_placed_ok hh.alloc)
    (hh.fs (lsProg_571 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 571)
    (Nat.le_refl _) (fun _ _ => Or.inl) (fun _ _ => Or.inr) hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 571) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨fut, out, self, id⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  change DirGhost at st0
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0⌝ ∗
      ((kitSpkGetPollSpec M A lim spkKit spkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0 ∗ R) := by
    change s0.mem ⊨ (⌜s0.fs.files = F0⌝ ∗
      (kitSpkGetPollSpec M A lim spkKit spkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0) ∗ R at hpre1
    simpa only [sepConj_assoc] using hpre1
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨hfiles, hpre3⟩ := hpre2
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        id = spkId ∧ FitsEnv M lim st (cliPollSpkGetPollEnv ReadEnv F0 st0 id)⌝ ∗
      pkBoxAt fut self id 0#8 ∗
      (⌜CliSpkInv cliIo.rd F0 cliWrOk spkId st0⌝ ∗ dirAt A.repAlloc self st0) ∗
      memRegion out 88 ∗ A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).spkGetPoll) ∗ R at hpre3
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
  obtain ⟨⟨_, hx0, hx8, rfl, hfit_kit⟩, hpre4⟩ := hpre3
  have hpre5 : s0.mem ⊨ ⌜CliSpkInv cliIo.rd F0 cliWrOk id st0⌝ ∗
      (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0 ∗ memRegion out 88 ∗
        A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).spkGetPoll ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre4
  rw [satisfies_pure_sepConj] at hpre5
  obtain ⟨hinv, hspatial⟩ := hpre5
  let xg : PkPollGhost := ⟨fut, out, self, id, st0⟩
  let PollEnv := fun F (x : PkPollGhost) =>
    CliSpkGetPollEnv DecimalEnv (fun dir k => DirGetEnv PathEnv ReadEnv cliIo.rd F dir (keyName k))
      CliSpkDecodeEnv cliIo.rd F x
  have hfit_hop : FitsEnv M lim st (PollEnv s0.fs.files xg) := fun evs hm => by
    rw [hfiles] at hm
    exact hfit_kit evs hm
  have hpre_hop : s0.mem ⊨
      (spkGetPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (cliKitStk B).spkGetPoll).pre
        (xg, st) s0 ∗ R := by
    dsimp only [spkGetPollSpecPlaced, pkGetPollSpecOfPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hinv.nameOk, hfiles ▸ hinv.sizeOk, hfit_hop⟩, ?_⟩
    simpa only [sepConj_assoc] using hspatial
  refine subroutine_ok.mono_outcome hhop (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left ?_) hpost⟩
    show (spkGetPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (cliKitStk B).spkGetPoll).post
        (xg, st) s0 sf ⊢
      (kitSpkGetPollSpec M A lim spkKit spkEnv).post (⟨fut, out, self, id⟩, st0, st) s0 sf
    dsimp only [spkGetPollSpecPlaced, pkGetPollSpecOfPlaced, kitSpkGetPollSpec, spkKit, spkEnv,
      cliPollSpkFullBudgetEnv, cliPollSpkKitPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliSignedPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpec, cliSpkStoreAt, xg]
    refine Entails.sepExists_elim fun evs => ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun pa => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hpa, htr, hmenv⟩ => ?_
    rw [hfiles] at hpa hmenv
    subst hpa
    have hent0 := spkAnsAt_entails_pollOut_placed A.repAlloc cliIo.rd F0 cliWrOk id
      (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll st0 id out
    dsimp only at hent0
    have hout_eq : spkGetPollOutAt
        (CryptoVerification.SignalSession.Cli.KitInst.cliSignedPreKeyStoreSpecPlaced
          A.repAlloc cliIo.rd F0 cliWrOk id
          (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll) out =
      spkGetPollOutAt spkKit out := by
      funext ans; cases ans <;> rfl
    rw [hout_eq] at hent0
    refine Entails.trans (sepConj_mono_left hent0) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ans => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hrel => ?_
    refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
    refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hmenv⟩ ?_
    dsimp only [spkKit, cliPollSpkKitPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliSignedPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpec, cliSpkStoreAt]
    exact Entails.trans (Entails.pure_right hinv (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- Discharges `SignedPreKeyStoreKitPlacedOk` from `RunHooksPlaced` and block-`589` `dirGetSpecPlaced`. -/
theorem cliPollSpk_kitPlacedOk_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (spkId : BitVec 32)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed)) :
    SignedPreKeyStoreKitPlacedOk A lim
      (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
      (cliPollSpkFullBudgetEnv A.repAlloc F0 spkId (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  getShim hblk := cliPollSpk_getShim_rocl_of_hooks mmpl gh W B F0 spkId hh hblk
  getPoll hblk := cliPollSpk_getPoll_rocl_of_dirGet mmpl gh W B F0 spkId hh hGet hblk
  getFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_rocl_placed_ok hblk

private theorem cliPollPk_getPoll_rocl_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
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
    subroutine_ok callerProg (0#64 + pkKit.getPollOff)
      (withLsRoCl lsmpl
        (kitPreKeyGetPollSpecE M A lim pkKit
          (cliPollPkFullBudgetEnv A.repAlloc F0 pkId (cliKitStk B) ReadEnv))) := by
  intro pkKit
  let pkEnv := cliPollPkFullBudgetEnv A.repAlloc F0 pkId (cliKitStk B) ReadEnv
  let hhSkel := toSkeletonRunHooks hh
  have hDecimal := cliDecimal_placed_ok hhSkel
  have hPkDec := cliPreKeyDeserialize_placed_ok A lim mmpl gh W hhSkel
  have hhop := pkGetPoll_placed_fs_caller_ok_of_deps
    (callerProg := callerProg) (i := callerBlk)
    (decProg := lsProg_597 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decBlk := 597)
    (getProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (getBlk := 589)
    (pkDecProg := lsProg_65 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (pkDecBlk := 65)
    (dropProg := lsProg_553 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (dropBlk := 553)
    (stk := (cliKitStk B).pkGetPoll)
    hh.alloc hDecimal hGet hPkDec (dropSpeWord_placed_ok hh.alloc)
    (hh.fs (lsProg_573 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 573)
    (Nat.le_refl _) (fun _ _ => Or.inl) (fun _ _ => Or.inr) hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 573) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨fut, out, self, id⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  change DirGhost at st0
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0⌝ ∗
      ((kitPreKeyGetPollSpec M A lim pkKit pkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0 ∗ R) := by
    change s0.mem ⊨ (⌜s0.fs.files = F0⌝ ∗
      (kitPreKeyGetPollSpec M A lim pkKit pkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0) ∗ R at hpre1
    simpa only [sepConj_assoc] using hpre1
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨hfiles, hpre3⟩ := hpre2
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        id = pkId ∧ FitsEnv M lim st (cliPollPkGetPollEnv ReadEnv F0 st0 id)⌝ ∗
      pkBoxAt fut self id 0#8 ∗
      (⌜CliPkInv cliIo.rd F0 cliWrOk pkId st0⌝ ∗ dirAt A.repAlloc self st0) ∗
      memRegion out 56 ∗ A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).pkGetPoll) ∗ R at hpre3
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
  obtain ⟨⟨_, hx0, hx8, rfl, hfit_kit⟩, hpre4⟩ := hpre3
  have hpre5 : s0.mem ⊨ ⌜CliPkInv cliIo.rd F0 cliWrOk id st0⌝ ∗
      (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0 ∗ memRegion out 56 ∗
        A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).pkGetPoll ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre4
  rw [satisfies_pure_sepConj] at hpre5
  obtain ⟨hinv, hspatial⟩ := hpre5
  let xg : PkPollGhost := ⟨fut, out, self, id, st0⟩
  let PollEnv := fun F (x : PkPollGhost) =>
    CliPkGetPollEnv DecimalEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F)
      CliPkDecodeEnv cliIo.rd F x
  have hfit_hop : FitsEnv M lim st (PollEnv s0.fs.files xg) := fun evs hm => by
    rw [hfiles] at hm
    exact hfit_kit evs hm
  have hpre_hop : s0.mem ⊨
      (pkGetPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (cliKitStk B).pkGetPoll).pre
        (xg, st) s0 ∗ R := by
    dsimp only [pkGetPollSpecPlaced, pkGetPollSpecOfPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hinv.nameOk, hfiles ▸ hinv.sizeOk, hfit_hop⟩, ?_⟩
    simpa only [sepConj_assoc] using hspatial
  refine subroutine_ok.mono_outcome hhop (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left ?_) hpost⟩
    show (pkGetPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (cliKitStk B).pkGetPoll).post
        (xg, st) s0 sf ⊢
      (kitPreKeyGetPollSpec M A lim pkKit pkEnv).post (⟨fut, out, self, id⟩, st0, st) s0 sf
    dsimp only [pkGetPollSpecPlaced, pkGetPollSpecOfPlaced, kitPreKeyGetPollSpec, pkKit, pkEnv,
      cliPollPkFullBudgetEnv, cliPollPkKitPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
      cliPreKeyStoreSpec, cliPkStoreAt, xg]
    refine Entails.sepExists_elim fun evs => ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun pa => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hpa, htr, hmenv⟩ => ?_
    rw [hfiles] at hpa hmenv
    subst hpa
    have hent0 := pkGetAnsAt_entails_pollOut_placed A.repAlloc cliIo.rd F0 cliWrOk id
      (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
      (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll st0 id out
    dsimp only at hent0
    have hout_eq : preKeyGetPollOutAt
        (CryptoVerification.SignalSession.Cli.KitInst.cliPreKeyStoreSpecPlaced
          A.repAlloc cliIo.rd F0 cliWrOk id
          (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
          (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll) out =
      preKeyGetPollOutAt pkKit out := by
      funext ans; cases ans <;> rfl
    rw [hout_eq] at hent0
    refine Entails.trans (sepConj_mono_left hent0) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ans => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hrel => ?_
    refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
    refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hmenv⟩ ?_
    dsimp only [pkKit, cliPollPkKitPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
      cliPreKeyStoreSpec, cliPkStoreAt]
    exact Entails.trans (Entails.pure_right hinv (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- Discharges `PreKeyStoreKitPlacedOk` from `RunHooksPlaced` and block-`589` `dirGetSpecPlaced`. -/
theorem cliPollPk_kitPlacedOk_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed)) :
    PreKeyStoreKitPlacedOk A lim
      (cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc F0 pkId (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  getShim hblk := cliPollPk_getShim_rocl_of_hooks mmpl gh W B F0 pkId hh hblk
  getPoll hblk := cliPollPk_getPoll_rocl_of_dirGet mmpl gh W B F0 pkId hh hGet hblk
  getFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_rocl_placed_ok hblk
  removeShim hblk :=
    (cliPollPk_removeKitPlacedOk_of_dirGet mmpl gh W B F0 pkId hDropNz hh hGet).removeShim hblk
  removePoll hblk :=
    (cliPollPk_removeKitPlacedOk_of_dirGet mmpl gh W B F0 pkId hDropNz hh hGet).removePoll hblk
  removeFutDrop hblk :=
    (cliPollPk_removeKitPlacedOk_of_dirGet mmpl gh W B F0 pkId hDropNz hh hGet).removeFutDrop hblk

private theorem cliPollKpk_getPoll_rocl_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
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
    subroutine_ok callerProg (0#64 + kpkKit.getPollOff)
      (withLsRoCl lsmpl
        (kitKpkGetPollSpecE M A lim kpkKit
          (cliPollKpkFullBudgetEnv A.repAlloc F0 kpkId spkId kbk (cliKitStk B) ReadEnv))) := by
  intro kpkKit
  let kpkEnv := cliPollKpkFullBudgetEnv A.repAlloc F0 kpkId spkId kbk (cliKitStk B) ReadEnv
  let hhSkel := toSkeletonRunHooks hh
  have hDecimal := cliDecimal_placed_ok hhSkel
  have hKpkDec := cliDecodeKyberPreKey_placed_ok A lim mmpl gh W
    (signedHooksPlaced_of_codecHooks hh.codecHooks) (signedPortDepsPlaced_ok hh.codecHooks)
  have hhop := kpkGetPoll_placed_fs_caller_ok_of_deps
    (callerProg := callerProg) (i := callerBlk)
    (decProg := lsProg_597 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decBlk := 597)
    (getProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (getBlk := 589)
    (decodeProg := lsProg_595 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decodeBlk := 595)
    (stk := (cliKitStk B).kpkGetPoll)
    hh.alloc hDecimal hGet hKpkDec
    (hh.fs (lsProg_576 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 576)
    (Nat.le_refl _) (fun _ _ => Or.inl) (fun _ _ => Or.inr) hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 576) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨fut, out, self, id⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  change KyberGhost at st0
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0⌝ ∗
      ((kitKpkGetPollSpec M A lim kpkKit kpkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0 ∗ R) := by
    change s0.mem ⊨ (⌜s0.fs.files = F0⌝ ∗
      (kitKpkGetPollSpec M A lim kpkKit kpkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0) ∗ R at hpre1
    simpa only [sepConj_assoc] using hpre1
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨hfiles, hpre3⟩ := hpre2
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        id = kpkId ∧ FitsEnv M lim st (cliPollKpkGetPollEnv ReadEnv F0 st0 id)⌝ ∗
      pkBoxAt fut self id 0#8 ∗
      (⌜CliKpkInvFull cliIo.rd F0 cliWrOk kpkId spkId kbk st0⌝ ∗
        (dirAt A.repAlloc self st0.oneTime ∗ dirAt A.repAlloc (self + 0x28#64) st0.lastResort)) ∗
      memRegion out 88 ∗ A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).kpkGetPoll) ∗ R at hpre3
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
  obtain ⟨⟨_, hx0, hx8, rfl, hfit_kit⟩, hpre4⟩ := hpre3
  have hpre5 : s0.mem ⊨ ⌜CliKpkInvFull cliIo.rd F0 cliWrOk id spkId kbk st0⌝ ∗
      (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0.oneTime ∗
        dirAt A.repAlloc (self + 0x28#64) st0.lastResort ∗ memRegion out 88 ∗
        A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).kpkGetPoll ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre4
  rw [satisfies_pure_sepConj] at hpre5
  obtain ⟨hinv, hspatial⟩ := hpre5
  let xg : KpkPollGhost := ⟨fut, out, self, id, st0⟩
  let PollEnv := fun F (x : KpkPollGhost) =>
    CliKpkGetPollEnv DecimalEnv (fun dir k => DirGetEnv PathEnv ReadEnv cliIo.rd F dir (keyName k))
      CliSpkDecodeEnv cliIo.rd F x
  have hfit_hop : FitsEnv M lim st (PollEnv s0.fs.files xg) := fun evs hm => by
    rw [hfiles] at hm
    exact hfit_kit evs hm
  have hpre_hop : s0.mem ⊨
      (kpkGetPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (cliKitStk B).kpkGetPoll).pre
        (xg, st) s0 ∗ R := by
    dsimp only [kpkGetPollSpecPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hinv.markInv.nameOk, hinv.lastNameOk,
      hfiles ▸ hinv.oneSizeOk, hfiles ▸ hinv.lastSizeOk, hfit_hop⟩, ?_⟩
    simpa only [sepConj_assoc] using hspatial
  refine subroutine_ok.mono_outcome hhop (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left ?_) hpost⟩
    show (kpkGetPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (cliKitStk B).kpkGetPoll).post
        (xg, st) s0 sf ⊢
      (kitKpkGetPollSpec M A lim kpkKit kpkEnv).post (⟨fut, out, self, id⟩, st0, st) s0 sf
    dsimp only [kpkGetPollSpecPlaced, kitKpkGetPollSpec, kpkKit, kpkEnv,
      cliPollKpkFullBudgetEnv, cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliKyberPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced,
      cliKyberPreKeyStoreSpec, cliKpkStoreSpec, cliKpkStoreAtFull, xg]
    refine Entails.sepExists_elim fun evs => ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun pa => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hpa, htr, hmenv⟩ => ?_
    rw [hfiles] at hpa hmenv
    subst hpa
    have hent0 := kpkAnsAt_entails_pollOut_placed A.repAlloc cliIo.rd F0 cliWrOk id spkId kbk
      (cliKitStk B).kpkGetShim (cliKitStk B).kpkGetPoll
      (cliKitStk B).kpkMarkShim (cliKitStk B).kpkMarkPoll st0 id out
    dsimp only at hent0
    have hout_eq : kpkGetPollOutAt
        (CryptoVerification.SignalSession.Cli.KitInst.cliKyberPreKeyStoreSpecPlaced
          A.repAlloc cliIo.rd F0 cliWrOk id spkId kbk
          (cliKitStk B).kpkGetShim (cliKitStk B).kpkGetPoll
          (cliKitStk B).kpkMarkShim (cliKitStk B).kpkMarkPoll) out =
      kpkGetPollOutAt kpkKit out := by
      funext ans; cases ans <;> rfl
    rw [hout_eq] at hent0
    refine Entails.trans (sepConj_mono_left hent0) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ans => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hrel => ?_
    refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
    refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hmenv⟩ ?_
    dsimp only [kpkKit, cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliKyberPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced,
      cliKyberPreKeyStoreSpec, cliKpkStoreSpec, cliKpkStoreAtFull]
    exact Entails.trans (Entails.pure_right hinv (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- Discharges `KyberPreKeyStoreKitPlacedOk` from `RunHooksPlaced` and block-`589` `dirGetSpecPlaced`. -/
theorem cliPollKpk_kitPlacedOk_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed)) :
    KyberPreKeyStoreKitPlacedOk A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc F0 kpkId spkId kbk (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  getShim hblk := cliPollKpk_getShim_rocl_of_hooks mmpl gh W B F0 kpkId spkId kbk hh hblk
  getPoll hblk := cliPollKpk_getPoll_rocl_of_dirGet mmpl gh W B F0 kpkId spkId kbk hh hGet hblk
  getFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_rocl_placed_ok hblk
  markShim hblk :=
    (cliPollKpk_markKitPlacedOk_of_dirGet mmpl gh W B F0 kpkId spkId kbk hDropNz hh hGet).markShim
      hblk
  markPoll hblk :=
    (cliPollKpk_markKitPlacedOk_of_dirGet mmpl gh W B F0 kpkId spkId kbk hDropNz hh hGet).markPoll
      hblk
  markFutDrop hblk :=
    (cliPollKpk_markKitPlacedOk_of_dirGet mmpl gh W B F0 kpkId spkId kbk hDropNz hh
      hGet).markFutDrop hblk

/-! ## 3. Full 6-Kit `CliDecPkPollKitsPlacedOk` Bundle from `dirGetSpecPlaced` -/

/-- Assembles the 6-kit `CliDecPkPollKitsPlacedOk` bundle from `RunHooksPlaced`, block-`589`
`dirGetSpecPlaced`, and block-`46` `sessDeserializeSpecPlaced`. -/
theorem cliDecPkPollKitsPlacedOk_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) :
    CliDecPkPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  let hhStages : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics,
      memcpyRO := hh.memcpyRO, bcmp := hh.bcmp, fs := hh.fs,
      utf8 := hh.utf8, memrchr := hh.memrchr, codecHooks := hh.codecHooks,
      allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
      formatInner := hh.formatInner }
  { sessOk := fun _ _ =>
      cliPollSess_kitPlacedOkSE_untrusted_of_dirGet mmpl gh W hDropNz hh hGet hDeser
    idOk := fun _ _ =>
      cliPollId_kitPlacedOkI_untrusted_of_dirGet mmpl gh W hDropNz hh hGet
    selfOk := fun F0 peer =>
      cliPollSelf_kitPlacedOk_of_dirGet mmpl gh W B F0 peer hDropNz hh hGet
    spkOk := fun F0 sid =>
      cliPollSpk_kitPlacedOk_of_dirGet mmpl gh W B F0 sid hDropNz hhStages hGet
    kpkOk := fun F0 kid sid kbk =>
      cliPollKpk_kitPlacedOk_of_dirGet mmpl gh W B F0 kid sid kbk hDropNz hhStages hGet
    pkOk := fun F0 pid =>
      cliPollPk_kitPlacedOk_of_dirGet mmpl gh W B F0 pid hDropNz hhStages hGet }

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage2PlacedBudgetFd
