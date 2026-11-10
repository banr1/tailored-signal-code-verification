/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SelfSpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `hRead`-Free CLI Poll Self-Identity Store Kit from Block-`589` `dirGetSpecPlaced`

Proves `cliPollSelf_kitPlacedOk_of_dirGet` (`IdentitySelfStoreKitPlacedOkI`) directly from
`RunHooksPlaced` and block-`589` `dirGetSpecPlaced` without raw `hRead` hypotheses.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsSelfPlacedBudgetFd

open Arm64 Arm64.Process ProofLib
open CryptoVerification (IsLsBlockProg LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded kpPollOutAt
  ls_subroutine_ok_rocl_of_block regIdPollOutAt speErrAt subroutine_ok_rocl_of_withLsCodeRoLoaded
  withEnvPre withLsCodeRoLoaded withLsLogOff withLsRoCl
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsDropOffPlaced lsDropOffPlaced_eq
)
open CryptoVerification.SignalSession.Cli (
  IdGhost dirAt idKeyPairFutVtSym idRegIdFutVtSym pathOf utf8
)
open CryptoVerification.SignalSession.Cli.KitInst (
  CliIdInv CliSelfSpeErr cliIdStoreAt cliIdentitySelfSpec cliIdentitySelfSpecPlaced
  cliIdentitySelf_kpErr_layout_placed cliIdentitySelf_regIdErr_layout_placed
  cliIdentityStoreSpec cliSelfSpeErrSpec
)
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel (
  cliKpRel cliKpRel_error_iff cliKpRel_ok_iff cliRegIdRel cliRegIdRel_error_iff cliRegIdRel_ok_iff
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_589 lsProg_602 lsProg_603)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (
  idKeyPairOutAt idOwnFutBoxAt idOwnFutBoxAtPlaced idRegIdOutAt
)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdKeyPairPoll (kpCalleeStk)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll (regCalleeStk)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon (
  idKeyPairOutAtPlaced_eq idRegIdOutAtPlaced_eq
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  CliIdOwnInv cliIdSelfSpecFullPlaced cliIdStoreAtFull cliIdStoreSpecFull cliIdStoreSpecFullPlaced
  cliKitStk cliPollIdKitPlaced cliPollSelfKitPlaced
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  kitKpPollSpec kitKpPollSpecE kitKpShimSpec kitRegIdPollSpec kitRegIdPollSpecE kitRegIdShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI kitKpPollPlacedSpecI kitRegIdPollPlacedSpecI
)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget (
  identityKeyPair_tryFrom_placed_ok_of_hooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  CliGhostHooks cliGhostExterns
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget (
  cliIdFutDrop_rocl_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv cliPollSelfKpPollEnv cliPollSelfRegIdPollEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  runHooks_of_stages
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget (
  CliIdKeyPairPollEnv OptIkpTryFromEnv idKeyPairPoll_placed_caller_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget (
  CliIdRegIdPollEnv OptRegIdMalformedEnv idRegIdPoll_placed_caller_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlacedBudget (
  idKeyPairShim_placed_ok_of_deps idRegIdShim_placed_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  dirGetSpecPlaced idKeyPairPollSpecPlaced idOwnShimSpecPlaced idRegIdPollSpecPlaced
)

private theorem cliPollSelf_kpShim_rocl_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let skit := cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + skit.kpShimOff)
      (withLsRoCl lsmpl (kitKpShimSpec M A lim skit)) := by
  intro skit
  have h602 := idKeyPairShim_placed_ok_of_deps (H := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (stk := (cliKitStk B).kpShim) hh.alloc (by dsimp [cliKitStk, extHookStack]; omega)
  have h602_kit : subroutine_ok (lsProg_602 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 602)
      (withLsCodeRoLoaded lsmpl (kitKpShimSpec M A lim skit)) := by
    refine subroutine_ok_outcome_intro fun ⟨self, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    have hpre' :
        s0.mem ⊨
          (idOwnShimSpecPlaced idKeyPairFutVtSym A lim (cliKitStk B).kpShim).pre (self, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [kitKpShimSpec, skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced] at hpre0 ⊢
      exact hpre0
    refine h602.mono_outcome (self, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded, kitKpShimSpec,
        skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, idOwnFutBoxAtPlaced,
        idOwnFutBoxAt] at hq ⊢
      simpa only [BitVec.zero_add] using hq
    · dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 602) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 602)
    h602_kit hblk (by decide) (by decide)

private theorem cliPollSelf_regIdShim_rocl_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let skit := cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + skit.regIdShimOff)
      (withLsRoCl lsmpl (kitRegIdShimSpec M A lim skit)) := by
  intro skit
  have h603 := idRegIdShim_placed_ok_of_deps (H := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (stk := (cliKitStk B).regIdShim) hh.alloc (by dsimp [cliKitStk, extHookStack]; omega)
  have h603_kit : subroutine_ok (lsProg_603 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 603)
      (withLsCodeRoLoaded lsmpl (kitRegIdShimSpec M A lim skit)) := by
    refine subroutine_ok_outcome_intro fun ⟨self, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    have hpre' :
        s0.mem ⊨
          (idOwnShimSpecPlaced idRegIdFutVtSym A lim (cliKitStk B).regIdShim).pre (self, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [kitRegIdShimSpec, skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced] at hpre0 ⊢
      exact hpre0
    refine h603.mono_outcome (self, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded, kitRegIdShimSpec,
        skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, idOwnFutBoxAtPlaced,
        idOwnFutBoxAt] at hq ⊢
      simpa only [BitVec.zero_add] using hq
    · dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [idOwnShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 603) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 603)
    h603_kit hblk (by decide) (by decide)

private theorem cliPollSelf_kpPoll_rocl_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet589 : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let skit := cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)
    let senv := cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv
    subroutine_ok callerProg (0#64 + skit.kpPollOff)
      (withLsRoCl lsmpl (kitKpPollPlacedSpecI M A lim skit senv)) := by
  intro skit senv
  have hDec84 := identityKeyPair_tryFrom_placed_ok_of_hooks hh.codecHooks
  have hhop := idKeyPairPoll_placed_caller_ok_of_deps
    (callerProg := callerProg) (callerBlk := callerBlk)
    (stk := (cliKitStk B).kpPoll)
    hh.alloc hGet589 hDec84
    (by dsimp [cliKitStk, kpCalleeStk]; omega)
    hblk (by decide) (by decide) (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 567) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok_outcome_intro fun ⟨fut, out, self, g, st⟩ R s0 hpc hrun hpre hsp => ?_
  change IdGhost at g
  dsimp only [withLsCodeRoLoaded, kitKpPollPlacedSpecI, withLsLogOff,
    kitKpPollSpecE, kitKpPollSpec, withEnvPre,
    skit, senv, cliPollSelfKitPlaced, cliPollSelfBudgetEnv, cliPollSelfKpPollEnv,
    cliIdSelfSpecFullPlaced, cliPollIdKitPlaced,
    cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
    cliIdentityStoreSpec, cliIdStoreAt] at hpre
  have hpre' : s0.mem ⊨
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      (⌜s0.fs.files = F0⌝ ∗
      (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        FitsEnv M lim st
          (SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "identity-key-pair"))
            (SeqEnv (OptIkpTryFromEnv (g.own.get cliIo.rd F0 (utf8 "identity-key-pair")))
              FreeOnlyEvs))⌝ ∗
      (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
      (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
      (idOwnFutBoxAt fut self 0#8 ∗ dirAt A.repAlloc self g.own ∗
        memRegion out 72 ∗ lsLogOff ∗ A.pool lim st s0 ∗
        stackAt s0.sp (cliKitStk B).kpPoll ∗
        (dirAt A.repAlloc (self + 0x28#64) g.peers ∗ R)))))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, hfit⟩, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hown, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
  let frameKpCore : SepProp :=
    ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
    ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
    dirAt A.repAlloc (self + 0x28#64) g.peers
  have hfit_hop :
      FitsEnv M lim st
        (CliIdKeyPairPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd
          s0.fs.files ⟨fut, out, self, g.own⟩) := by
    rw [hfiles]; exact hfit
  have hhop_pure :
      s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        g.own.path.length < 2 ^ 32 ∧
        cliWrOk (pathOf g.own.path (utf8 "identity-key-pair")) ∧
        (∀ bs, g.own.get cliIo.rd s0.fs.files (utf8 "identity-key-pair") = .ok bs →
          bs.length < 2 ^ 32) ∧
        FitsEnv M lim st
          (CliIdKeyPairPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd
            s0.fs.files ⟨fut, out, self, g.own⟩) :=
    ⟨hx0, hx8, hown.ownPathLt, hown.kpPathOk,
      fun bs hbs => hown.kpSizeOk bs (hfiles ▸ hbs), hfit_hop⟩
  have hm_hop :
      s0.mem ⊨
        (idKeyPairPollSpecPlaced cliIo.rd cliWrOk A lim
          (CliIdKeyPairPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd)
          (cliKitStk B).kpPoll).pre (⟨fut, out, self, g.own⟩, st) s0 ∗
        (frameKpCore ∗ R) := by
    dsimp only [idKeyPairPollSpecPlaced, withLsCodeRoLoaded, frameKpCore,
      idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hspatial ⊢
    have h1 : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          g.own.path.length < 2 ^ 32 ∧
          cliWrOk (pathOf g.own.path (utf8 "identity-key-pair")) ∧
          (∀ bs, g.own.get cliIo.rd s0.fs.files (utf8 "identity-key-pair") = .ok bs →
            bs.length < 2 ^ 32) ∧
          FitsEnv M lim st
            (CliIdKeyPairPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd
              s0.fs.files ⟨fut, out, self, g.own⟩)⌝ ∗
        (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
        (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
        (idOwnFutBoxAt fut self 0#8 ∗ dirAt A.repAlloc self g.own ∗
          memRegion out 72 ∗ lsLogOff ∗ A.pool lim st s0 ∗
          stackAt s0.sp (cliKitStk B).kpPoll ∗
          (dirAt A.repAlloc (self + 0x28#64) g.peers ∗ R))))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hhop_pure, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hown, ?_⟩
      rw [satisfies_pure_sepConj]
      dsimp only [idOwnFutBoxAt]
      exact ⟨hinv, hspatial⟩
    dsimp only [idOwnFutBoxAt, CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff,
      CryptoVerification.LibsignalTripleRatchet.lsLogOff] at h1 ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
  refine hhop.mono_outcome (⟨fut, out, self, g.own⟩, st) (frameKpCore ∗ R)
    s0 hpc hrun hm_hop hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [idKeyPairPollSpecPlaced, withLsCodeRoLoaded, frameKpCore] at hpost
    simp_rw [idKeyPairOutAtPlaced_eq] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨evs, ans0, ⟨hans0, htr, hevs⟩, hm⟩ := hpost
    rw [hfiles, IdGhost.keyPair_mk_own] at hans0
    rw [hfiles] at hevs
    dsimp only [withLsCodeRoLoaded, kitKpPollPlacedSpecI, withLsLogOff,
      kitKpPollSpecE, kitKpPollSpec, withEnvPre,
      skit, senv, cliPollSelfKitPlaced, cliPollSelfBudgetEnv, cliPollSelfKpPollEnv,
      cliIdSelfSpecFullPlaced, cliPollIdKitPlaced,
      cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
      cliIdentityStoreSpec, cliIdStoreAt]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    cases ans0 with
    | ok kp =>
      have hrel : cliKpRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok kp) :=
        (cliKpRel_ok_iff (E := CliSelfSpeErr) cliIo.rd F0 g kp).2 hans0.symm
      refine ⟨.ok kp, evs, ?_⟩
      dsimp only [kpPollOutAt, idKeyPairOutAt, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hm ⊢
      have hgoal : sf.mem ⊨
          ⌜cliKpRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok kp) ∧
            sf.trace = s0.trace ++ [] ∧
            SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "identity-key-pair"))
              (SeqEnv (OptIkpTryFromEnv (g.own.get cliIo.rd F0 (utf8 "identity-key-pair")))
                FreeOnlyEvs) evs⌝ ∗
          (idKeyPairOutAt A.repAlloc out (.ok kp) ∗ idOwnFutBoxAt fut self 1#8 ∗
            dirAt A.repAlloc self g.own ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (cliKitStk B).kpPoll ∗
            ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
            ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
            dirAt A.repAlloc (self + 0x28#64) g.peers ∗ R) := by
        dsimp only [idKeyPairOutAt, idOwnFutBoxAt]
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrel, by rw [List.append_nil]; exact htr, hevs⟩, hm⟩
      dsimp only [idKeyPairOutAt, idOwnFutBoxAt] at hgoal
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    | error u =>
      cases u
      have herr_ent :
          idKeyPairOutAt A.repAlloc out (.error ()) ⊢
            ∃∗ e : skit.KpErr, kpPollOutAt skit out (.error e) :=
        (cliIdentitySelf_kpErr_layout_placed A.repAlloc F0
          (peer := peer) (t1 := (cliKitStk B).idTrustShim) (t2 := (cliKitStk B).idTrustPoll)
          (t3 := (cliKitStk B).idSaveShim) (t4 := (cliKitStk B).idSavePoll)
          (k1 := (cliKitStk B).kpShim) (k2 := (cliKitStk B).kpPoll)
          (k3 := (cliKitStk B).regIdShim) (k4 := (cliKitStk B).regIdPoll) out).2
      have hm' := Satisfies.mono (sepConj_mono_left herr_ent) hm
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
      dsimp only [skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced,
        cliIdentitySelfSpecPlaced, cliIdentitySelfSpec,
        kpPollOutAt, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hm' ⊢
      obtain ⟨e, hme⟩ := hm'
      have hrel : cliKpRel cliIo.rd F0 g (.error e) :=
        (cliKpRel_error_iff cliIo.rd F0 g e).2 hans0.symm
      refine ⟨.error e, evs, ?_⟩
      dsimp only [kpPollOutAt, cliIdentitySelfSpecPlaced, cliIdentitySelfSpec]
      have hgoal : sf.mem ⊨
          ⌜cliKpRel cliIo.rd F0 g (.error e) ∧
            sf.trace = s0.trace ++ [] ∧
            SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "identity-key-pair"))
              (SeqEnv (OptIkpTryFromEnv (g.own.get cliIo.rd F0 (utf8 "identity-key-pair")))
                FreeOnlyEvs) evs⌝ ∗
          (((out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
              speErrAt (cliSelfSpeErrSpec A.repAlloc) (out + 8#64) e ∗
              memRegion (out + 0x38#64) 16) ∗
            ((fut ↦₆₄ self) ∗ ((fut + 8#64) ↦₈ 1#8) ∗ memRegion (fut + 9#64) 7) ∗
            dirAt A.repAlloc self g.own ∗ lsLogOff ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (cliKitStk B).kpPoll ∗
            ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
            ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
            dirAt A.repAlloc (self + 0x28#64) g.peers ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrel, by rw [List.append_nil]; exact htr, hevs⟩, hme⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
  · dsimp only [idKeyPairPollSpecPlaced, withLsCodeRoLoaded] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · dsimp only [idKeyPairPollSpecPlaced, withLsCodeRoLoaded] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · dsimp only [idKeyPairPollSpecPlaced, withLsCodeRoLoaded] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

private theorem cliPollSelf_regIdPoll_rocl_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet589 : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let skit := cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)
    let senv := cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv
    subroutine_ok callerProg (0#64 + skit.regIdPollOff)
      (withLsRoCl lsmpl (kitRegIdPollPlacedSpecI M A lim skit senv)) := by
  intro skit senv
  have hhop := idRegIdPoll_placed_caller_ok_of_deps
    (callerProg := callerProg) (callerBlk := callerBlk)
    (stk := (cliKitStk B).regIdPoll)
    hh.alloc hGet589
    (by dsimp [cliKitStk, regCalleeStk]; omega)
    hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 568) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok_outcome_intro fun ⟨fut, out, self, g, st⟩ R s0 hpc hrun hpre hsp => ?_
  change IdGhost at g
  dsimp only [withLsCodeRoLoaded, kitRegIdPollPlacedSpecI, withLsLogOff,
    kitRegIdPollSpecE, kitRegIdPollSpec, withEnvPre,
    skit, senv, cliPollSelfKitPlaced, cliPollSelfBudgetEnv, cliPollSelfRegIdPollEnv,
    cliIdSelfSpecFullPlaced, cliPollIdKitPlaced,
    cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
    cliIdentityStoreSpec, cliIdStoreAt] at hpre
  have hpre' : s0.mem ⊨
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      (⌜s0.fs.files = F0⌝ ∗
      (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        FitsEnv M lim st
          (SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "registration-id"))
            (SeqEnv (OptRegIdMalformedEnv (g.own.get cliIo.rd F0 (utf8 "registration-id")))
              FreeOnlyEvs))⌝ ∗
      (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
      (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
      (idOwnFutBoxAt fut self 0#8 ∗ dirAt A.repAlloc self g.own ∗
        memRegion out 48 ∗ A.pool lim st s0 ∗
        stackAt s0.sp (cliKitStk B).regIdPoll ∗
        (dirAt A.repAlloc (self + 0x28#64) g.peers ∗ lsLogOff ∗ R)))))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, hfit⟩, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hown, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
  let frameRegCore : SepProp :=
    ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
    ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
    dirAt A.repAlloc (self + 0x28#64) g.peers ∗ lsLogOff
  have hfit_hop :
      FitsEnv M lim st
        (CliIdRegIdPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd
          s0.fs.files ⟨fut, out, self, g.own⟩) := by
    rw [hfiles]; exact hfit
  have hhop_pure :
      s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        g.own.path.length < 2 ^ 32 ∧
        cliWrOk (pathOf g.own.path (utf8 "registration-id")) ∧
        FitsEnv M lim st
          (CliIdRegIdPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd
            s0.fs.files ⟨fut, out, self, g.own⟩) :=
    ⟨hx0, hx8, hown.ownPathLt, hown.regPathOk, hfit_hop⟩
  have hm_hop :
      s0.mem ⊨
        (idRegIdPollSpecPlaced cliIo.rd cliWrOk A lim
          (CliIdRegIdPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd)
          (cliKitStk B).regIdPoll).pre (⟨fut, out, self, g.own⟩, st) s0 ∗
        (frameRegCore ∗ R) := by
    dsimp only [idRegIdPollSpecPlaced, withLsCodeRoLoaded, frameRegCore,
      idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hspatial ⊢
    have h1 : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          g.own.path.length < 2 ^ 32 ∧
          cliWrOk (pathOf g.own.path (utf8 "registration-id")) ∧
          FitsEnv M lim st
            (CliIdRegIdPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd
              s0.fs.files ⟨fut, out, self, g.own⟩)⌝ ∗
        (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
        (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
        (idOwnFutBoxAt fut self 0#8 ∗ dirAt A.repAlloc self g.own ∗
          memRegion out 48 ∗ A.pool lim st s0 ∗
          stackAt s0.sp (cliKitStk B).regIdPoll ∗
          (dirAt A.repAlloc (self + 0x28#64) g.peers ∗ lsLogOff ∗ R))))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hhop_pure, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hown, ?_⟩
      rw [satisfies_pure_sepConj]
      dsimp only [idOwnFutBoxAt]
      exact ⟨hinv, hspatial⟩
    dsimp only [idOwnFutBoxAt, CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff,
      CryptoVerification.LibsignalTripleRatchet.lsLogOff] at h1 ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
  refine hhop.mono_outcome (⟨fut, out, self, g.own⟩, st) (frameRegCore ∗ R)
    s0 hpc hrun hm_hop hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [idRegIdPollSpecPlaced, withLsCodeRoLoaded, frameRegCore] at hpost
    simp_rw [idRegIdOutAtPlaced_eq] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨evs, ans0, ⟨hans0, htr, hevs⟩, hm⟩ := hpost
    rw [hfiles, IdGhost.regId_mk_own] at hans0
    rw [hfiles] at hevs
    dsimp only [withLsCodeRoLoaded, kitRegIdPollPlacedSpecI, withLsLogOff,
      kitRegIdPollSpecE, kitRegIdPollSpec, withEnvPre,
      skit, senv, cliPollSelfKitPlaced, cliPollSelfBudgetEnv, cliPollSelfRegIdPollEnv,
      cliIdSelfSpecFullPlaced, cliPollIdKitPlaced,
      cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
      cliIdentityStoreSpec, cliIdStoreAt]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    cases ans0 with
    | ok reg =>
      have hrel : cliRegIdRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok reg) :=
        (cliRegIdRel_ok_iff (E := CliSelfSpeErr) cliIo.rd F0 g reg).2 hans0.symm
      refine ⟨.ok reg, evs, ?_⟩
      dsimp only [regIdPollOutAt, idRegIdOutAt, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hm ⊢
      have hgoal : sf.mem ⊨
          ⌜cliRegIdRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok reg) ∧
            sf.trace = s0.trace ++ [] ∧
            SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "registration-id"))
              (SeqEnv (OptRegIdMalformedEnv (g.own.get cliIo.rd F0 (utf8 "registration-id")))
                FreeOnlyEvs) evs⌝ ∗
          (((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₃₂ reg) ∗
              memRegion (out + 12#64) 36) ∗
            idOwnFutBoxAt fut self 1#8 ∗
            dirAt A.repAlloc self g.own ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (cliKitStk B).regIdPoll ∗
            ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
            ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
            dirAt A.repAlloc (self + 0x28#64) g.peers ∗ lsLogOff ∗ R) := by
        dsimp only [idOwnFutBoxAt]
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrel, by rw [List.append_nil]; exact htr, hevs⟩, hm⟩
      dsimp only [idOwnFutBoxAt] at hgoal
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    | error u =>
      cases u
      have herr_ent :
          idRegIdOutAt A.repAlloc out (.error ()) ⊢
            ∃∗ e : skit.RegIdErr, regIdPollOutAt skit out (.error e) :=
        (cliIdentitySelf_regIdErr_layout_placed A.repAlloc F0
          (peer := peer) (t1 := (cliKitStk B).idTrustShim) (t2 := (cliKitStk B).idTrustPoll)
          (t3 := (cliKitStk B).idSaveShim) (t4 := (cliKitStk B).idSavePoll)
          (k1 := (cliKitStk B).kpShim) (k2 := (cliKitStk B).kpPoll)
          (k3 := (cliKitStk B).regIdShim) (k4 := (cliKitStk B).regIdPoll) out).2
      have hm' := Satisfies.mono (sepConj_mono_left herr_ent) hm
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
      dsimp only [skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced,
        cliIdentitySelfSpecPlaced, cliIdentitySelfSpec,
        regIdPollOutAt, idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hm' ⊢
      obtain ⟨e, hme⟩ := hm'
      have hrel : cliRegIdRel cliIo.rd F0 g (.error e) :=
        (cliRegIdRel_error_iff cliIo.rd F0 g e).2 hans0.symm
      refine ⟨.error e, evs, ?_⟩
      dsimp only [regIdPollOutAt, cliIdentitySelfSpecPlaced, cliIdentitySelfSpec]
      have hgoal : sf.mem ⊨
          ⌜cliRegIdRel cliIo.rd F0 g (.error e) ∧
            sf.trace = s0.trace ++ [] ∧
            SeqEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F0 g.own (utf8 "registration-id"))
              (SeqEnv (OptRegIdMalformedEnv (g.own.get cliIo.rd F0 (utf8 "registration-id")))
                FreeOnlyEvs) evs⌝ ∗
          (speErrAt (cliSelfSpeErrSpec A.repAlloc) out e ∗
            ((fut ↦₆₄ self) ∗ ((fut + 8#64) ↦₈ 1#8) ∗ memRegion (fut + 9#64) 7) ∗
            dirAt A.repAlloc self g.own ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (cliKitStk B).regIdPoll ∗
            ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
            ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
            dirAt A.repAlloc (self + 0x28#64) g.peers ∗ lsLogOff ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrel, by rw [List.append_nil]; exact htr, hevs⟩, hme⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
  · dsimp only [idRegIdPollSpecPlaced, withLsCodeRoLoaded] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · dsimp only [idRegIdPollSpecPlaced, withLsCodeRoLoaded] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · dsimp only [idRegIdPollSpecPlaced, withLsCodeRoLoaded] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-- Discharges `IdentitySelfStoreKitPlacedOkI` for `cliPollSelfKitPlaced` directly from
`SkeletonPlacedBudget.RunHooksPlaced` and block-`589` `dirGetSpecPlaced`. -/
theorem cliPollSelf_kitPlacedOk_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed)) :
    IdentitySelfStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  kpShim hblk := cliPollSelf_kpShim_rocl_of_hooks mmpl gh W B F0 peer hh hblk
  kpPoll hblk := cliPollSelf_kpPoll_rocl_of_dirGet mmpl gh W B F0 peer hh hGet hblk
  kpFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]; exact cliIdFutDrop_rocl_placed_ok hblk
  regIdShim hblk := cliPollSelf_regIdShim_rocl_of_hooks mmpl gh W B F0 peer hh hblk
  regIdPoll hblk := cliPollSelf_regIdPoll_rocl_of_dirGet mmpl gh W B F0 peer hh hGet hblk
  regIdFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]; exact cliIdFutDrop_rocl_placed_ok hblk

theorem cliPollSelf_kitPlacedOk_stagesHooks_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed)) :
    IdentitySelfStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliPollSelf_kitPlacedOk_of_dirGet mmpl gh W B F0 peer hDropNz (runHooks_of_stages hh) hGet

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsSelfPlacedBudgetFd
