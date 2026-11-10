/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Stage P4 Instantiations

Defines CLI poll store budget envelopes (`cliPollSessBudgetEnv`, `cliPollIdBudgetEnv`,
`cliPollPkBudgetEnv`, `cliPollKpkBudgetEnv`), discharges the four placed CLI store-kit bundles, and
instantiates `StageP4MatchedCliPlacedStmt` and `StageP4PathACliPlacedStmt` (plus SeqFree variants)
from `hDropNz : lsmpl.base 547 ≠ 0#64`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (IdentityKey PublicKey)
open CryptoGames.LibsignalSessionApi (IdentityChange Session SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsBlackBoxU8Sym
   ls_hook_ok_ultra_of_mem lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_52)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (ClosureCalleeSavedP4)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
  (SessionExtraRel stageP4CallStack stageP4EnvOk stageP4Quiet)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (stageP4MatchedCallStack)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStackX extHookStack hookMemcpy_trace_ok hookMemmove_trace_ok
   noAllocShimSpec sessionMemcpySpec sessionMemmoveSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsAt FsFiles IdentityStoreSpec IdentityVtablesPlacedOk KyberPreKeyStoreSpec
   KyberPreKeyVtablesPlacedOk LibsignalCodeRoLoaded PreKeyStoreSpec PreKeyVtablesPlacedOk
   SessionOnlyVtablesPlacedOk SessionStoreSpec extract_withLsCodeRoLoaded kpkMarkPollOutAt
   ls_subroutine_ok_rocl_of_block preKeyRemovePollOutAt subroutine_ok_rocl_of_withLsCodeRoLoaded
   subroutine_ok_withLsCodeRoLoaded_of_plain unitSpePollOutAt withEnvPre withLsCodeRoLoaded
   withLsLogOff withLsRoCl)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced isCliPanicSymbolPlaced lsDropOffPlaced lsDropOffPlaced_eq lsReadFileSym)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdGhost KpkMarkPollGhost KyberGhost PkPollGhost ReadRule cliIdentityVtSym
   cliSessionVtSym dirAt keyName kpkMarkBoxAt kpkMarkOf pkBoxAt pkRemoveFutVtSym pkRemoveOf
   pkRemoveOutAt)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliExternsPlaced_memmove cliIo cliWrOk main_cliExternsPlaced_row)
open CryptoVerification.SignalSession.Cli.Placed
  (lsProg_570 lsProg_575 lsProg_578 lsProg_589 lsProg_597 lsProg_610)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SignalSession.Cli.KitInst
  (CliKpkInv CliKpkMarkErr CliPkInv cliIdentityStoreSpec cliKpkGetSide cliKpkMarkErrSpec
   cliKpkStoreAt cliKpkStoreSpec cliKpkStoreSpecPlaced cliKyberPreKeyStoreSpec cliPkStoreAt
   cliPreKeyStoreSpec kpkMarkBoxAt_memRegion pkBoxAt_memRegion pkRemoveOutAt_entails_pollOut_placed)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (cliIdentityKitSpecPlaced)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (decNeedPlaced dirPutNeedPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (CliIdOwnInv CliKpkInvFull DpKitStk cliIdStoreAtFull cliIdStoreSpecFull cliIdStoreSpecFullPlaced
   cliKitStk cliKpkStoreAtFull cliKpkStoreSpecFullPlaced cliPollIdKitPlaced
   cliPollId_vtablesPlacedOk cliPollKpkKitPlaced cliPollKpk_vtablesPlacedOk cliPollPkKitPlaced
   cliPollPk_vtablesPlacedOk cliPollSessKitPlaced cliPollSess_vtablesPlacedOk dpPollEntryPlaced
   dpPollProgPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv VmPreserved
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (BoxAllocEnv PreKeyStoreBudgetEnv kitPreKeyRemovePollSpec kitPreKeyRemovePollSpecE
   kitPreKeyRemoveShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
  (KyberPreKeyStoreBudgetEnv kitKpkMarkPollSpec kitKpkMarkPollSpecE kitKpkMarkShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv SaveStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv StoreStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE kitSavePollPlacedSpec kitSavePollPlacedSpecE
   kitSavePollPlacedSpecI kitTrustPollPlacedSpec kitTrustPollPlacedSpecE kitTrustPollPlacedSpecI)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (dropSessionStructureLocal2Spec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget (drop_session_structure4_placed_ok_at)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget (StageP4MatchedEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4PlacedBudget (stageP4_matched_placed_ok)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget (KyberPreKeyMarkKitPlacedOk)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget (PreKeyRemoveKitPlacedOk)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNonePlacedBudget (StageP4StepEnv StageP4StoreBranchEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsPlacedBudget (stageP4_v1_vregs_mark_remove_placed_ok)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced serializeCanonSpecX)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemmoveBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns cliGhostExterns_other)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced ReadFileRuleEnv pkRemovePollSpecPlaced pkShimSpecPlaced readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget (pkRemoveShim_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget (CliPkRemovePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudget (pkRemovePoll_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudget (CliKpkMarkPollEnv kpkMarkPoll_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget (serializeCanonX_placed_ok_of_serContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget
  (serializeCanonSeqFreeSpecX serializeCanonSeqFree_placed_ok_of_serContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (SerializeCanonSeqFreeValidEnv cliDecimal_placed_ok cliDirGet_placed_ok cliDirPut_placed_ok
   cliSessKitOkSE_placed cliSessKitOkSE_seqFree_placed cliSessionKitDefaultBudgetEnv
   cliSessionKitSeqFreeBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdFutDrop_rocl_placed_ok cliIdKitOkIE_placed cliIdentityKitDefaultBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlacedBudget
  (cliKpkMarkShim_placed_ok cliKpkStoreBudgetEnvPlaced cliKpkStoreSpecPlaced_markPoll_of_env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (OptRemoveStepEnv RunHooksPlaced StageP4BranchPlaced StageP4MatchedBranchPlaced StageP4PathAEnv
   StageP4PathAMarkErrEnv StageP4PathARemoveErrEnv StageP4PathASaveErrEnv StageP4PathAStoreStepEnv
   stageP4MatchedPrePlaced stageP4PrePlaced)

/-! ## 1. Hook & Identity-Store Full-Invariant Helpers -/

private theorem toSkeletonRunHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

private theorem hookMemcpy_vm_local (s : State) : VmPreserved s (hookMemcpy s) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl,
    fun a => congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_writeBytes_norm _ _ _) a,
    fun _ _ _ => rfl⟩

private theorem hookMemmove_vm_local (s : State) : VmPreserved s (hookMemmove s) :=
  hookMemcpy_vm_local s

theorem cliSerContractsX_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    SerContractsXPlaced M A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  SerContractsXPlaced.of_hooks hh.codecHooks.alloc hh.codecHooks.dealloc hh.codecHooks.realloc
    ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
    (by
      let hlookup : cliGhostExterns gh (cliExternsPlaced mmpl W) "memmove" = some hookMemmove :=
        (cliGhostExterns_other gh (cliExternsPlaced mmpl W)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (cliExternsPlaced_memmove mmpl W)
      exact (show withVmPreserved (sessionMemmoveSpec extHookStack) =
          sessionMemmoveBudgetSpec extHookStack from rfl) ▸
        hookSat_withVmPreserved ⟨hookMemmove, hlookup, hookMemmove_trace_ok extHookStack⟩
          fun f hf s => by
            rw [hlookup] at hf; injection hf with hfg; subst hfg; exact hookMemmove_vm_local s)
    (by
      refine ProofLib.HookSat.mono hh.codecHooks.memcpy fun ⟨dst, src, bs⟩ R s0 hpre =>
        ⟨(dst, src, bs), stackAt s0.sp extHookStack ∗ R, ?_, fun sf hpost => ?_⟩
      · dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec,
          withVmPreserved, sessionMemcpySpec, ProofLib.libcMemcpySpec,
          CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
          ProofLib.memcpyRegionSpec] at hpre ⊢
        ac_nf at hpre ⊢
      · dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec,
          withVmPreserved, sessionMemcpySpec,
          CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hpost ⊢
        ac_nf at hpost ⊢)

private theorem cliSerializeCanonX_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)) :=
  serializeCanonX_placed_ok_of_serContractsX (cliSerContractsX_placed_ok mmpl gh W hh)

theorem cliSerializeCanonSeqFree_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)) :=
  serializeCanonSeqFree_placed_ok_of_serContractsX (cliSerContractsX_placed_ok mmpl gh W hh)

private theorem false_absorb_extra {extra R : SepProp} {m : Memory}
    (h : m ⊨ ⌜False⌝ ∗ (extra ∗ R)) : m ⊨ ⌜False⌝ ∗ R := by
  rw [satisfies_pure_sepConj] at h; exact nomatch h.1

private theorem saveUpd_own_placed (rd : ReadRule) (F0 : FsFiles) (g : IdGhost)
    (addr : AddrVal) (key : IdentityKey) : (IdGhost.saveUpd rd F0 g addr key).own = g.own := by
  unfold IdGhost.saveUpd; cases IdGhost.peer rd F0 g addr <;> rfl

private theorem withPanics_cliGhostExterns_eq (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      cliGhostExterns gh (cliExternsPlaced mmpl W) := by
  funext name
  by_cases hp : Rust.isPanicSymbol name = true
  · have hother : cliGhostExterns gh (cliExternsPlaced mmpl W) name = cliExternsPlaced mmpl W name :=
      cliGhostExterns_other gh (cliExternsPlaced mmpl W)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli, CryptoVerification.SignalSession.lsRustDeallocSymCli, CryptoVerification.SignalSession.lsRustReallocSymCli, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli, CryptoVerification.SignalSession.lsRustDeallocSymCli, CryptoVerification.SignalSession.lsRustReallocSymCli, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli, CryptoVerification.SignalSession.lsRustDeallocSymCli, CryptoVerification.SignalSession.lsRustReallocSymCli, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli, CryptoVerification.SignalSession.lsRustDeallocSymCli, CryptoVerification.SignalSession.lsRustReallocSymCli, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli, CryptoVerification.SignalSession.lsRustDeallocSymCli, CryptoVerification.SignalSession.lsRustReallocSymCli, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli, CryptoVerification.SignalSession.lsRustDeallocSymCli, CryptoVerification.SignalSession.lsRustReallocSymCli, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsReadFileSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsReadStdinSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemsetSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemcpySym] at hp)
    unfold Rust.withPanics
    rw [hother]
    unfold cliExternsPlaced isCliPanicSymbolPlaced
    simp [hp]
  · simp [Rust.withPanics, hp]

theorem cliGhostExterns_blackBox (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook :=
  (cliGhostExterns_other gh (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (CryptoVerification.SignalSession.Cli.RunGlue.cliExternsPlaced_row mmpl W
      (List.mem_append_right _ (List.mem_of_getElem? (i := 11) rfl)))

/-- Retag `IdentityStoreBudgetEnv` from `cliIdentityKitSpecPlaced` to `cliIdStoreSpecFullPlaced`. -/
def fullIdKitBudgetEnv [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {peer : AddrGhost} {t1 t2 t3 t4 : Nat}
    (baseEnv : IdentityStoreBudgetEnv
      (cliIdentityKitSpecPlaced A rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)) :
    IdentityStoreBudgetEnv
      (cliIdStoreSpecFullPlaced A rd F0 pathOk peer t1 t2 t3 t4) where
  trustPollEnv := baseEnv.trustPollEnv
  savePollEnv := baseEnv.savePollEnv

/-- Budget-threaded lift of `IdentityStoreKitPlacedOkI` from `cliIdentityKitSpecPlaced` to
`cliIdStoreSpecFullPlaced` (carrying `CliIdOwnInv rd F0 pathOk g.own` in the frame). -/
theorem cliIdKitPlacedOkI_full [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {peer : AddrGhost} {t1 t2 t3 t4 : Nat}
    {baseEnv : IdentityStoreBudgetEnv
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)}
    (hBase : IdentityStoreKitPlacedOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)
      baseEnv H) :
    IdentityStoreKitPlacedOkI A lim
      (cliIdStoreSpecFullPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4)
      (fullIdKitBudgetEnv baseEnv) H where
  trustShim := hBase.trustShim
  trustFutDrop := hBase.trustFutDrop
  saveShim := hBase.saveShim
  saveFutDrop := hBase.saveFutDrop
  trustPoll hblk := by
    refine subroutine_ok_map_panic (hBase.trustPoll hblk) ?_
    rintro ⟨x, d, self, g, st⟩ R s0 hpre
    change IdGhost at g
    dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
      kitTrustPollPlacedSpec, withEnvPre, cliIdentityStoreSpec, cliIdStoreSpecFullPlaced,
      cliIdStoreSpecFull, cliIdStoreAtFull, fullIdKitBudgetEnv] at hpre
    have hpre' : s0.mem ⊨ (withLsRoCl lsmpl (kitTrustPollPlacedSpecI M A lim
        (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)
        baseEnv)).pre (x, d, self, g, st) s0 ∗ (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R) := by
      dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        kitTrustPollPlacedSpec, withEnvPre, cliIdentityKitSpecPlaced, cliIdentityStoreSpec]
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    refine ⟨(x, d, self, g, st), ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R, hpre', ?_,
      fun _ hpan => false_absorb_extra hpan⟩
    intro sf hpost
    dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
      kitTrustPollPlacedSpec, withEnvPre, cliIdentityKitSpecPlaced, cliIdentityStoreSpec,
      cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull, fullIdKitBudgetEnv] at hpost ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
    obtain ⟨ans, evs, hm⟩ := hpost
    exact ⟨ans, evs, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm⟩
  savePoll hblk := by
    refine subroutine_ok_map_panic (hBase.savePoll hblk) ?_
    rintro ⟨x, self, g, st⟩ R s0 hpre
    change IdGhost at g
    dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
      kitSavePollPlacedSpec, withEnvPre, cliIdentityStoreSpec, cliIdStoreSpecFullPlaced,
      cliIdStoreSpecFull, cliIdStoreAtFull, fullIdKitBudgetEnv] at hpre
    have hpre' : s0.mem ⊨ (withLsRoCl lsmpl (kitSavePollPlacedSpecI M A lim
        (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)
        baseEnv)).pre (x, self, g, st) s0 ∗ (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R) := by
      dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        kitSavePollPlacedSpec, withEnvPre, cliIdentityKitSpecPlaced, cliIdentityStoreSpec]
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    refine ⟨(x, self, g, st), ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R, hpre', ?_,
      fun _ hpan => false_absorb_extra hpan⟩
    intro sf hpost
    dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
      kitSavePollPlacedSpec, withEnvPre, cliIdentityKitSpecPlaced, cliIdentityStoreSpec,
      cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull, fullIdKitBudgetEnv] at hpost ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
    obtain ⟨ans, evs, hm⟩ := hpost
    rw [saveUpd_own_placed]
    exact ⟨ans, evs, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm⟩

/-! ## 2. Concrete CLI Poll Store Budget Envelopes & Placed Kit Discharges -/

/-- Default `SessionStoreBudgetEnv` for `cliPollSessKitPlaced`. -/
abbrev cliPollSessBudgetEnv [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv cliIo.rd) :
    SessionStoreBudgetEnv (cliPollSessKitPlaced A F0 scopeKit peer σ) :=
  cliSessionKitDefaultBudgetEnv A cliIo.rd F0 cliWrOk scopeKit peer
    σ.sessLoadShim σ.sessLoadPoll σ.sessStoreShim σ.sessStorePoll
    DeserEnv cliSessionVtSym cliIdentityVtSym ReadEnv

/-- SeqFree (`SerializeCanonSeqFreeValidEnv` = `RecordSerializeSeqFreeValidEnv`)
`SessionStoreBudgetEnv` for `cliPollSessKitPlaced`. -/
abbrev cliPollSessSeqFreeBudgetEnv [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv cliIo.rd) :
    SessionStoreBudgetEnv (cliPollSessKitPlaced A F0 scopeKit peer σ) :=
  cliSessionKitSeqFreeBudgetEnv A cliIo.rd F0 cliWrOk scopeKit peer
    σ.sessLoadShim σ.sessLoadPoll σ.sessStoreShim σ.sessStorePoll
    DeserEnv cliSessionVtSym cliIdentityVtSym ReadEnv

/-- Default `IdentityStoreBudgetEnv` for `cliPollIdKitPlaced`. -/
abbrev cliPollIdBudgetEnv [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv cliIo.rd) :
    IdentityStoreBudgetEnv (cliPollIdKitPlaced A F0 peer σ) :=
  fullIdKitBudgetEnv
    (cliIdentityKitDefaultBudgetEnv A cliIo.rd F0 cliWrOk peer
      σ.idTrustShim σ.idTrustPoll σ.idSaveShim σ.idSavePoll cliIdentityVtSym ReadEnv)

/-- Concrete `remove_pre_key` poll allocation envelope for `cliPollPkKitPlaced`. -/
def cliPollPkRemovePollEnv
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (dir : DirGhost) (id : BitVec 32) : List AllocEvent → Prop :=
  CliPkRemovePollEnv cliIo.rd DecimalEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) DirPutEnv
    F0 ⟨0#64, 0#64, 0#64, id, dir⟩

/-- Default `PreKeyStoreBudgetEnv` for `cliPollPkKitPlaced` (Stage P4 only invokes `remove_pre_key`;
`getPollEnv` is `(· = [])`). -/
def cliPollPkBudgetEnv [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv cliIo.rd) :
    PreKeyStoreBudgetEnv (cliPollPkKitPlaced A F0 pid σ) where
  getPollEnv := fun _ _ => (· = [])
  removePollEnv := cliPollPkRemovePollEnv ReadEnv F0

/-- Concrete `mark_kyber_pre_key_used` poll allocation envelope for `cliPollKpkKitPlaced`. -/
def cliPollKpkMarkPollEnv
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (kg : KyberGhost) (kid ksid : BitVec 32) (kbk : PublicKey) :
    List AllocEvent → Prop :=
  CliKpkMarkPollEnv cliIo.rd DecimalEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) DirPutEnv
    F0 ⟨0#64, 0#64, 0#64, 0#64, kid, ksid, kbk, kg⟩

/-- Default `KyberPreKeyStoreBudgetEnv` for `cliPollKpkKitPlaced` (Stage P4 only invokes
`mark_kyber_pre_key_used`; `getPollEnv` is `(· = [])`). -/
def cliPollKpkBudgetEnv [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (kpkId spkId : BitVec 32) (kbk : PublicKey) (σ : DpKitStk)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv cliIo.rd) :
    KyberPreKeyStoreBudgetEnv (cliPollKpkKitPlaced A F0 kpkId spkId kbk σ) where
  getPollEnv := fun _ _ => (· = [])
  markPollEnv := cliPollKpkMarkPollEnv ReadEnv F0

/-- Discharges `SessionOnlyKitPlacedOkSE` for `cliPollSessKitPlaced` from `RunHooksPlaced`,
`hRead`, and `hDeser`. -/
theorem cliPollSess_kitPlacedOkSE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) :
    SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessBudgetEnv A.repAlloc F0 peer (cliKitStk B) DeserEnv ReadEnv)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_placed
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (deserProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (deserBlk := 518)
    (serProg := lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz (fun _ hp => hp.2) (toSkeletonRunHooks hh)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
    hDeser
    (cliSerializeCanonX_placed_ok mmpl gh W hh)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Discharges `SessionOnlyKitPlacedOkSE` for `cliPollSessKitPlaced` at SeqFree
`cliPollSessSeqFreeBudgetEnv` (`SerializeCanonSeqFreeValidEnv` = `RecordSerializeSeqFreeValidEnv`)
from `RunHooksPlaced`, `hRead`, and `hDeser`. -/
theorem cliPollSess_seqFreeKitPlacedOkSE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) :
    SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessSeqFreeBudgetEnv A.repAlloc F0 peer (cliKitStk B) DeserEnv ReadEnv)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_seqFree_placed
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (deserProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (deserBlk := 518)
    (serProg := lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz (fun _ hp => hp.2) (toSkeletonRunHooks hh)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
    hDeser
    (cliSerializeCanonSeqFree_placed_ok mmpl gh W hh)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Discharges `IdentityStoreKitPlacedOkI` for `cliPollIdKitPlaced` from `RunHooksPlaced` and
`hRead`. -/
theorem cliPollId_kitPlacedOkI [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliIdKitPlacedOkI_full
    (cliIdKitOkIE_placed
      (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
      hDropNz (fun _ hp => hp.2) (toSkeletonRunHooks hh)
      (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
      (cliGhostExterns_blackBox mmpl gh W)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) (by decide))

private theorem cliPollKpk_markShim_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hblk : callerBlk < 619) :
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

private theorem cliPollKpk_markPoll_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hblk : callerBlk < 619) :
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B)
    subroutine_ok callerProg (0#64 + kpkKit.markPollOff)
      (withLsRoCl lsmpl
        (kitKpkMarkPollSpecE M A lim kpkKit
          (cliPollKpkBudgetEnv A.repAlloc F0 kpkId spkId kbk (cliKitStk B) ReadEnv))) := by
  intro kpkKit
  let hhSkel := toSkeletonRunHooks hh
  have hDecimal := cliDecimal_placed_ok hhSkel
  have hGet := cliDirGet_placed_ok
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (fun _ hp => hp.2) hhSkel
    (subroutine_ok_withLsCodeRoLoaded_of_plain hRead) (by decide) (by decide)
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
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
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
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp2
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
    Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [relProp]; ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  exact Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [relProp]; ac_rfl))
    ((satisfies_pure_sepConj ..).mpr ⟨hinv.mark, hm1.2⟩)

/-- Discharges `KyberPreKeyMarkKitPlacedOk` for `cliPollKpkKitPlaced` from `RunHooksPlaced` and
`hRead`. -/
theorem cliPollKpk_markKitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    KyberPreKeyMarkKitPlacedOk A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
      (cliPollKpkBudgetEnv A.repAlloc F0 kpkId spkId kbk (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  markShim hblk := cliPollKpk_markShim_rocl mmpl gh W B F0 kpkId spkId kbk hh hblk
  markPoll hblk := cliPollKpk_markPoll_rocl mmpl gh W B F0 kpkId spkId kbk hh hRead hblk
  markFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_rocl_placed_ok hblk

private theorem cliPollPk_removeShim_placed_ok [LibsignalPlacement] {M : AllocCostModel}
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

private theorem cliPollPk_removeShim_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hblk : callerBlk < 619) :
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + pkKit.removeShimOff)
      (withLsRoCl lsmpl (kitPreKeyRemoveShimSpec M A lim pkKit)) := by
  intro pkKit
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 610)
    (cliPollPk_removeShim_placed_ok B F0 pkId hh.alloc) hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 610) _
  rw [BitVec.zero_add]
  exact hrocl

private theorem cliPollPk_removePoll_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hblk : callerBlk < 619) :
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + pkKit.removePollOff)
      (withLsRoCl lsmpl
        (kitPreKeyRemovePollSpecE M A lim pkKit
          (cliPollPkBudgetEnv A.repAlloc F0 pkId (cliKitStk B) ReadEnv))) := by
  intro pkKit
  let pkEnv := cliPollPkBudgetEnv A.repAlloc F0 pkId (cliKitStk B) ReadEnv
  let hhSkel := toSkeletonRunHooks hh
  have hDecimal := cliDecimal_placed_ok hhSkel
  have hGet := cliDirGet_placed_ok
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (fun _ hp => hp.2) hhSkel
    (subroutine_ok_withLsCodeRoLoaded_of_plain hRead) (by decide) (by decide)
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
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre4
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
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (cliKitStk B).pkRemovePoll) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hent0) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ans => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hrel, heq2⟩ => ?_
    rw [heq2]
    refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
    refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hmenv⟩ ?_
    exact Entails.trans (Entails.pure_right hinv.removePreKey (Entails.refl _))
      (Entails.of_eq (by ac_rfl))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- Discharges `PreKeyRemoveKitPlacedOk` for `cliPollPkKitPlaced` from `RunHooksPlaced` and
`hRead`. -/
theorem cliPollPk_removeKitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    PreKeyRemoveKitPlacedOk A lim
      (cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B))
      (cliPollPkBudgetEnv A.repAlloc F0 pkId (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  removeShim hblk := cliPollPk_removeShim_rocl mmpl gh W B F0 pkId hh hblk
  removePoll hblk := cliPollPk_removePoll_rocl mmpl gh W B F0 pkId hh hRead hblk
  removeFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_rocl_placed_ok hblk

/-! ## 3. Envelope & Outcome Bridges (`Matched` / `Kits` ↔ `ClosureStagesStmtPlacedBudget`) -/

private theorem sepWPp_map_post {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q1 Q2 Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hQ : ∀ sf Pf, Q1 sf Pf → Q2 sf Pf) (h : SepWPp prog ret s P Q1 Qp oom) :
    SepWPp prog ret s P Q2 Qp oom := fun R hm hL => by
  obtain ⟨sf, hsteps, hout⟩ := h R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, Pf, hmm, hq⟩ | hrest
  · exact Or.inl ⟨hpc, hrun, Pf, hmm, hQ sf Pf hq⟩
  · exact Or.inr hrest

private theorem stageP4MatchedBranchPlaced_of_matched [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {s0 s : State}
    {coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64}
    {opkHi kyberPreKeyId signedPreKeyId : BitVec 32} {pt : List (BitVec 8)}
    {peer : AddrGhost} {remoteIk : IdentityKey} {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {ss : Session (List (BitVec 8))} {sf : State} {Pf : SepProp}
    (h : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget.StageP4MatchedBranchPlaced
      A lim st0 kit kitEnv ikit ikitEnv encRecord s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt
      ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk sst0 ist0 ss sf Pf) :
    StageP4MatchedBranchPlaced A lim st0 kit kitEnv ikit ikitEnv encRecord s0 s coroPtr msgPtr
      outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt
      ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk sst0 ist0 ss sf Pf := by
  cases h with
  | ok c evs hevs hsave hstore htr hpost => exact .ok c evs hevs hsave hstore htr hpost
  | saveErr evs hevs hsave htr hpost => exact .saveErr evs hevs hsave htr hpost
  | storeErr c evs hevs hsave hstore htr hpost => exact .storeErr c evs hevs hsave hstore htr hpost

private theorem fitsEnv_step_of_pathA {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {pkKit : PreKeyStoreSpec A b} {pkKitEnv : PreKeyStoreBudgetEnv pkKit}
    {kpkKit : KyberPreKeyStoreSpec A b} {kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {pst0 : pkKit.PkState} {kst0 : kpkKit.KpkState}
    {rem : AddrVal} {remoteIk : IdentityKey}
    {opkId? : Option (BitVec 32)} {kyberPreKeyId signedPreKeyId : BitVec 32}
    {baseKey : PublicKey} {ss : Session (List (BitVec 8))}
    (h : FitsEnv M lim st
      (StageP4PathAEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 rem remoteIk opkId? kyberPreKeyId signedPreKeyId baseKey ss)) :
    FitsEnv M lim st
      (StageP4StepEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 opkId? rem remoteIk kyberPreKeyId signedPreKeyId baseKey
        ⟨some ss⟩) := by
  cases opkId? with
  | none =>
    have hopt : OptRemoveStepEnv pkKit pkKitEnv pst0 none [] := rfl
    refine h.mono fun evs hevs => ?_
    rcases hevs with hsave | ⟨_, _, rfl, hsave, hmark | ⟨_, _, rfl, hmark, hstore⟩⟩
    · exact Or.inl (SeqEnv.inl hsave)
    · exact Or.inr (Or.inl (SeqEnv.append hsave (SeqEnv.inl hmark)))
    · exact Or.inr (Or.inr (Or.inr
        (SeqEnv.append hsave
          (SeqEnv.append hmark
            (SeqEnv.append hopt (SeqEnv.inl hstore))))))
  | some opkId =>
    refine h.mono fun evs hevs => ?_
    rcases hevs with hsave | ⟨_, _, rfl, hsave, hmark |
        ⟨_, _, rfl, hmark, hrem | ⟨_, _, rfl, hrem, hstore⟩⟩⟩
    · exact Or.inl (SeqEnv.inl hsave)
    · exact Or.inr (Or.inl (SeqEnv.append hsave (SeqEnv.inl hmark)))
    · exact Or.inr (Or.inr (Or.inl (SeqEnv.append hsave (SeqEnv.append hmark (SeqEnv.inl hrem)))))
    · exact Or.inr (Or.inr (Or.inr
        (SeqEnv.append hsave
          (SeqEnv.append hmark
            (SeqEnv.append hrem (SeqEnv.inl hstore))))))

private theorem storeStepEnv_of_storeBranchEnv {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {pkKit : PreKeyStoreSpec A b} {pkKitEnv : PreKeyStoreBudgetEnv pkKit}
    {kpkKit : KyberPreKeyStoreSpec A b} {kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {pst0 : pkKit.PkState} {kst0 : kpkKit.KpkState}
    {rem : AddrVal} {remoteIk : IdentityKey}
    {opkId? : Option (BitVec 32)} {kyberPreKeyId signedPreKeyId : BitVec 32}
    {baseKey : PublicKey} {ss : Session (List (BitVec 8))} {evs : List AllocEvent}
    (hevs : StageP4StoreBranchEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
      sst0 ist0 pst0 kst0 opkId? rem remoteIk kyberPreKeyId signedPreKeyId baseKey ⟨some ss⟩ evs) :
    StageP4PathAStoreStepEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
      sst0 ist0 pst0 kst0 rem remoteIk opkId? kyberPreKeyId signedPreKeyId baseKey ss evs := by
  cases opkId? with
  | some opkId => exact hevs
  | none =>
    have hopt : OptRemoveStepEnv pkKit pkKitEnv pst0 none [] := rfl
    rcases hevs with hs | ⟨l1, _, rfl, hs, hm | ⟨l2, l3, rfl, hm, hst⟩⟩
    · exact SeqEnv.inl hs
    · exact SeqEnv.append hs (SeqEnv.inl hm)
    · exact SeqEnv.append hs (SeqEnv.append hm (SeqEnv.append hopt hst))

private theorem stageP4BranchPlaced_of_kits [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {pkKit : PreKeyStoreSpec A.repAlloc 0#64} {pkKitEnv : PreKeyStoreBudgetEnv pkKit}
    {kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64} {kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {s0 s : State}
    {coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64}
    {opkId? : Option (BitVec 32)} {kyberPreKeyId signedPreKeyId : BitVec 32}
    {pt : List (BitVec 8)} {peer : AddrGhost} {remoteIk : IdentityKey} {baseKey : PublicKey}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState} {pst0 : pkKit.PkState} {kst0 : kpkKit.KpkState}
    {ss : Session (List (BitVec 8))} {sf : State} {Pf : SepProp}
    (h : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNonePlacedBudget.StageP4BranchPlaced
      A lim st0 kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv encRecord s0 s coroPtr
      msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
      kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt peer
      remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf) :
    StageP4BranchPlaced A lim st0 kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
      encRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId
      signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf := by
  cases opkId? <;> cases h with
  | ok c evs hevs hsave hmark hrem hstore htr hpost =>
    exact .ok c evs (storeStepEnv_of_storeBranchEnv hevs) hsave hmark hrem hstore htr hpost
  | saveErr evs hevs hsave htr hpost =>
    exact .saveErr evs hevs hsave htr hpost
  | markErr c e evs hevs hsave hmark htr hpost =>
    exact .markErr c e evs hevs hsave hmark htr hpost
  | removeErr opkId c e evs hopk hevs hsave hmark hrem htr hpost =>
    exact .removeErr opkId c e evs hopk hevs hsave hmark hrem htr hpost
  | storeErr c evs hevs hsave hmark hrem hstore htr hpost =>
    exact .storeErr c evs (storeStepEnv_of_storeBranchEnv hevs) hsave hmark hrem hstore htr hpost

/-! ## 4. Parametric-Kit & Concrete CLI Stage-P4 Instantiation Theorems -/

/-- Parametric-kit budget-threaded matched-session Path B Stage P4 (`+0x34dc → s0.readReg64.x30`)
on `dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem stageP4Matched_placed_of_kits [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    {kitEnv : SessionStoreBudgetEnv (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))}
    {ikitEnv : IdentityStoreBudgetEnv (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSkit : SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      kitEnv scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hIkit : IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      ikitEnv (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
      (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
      (remoteIk : IdentityKey) (sst0 : kit.StoreState) (ist0 : ikit.IdState)
      (g : RecordGhost) (G : SessionGhost)
      (ss : Session (List (BitVec 8))),
      SessionExtraRel G ss → kit.RecOk ⟨some ss⟩ →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      FitsEnv M lim st_b
        (StageP4MatchedEnv kit kitEnv ikit ikitEnv sst0 ist0 peer.val remoteIk ss) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 →
      FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
        (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x34dc#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (stageP4MatchedPrePlaced A lim st_b kit ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr
          remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk sst0 ist0 g G ss.state)
        (fun sf Pf =>
          Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4MatchedBranchPlaced A lim st_b kit kitEnv ikit ikitEnv encodeRecord
            s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
            kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId
            pt peer remoteIk sst0 ist0 ss sf Pf)
        (fun _ _ => False) := by
  intro σ kit ikit st_b s0 s
    coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId b_2c0 pt
    remoteIk sst0 ist0 g G ss hex hrec hka hia hfits hpt1 hpt2 hpt3 hstk
    hfs hcro hpc hrun hsp htr hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  have hext : Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      cliGhostExterns gh (cliExternsPlaced mmpl W) :=
    withPanics_cliGhostExterns_eq mmpl gh W
  have hdealloc : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_ultra_of_mem hh.codecHooks.dealloc (by decide)
  have hDrop : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
    drop_session_structure4_placed_ok_at
      (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
      hh.codecHooks.dealloc (by decide)
  have hSvt : SessionOnlyVtablesPlacedOk kit :=
    cliPollSess_vtablesPlacedOk F0 scopeKit peer σ hDropNz
  have hIvt : IdentityVtablesPlacedOk ikit :=
    cliPollId_vtablesPlacedOk F0 peer σ hDropNz
  have hwp0 := stageP4_matched_placed_ok A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Scope := scopeKit) (encRecord := encodeRecord) kit kitEnv ikit ikitEnv
  rw [hext] at hwp0
  have hwp := hwp0 hdealloc hDrop hSkit hSvt hIkit hIvt
    st_b s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId b_2c0 pt
    peer remoteIk sst0 ist0 g G ss hex hrec hka hia hfits hpt1 hpt2 hpt3 hstk
    hfs hcro hpc hrun hsp htr hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  exact sepWPp_map_post
    (fun _ _ ⟨hs1, hs2, hs3, hs4, hs5, hbr⟩ =>
      ⟨hs1, hs2, hs3, hs4, hs5, stageP4MatchedBranchPlaced_of_matched hbr⟩)
    hwp

/-- Concrete CLI-instantiated budget-threaded Path B Stage P4 statement (`M4`) binding `kitEnv` to
`cliPollSessBudgetEnv` and `ikitEnv` to `cliPollIdBudgetEnv`. -/
def StageP4MatchedCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let kitEnv := cliPollSessBudgetEnv A.repAlloc F0 peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc F0 peer σ ReadEnv
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
      (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
      (remoteIk : IdentityKey) (sst0 : kit.StoreState) (ist0 : ikit.IdState)
      (g : RecordGhost) (G : SessionGhost)
      (ss : Session (List (BitVec 8))),
      SessionExtraRel G ss → kit.RecOk ⟨some ss⟩ →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      FitsEnv M lim st_b
        (StageP4MatchedEnv kit kitEnv ikit ikitEnv sst0 ist0 peer.val remoteIk ss) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 →
      FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
        (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x34dc#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (stageP4MatchedPrePlaced A lim st_b kit ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr
          remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk sst0 ist0 g G ss.state)
        (fun sf Pf =>
          Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4MatchedBranchPlaced A lim st_b kit kitEnv ikit ikitEnv encodeRecord
            s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
            kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId
            pt peer remoteIk sst0 ist0 ss sf Pf)
        (fun _ _ => False)

/-- Instantiates `StageP4MatchedCliPlacedStmt` via `stageP4_matched_placed_ok`. -/
theorem stageP4Matched_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP4MatchedCliPlacedStmt :=
  fun mmpl gh W B F0 peer hh hRead hDeser =>
    stageP4Matched_placed_of_kits mmpl gh W B F0 peer hDropNz hh
      (cliPollSess_kitPlacedOkSE mmpl gh W B F0 peer hDropNz hh hRead hDeser)
      (cliPollId_kitPlacedOkI mmpl gh W B F0 peer hDropNz hh hRead)

/-- SeqFree (`cliPollSessSeqFreeBudgetEnv`) Path B Stage P4 statement (`M4`). -/
def StageP4MatchedSeqFreeCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let kitEnv := cliPollSessSeqFreeBudgetEnv A.repAlloc F0 peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc F0 peer σ ReadEnv
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
      (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
      (remoteIk : IdentityKey) (sst0 : kit.StoreState) (ist0 : ikit.IdState)
      (g : RecordGhost) (G : SessionGhost)
      (ss : Session (List (BitVec 8))),
      SessionExtraRel G ss → kit.RecOk ⟨some ss⟩ →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      FitsEnv M lim st_b
        (StageP4MatchedEnv kit kitEnv ikit ikitEnv sst0 ist0 peer.val remoteIk ss) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 →
      FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
        (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x34dc#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (stageP4MatchedPrePlaced A lim st_b kit ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr
          remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk sst0 ist0 g G ss.state)
        (fun sf Pf =>
          Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4MatchedBranchPlaced A lim st_b kit kitEnv ikit ikitEnv encodeRecord
            s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
            kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId
            pt peer remoteIk sst0 ist0 ss sf Pf)
        (fun _ _ => False)

/-- Instantiates `StageP4MatchedSeqFreeCliPlacedStmt` via `stageP4_matched_placed_ok`. -/
theorem stageP4Matched_seqFree_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP4MatchedSeqFreeCliPlacedStmt :=
  fun mmpl gh W B F0 peer hh hRead hDeser =>
    stageP4Matched_placed_of_kits mmpl gh W B F0 peer hDropNz hh
      (cliPollSess_seqFreeKitPlacedOkSE mmpl gh W B F0 peer hDropNz hh hRead hDeser)
      (cliPollId_kitPlacedOkI mmpl gh W B F0 peer hDropNz hh hRead)

/-- Parametric-kit budget-threaded Path A 4-kit Stage P4 (`+0x34dc → s0.readReg64.x30`) on
`dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem stageP4PathA_placed_of_kits [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    {kitEnv : SessionStoreBudgetEnv (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))}
    {ikitEnv : IdentityStoreBudgetEnv (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))}
    {pkKitEnv : PreKeyStoreBudgetEnv (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))}
    {kpkKitEnv : KyberPreKeyStoreBudgetEnv
      (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSkit : SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      kitEnv scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hIkit : IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      ikitEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : PreKeyRemoveKitPlacedOk A lim
      (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))
      pkKitEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : KyberPreKeyMarkKitPlacedOk A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
      kpkKitEnv (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk σ
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
      (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
      (b_2c0 : BitVec 8) (pt : List (BitVec 8))
      (remoteIk : IdentityKey) (baseKey : PublicKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState)
      (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
      (G : SessionGhost) (ss : Session (List (BitVec 8))),
      prevStatesPtr ≠ 0#64 →
      SessionExtraRel G ss → kit.RecOk ⟨some ss⟩ →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
      (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
      FitsEnv M lim st_b
        (StageP4PathAEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
          sst0 ist0 pst0 kst0 peer.val remoteIk opkId? kyberPreKeyId signedPreKeyId baseKey ss) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 →
      FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
        (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x34dc#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (stageP4PrePlaced A lim st_b kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt
          peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss.state)
        (fun sf Pf =>
          Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4BranchPlaced A lim st_b kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
            encodeRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
            idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkId?
            kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf)
        (fun _ _ => False) := by
  intro σ kit ikit pkKit kpkKit st_b s0 s
    coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    opkId? kyberPreKeyId signedPreKeyId b_2c0 pt remoteIk baseKey sst0 ist0 pst0 kst0 G ss
    hprev_nz hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok hfits
    hpt_le hcap_lt hptr_nz hsp_ub hfs hcro hpc hrun hsp_align _htr_pfx
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  have hdealloc : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_ultra_of_mem hh.codecHooks.dealloc (by decide)
  have hDrop : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
    drop_session_structure4_placed_ok_at
      (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
      hh.codecHooks.dealloc (by decide)
  have hSvt : SessionOnlyVtablesPlacedOk kit :=
    cliPollSess_vtablesPlacedOk F0 scopeKit peer σ hDropNz
  have hIvt : IdentityVtablesPlacedOk ikit :=
    cliPollId_vtablesPlacedOk F0 peer σ hDropNz
  have hPkVt : PreKeyVtablesPlacedOk pkKit :=
    cliPollPk_vtablesPlacedOk F0 pid σ hDropNz
  have hKpkVt : KyberPreKeyVtablesPlacedOk kpkKit :=
    cliPollKpk_vtablesPlacedOk F0 kpkId spkId kbk σ hDropNz
  refine sepWPp_map_post ?_
    (stageP4_v1_vregs_mark_remove_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))
      scopeKit encodeRecord kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
      hdealloc hDrop hSkit hSvt hIkit hIvt hPkKit hPkVt hKpkKit hKpkVt
      st_b s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId
      signedPreKeyId b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
      hprev_nz hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok (fitsEnv_step_of_pathA hfits)
      hpt_le hcap_lt hptr_nz hsp_ub hfs hcro hpc hrun hsp_align
      hx19 hx24 hx25 hx26 hx27 hx28 hvregs)
  rintro sf Pf ⟨hst, hspf, hcsf, hvregsf, hcrof, hbr⟩
  exact ⟨hst, hspf, hcsf, hvregsf, hcrof, stageP4BranchPlaced_of_kits hbr⟩

/-- Concrete CLI-instantiated budget-threaded Path A 4-kit Stage P4 statement binding the four
store budget envelopes to `cliPollSessBudgetEnv`, `cliPollIdBudgetEnv`, `cliPollPkBudgetEnv`, and
`cliPollKpkBudgetEnv`. -/
def StageP4PathACliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk σ
    let kitEnv := cliPollSessBudgetEnv A.repAlloc F0 peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc F0 peer σ ReadEnv
    let pkKitEnv := cliPollPkBudgetEnv A.repAlloc F0 pid σ ReadEnv
    let kpkKitEnv := cliPollKpkBudgetEnv A.repAlloc F0 kpkId spkId kbk σ ReadEnv
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
      (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
      (b_2c0 : BitVec 8) (pt : List (BitVec 8))
      (remoteIk : IdentityKey) (baseKey : PublicKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState)
      (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
      (G : SessionGhost) (ss : Session (List (BitVec 8))),
      prevStatesPtr ≠ 0#64 →
      SessionExtraRel G ss → kit.RecOk ⟨some ss⟩ →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
      (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
      FitsEnv M lim st_b
        (StageP4PathAEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
          sst0 ist0 pst0 kst0 peer.val remoteIk opkId? kyberPreKeyId signedPreKeyId baseKey ss) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 →
      FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
        (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x34dc#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (stageP4PrePlaced A lim st_b kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt
          peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss.state)
        (fun sf Pf =>
          Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4BranchPlaced A lim st_b kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
            encodeRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
            idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkId?
            kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf)
        (fun _ _ => False)

/-- Instantiates `StageP4PathACliPlacedStmt` via `stageP4_v1_vregs_mark_remove_placed_ok`. -/
theorem stageP4PathA_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP4PathACliPlacedStmt :=
  fun mmpl gh W B F0 peer pid kpkId spkId kbk hh hRead hDeser =>
    stageP4PathA_placed_of_kits mmpl gh W B F0 peer pid kpkId spkId kbk hDropNz hh
      (cliPollSess_kitPlacedOkSE mmpl gh W B F0 peer hDropNz hh hRead hDeser)
      (cliPollId_kitPlacedOkI mmpl gh W B F0 peer hDropNz hh hRead)
      (cliPollPk_removeKitPlacedOk mmpl gh W B F0 pid hDropNz hh hRead)
      (cliPollKpk_markKitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hRead)

/-- SeqFree (`cliPollSessSeqFreeBudgetEnv`) Path A 4-kit Stage P4 statement. -/
def StageP4PathASeqFreeCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk σ
    let kitEnv := cliPollSessSeqFreeBudgetEnv A.repAlloc F0 peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc F0 peer σ ReadEnv
    let pkKitEnv := cliPollPkBudgetEnv A.repAlloc F0 pid σ ReadEnv
    let kpkKitEnv := cliPollKpkBudgetEnv A.repAlloc F0 kpkId spkId kbk σ ReadEnv
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
      (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
      (b_2c0 : BitVec 8) (pt : List (BitVec 8))
      (remoteIk : IdentityKey) (baseKey : PublicKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState)
      (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
      (G : SessionGhost) (ss : Session (List (BitVec 8))),
      prevStatesPtr ≠ 0#64 →
      SessionExtraRel G ss → kit.RecOk ⟨some ss⟩ →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
      (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
      FitsEnv M lim st_b
        (StageP4PathAEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
          sst0 ist0 pst0 kst0 peer.val remoteIk opkId? kyberPreKeyId signedPreKeyId baseKey ss) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 →
      FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
        (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x34dc#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (stageP4PrePlaced A lim st_b kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt
          peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss.state)
        (fun sf Pf =>
          Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4BranchPlaced A lim st_b kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
            encodeRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
            idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkId?
            kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf)
        (fun _ _ => False)

/-- Instantiates `StageP4PathASeqFreeCliPlacedStmt` via `stageP4_v1_vregs_mark_remove_placed_ok`. -/
theorem stageP4PathA_seqFree_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP4PathASeqFreeCliPlacedStmt :=
  fun mmpl gh W B F0 peer pid kpkId spkId kbk hh hRead hDeser =>
    stageP4PathA_placed_of_kits mmpl gh W B F0 peer pid kpkId spkId kbk hDropNz hh
      (cliPollSess_seqFreeKitPlacedOkSE mmpl gh W B F0 peer hDropNz hh hRead hDeser)
      (cliPollId_kitPlacedOkI mmpl gh W B F0 peer hDropNz hh hRead)
      (cliPollPk_removeKitPlacedOk mmpl gh W B F0 pid hDropNz hh hRead)
      (cliPollKpk_markKitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hRead)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
