/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1PlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable CLI Poll Stage P4 Over-Path (`Path C`) Instantiation

Budget-threaded `[LibsignalPlacement]` instantiation of Stage P4 on overwrite path `Path C` under
`RustCliAllocBudget M`, discharging `SessionPrev1KitPlacedOkSE` for `cliPollSessPrev1KitPlaced`
and instantiating `StageP4Prev1CliPlacedStmt` and `StageP4Prev1VRegsPlacedStmt`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (IdentityKey PublicKey)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ
   withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (ClosureCalleeSavedP4)
open CryptoVerification.E2E.Record.Serialization (CanonSession)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
  (SessionExtraRel stageP4CallStack stageP4EnvOk stageP4Quiet)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
  (StorePrev1Ops encodeRecordPrev1 sessionRecordPrevAt)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost protocolAddressAt)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsAt FsFiles IdentityVtablesPlacedOk KyberPreKeyVtablesPlacedOk LibsignalCodeRoLoaded
   PreKeyVtablesPlacedOk SessionOnlyVtablesPlacedOk extract_withLsCodeRoLoaded
   ls_subroutine_ok_rocl_of_block storePollPlacedOutAt withEnvPre withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsDropOffPlaced lsDropOffPlaced_eq lsReadFileSym)
open CryptoVerification.SignalSession.Cli
  (addressText cliIdentityVtSym cliSessionVtSym dirAt sessStoreBoxAt)
open CryptoVerification.SignalSession.Cli.KitInst (cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_570)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.StoreSessionPrev1
  (SessStorePollPrev1Ghost changedLt_put_self)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (CliSessPrev1Inv cliKitStk cliPollIdKitPlaced cliPollId_vtablesPlacedOk cliPollKpkKitPlaced
   cliPollKpk_vtablesPlacedOk cliPollPkKitPlaced cliPollPk_vtablesPlacedOk cliPollSessKit
   cliPollSessPrev1Kit cliPollSessPrev1KitPlaced cliPollStorePrev1OpsPlaced cliSessPrev1StoreAt
   dpPollEntryPlaced dpPollProgPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (KyberPreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (IdentityStoreKitPlacedOkI)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (PreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (kitStoreShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (dropSessionStructureLocal2Spec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
  (drop_session_structure4_placed_ok_at)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget
  (KyberPreKeyMarkKitPlacedOk)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget
  (PreKeyRemoveKitPlacedOk)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget
  (SerializePrev1Env)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgePlacedBudget
  (SerializePrev1EnvX serializePrev1Body_placed_lscro_of_serContractsX
   serializePrev1Body_seqFree_placed_lscro_of_serContractsX storeSerializePrev1BodySpecX_eq)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget
  (StageP4Prev1BranchPlaced StageP4Prev1ExitEnv fitsEnv_prev1Step_of_exit stageP4Prev1PrePlaced)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1PlacedBudget
  (stageP4_prev1_vregs_mark_remove_placed_ok)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlacedBudget
  (SessionPrev1KitPlacedOkSE StorePrev1BudgetEnv kitStorePollPrev1PlacedSpec
   kitStorePollPrev1PlacedSpecE)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudget (AddrTextEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliAddrText_placed_ok cliDirPut_placed_ok cliSessFutDrop_rocl_placed_ok
   cliSessStoreShim_rocl_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
  (CliStageP4Prev1Envs StageP4Prev1CliPlacedStmt StageP4Prev1SeqFreeCliPlacedStmt
   StageP4Prev1VRegsPlacedStmt cliPollSessPrev1BudgetEnv cliPollSessPrev1SeqFreeBudgetEnv
   cliPollSessPrev1SeqFreeStorePollEnv cliPollSessPrev1StorePollEnv cliPollStageP4Prev1Envs
   cliPollStageP4Prev1SeqFreeEnvs stageP4Prev1SeqFreeVRegsPlaced_of_cli
   stageP4Prev1VRegsPlaced_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
  (cliPollId_kitPlacedOkI cliPollKpk_markKitPlacedOk cliPollPk_removeKitPlacedOk
   cliSerContractsX_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1Budget (CliStorePollPrev1Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1PlacedBudget
  (serializePrev1BodySpecX sessStorePollPrev1SpecPlaced sessStorePollPrev1_placed_ok_of_deps)

/-! ## 1. Placed `Prev1` Vtable, `serializePrev1Body`, & `SessionPrev1KitPlacedOkSE` Instantiation -/

abbrev cliPollSess_prev1VtablesPlacedOk :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSess_prev1VtablesPlacedOk

private theorem toSkeletonRunHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

/-- Caller-block-polymorphic `withLsCodeRoLoaded` form of `serializePrev1BodySpecX` at
`cliGhostExterns gh (cliExternsPlaced mmpl W)` discharged from `RunHooksPlaced`. -/
theorem cliSerializePrev1Body_placed_lscro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecX A lim SerializePrev1EnvX)) := by
  rw [storeSerializePrev1BodySpecX_eq]
  exact serializePrev1Body_placed_lscro_of_serContractsX
    (cliSerContractsX_placed_ok mmpl gh W hh)
    hblk

/-- Caller-block-polymorphic `withLsCodeRoLoaded` form of `serializePrev1BodySpecX` at SeqFree
`SerializePrev1Env` (`= SerializePrev1SeqFreeEnv`) discharged from `RunHooksPlaced`. -/
theorem cliSerializePrev1Body_seqFree_placed_lscro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecX A lim SerializePrev1Env)) := by
  rw [storeSerializePrev1BodySpecX_eq]
  exact serializePrev1Body_seqFree_placed_lscro_of_serContractsX
    (cliSerContractsX_placed_ok mmpl gh W hh)
    hblk

theorem cliPollSess_prev1StoreShim_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let kit := cliPollSessPrev1KitPlaced A.repAlloc F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + kit.storeShimOff)
      (withLsRoCl lsmpl (kitStoreShimSpec M A lim kit)) := by
  intro kit
  exact cliSessStoreShim_rocl_placed_ok
    (rd := cliIo.rd) (F0 := F0) (pathOk := cliWrOk) (Scope := scopeKit) (peer := peer)
    (s1 := (cliKitStk B).sessLoadShim) (s2 := (cliKitStk B).sessLoadPoll)
    (s3 := (cliKitStk B).sessStoreShim) (s4 := (cliKitStk B).sessStorePoll)
    (vtSym := cliSessionVtSym) (idVtSym := cliIdentityVtSym)
    hh.alloc (Nat.le_refl _) hblk

theorem cliPollSess_prev1StorePoll_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let kit := cliPollSessPrev1KitPlaced A.repAlloc F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + kit.storePollOff)
      (withLsRoCl lsmpl
        (kitStorePollPrev1PlacedSpecE M A lim kit cliPollStorePrev1OpsPlaced
          (cliPollSessPrev1BudgetEnv A.repAlloc F0 peer (cliKitStk B)))) := by
  intro kit
  let hhSkel := toSkeletonRunHooks hh
  have hAddr := cliAddrText_placed_ok hhSkel
  have hSer := cliSerializePrev1Body_placed_lscro mmpl gh W hh
    (callerProg := lsProg_570 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (callerBlk := 570) (by decide)
  have hPut := cliDirPut_placed_ok hhSkel
  have h570 := sessStorePollPrev1_placed_ok_of_deps
    hAddr hSer hPut (stk := (cliKitStk B).sessStorePoll) (by dsimp only [cliKitStk]; decide)
  have h570_kit : subroutine_ok (lsProg_570 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 570)
      (withLsCodeRoLoaded lsmpl
        (kitStorePollPrev1PlacedSpecE M A lim kit cliPollStorePrev1OpsPlaced
          (cliPollSessPrev1BudgetEnv A.repAlloc F0 peer (cliKitStk B)))) := by
    refine subroutine_ok.of_codeLoaded fun ⟨call, self, d, st⟩ R s0 hpc hrun hpre hsp _ => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitStorePollPrev1PlacedSpecE, withEnvPre, kitStorePollPrev1PlacedSpec,
      kit, cliPollSessPrev1KitPlaced, cliPollSessPrev1Kit, cliPollSessKit, cliSessionStoreSpec,
      cliSessPrev1StoreAt, cliPollStorePrev1OpsPlaced, cliPollSessPrev1BudgetEnv] at hpre0
    have hpre' : s0.mem ⊨
        ⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          (CanonSession call.G call.sess ∧
            (encodeRecordPrev1 call.sess call.enc).length < 2 ^ 32) ∧
          call.addr.val = peer.val ∧
          FitsEnv M lim st
            (cliPollSessPrev1StorePollEnv d call.addr.val call.G call.sess call.enc)⌝ ∗
        (⌜CliSessPrev1Inv peer d⌝ ∗
        (sessStoreBoxAt call.fut self call.addrA call.recA 0#8 ∗
          dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
          protocolAddressAt A.repAlloc call.addr call.addrA ∗
          sessionRecordPrevAt A.repAlloc call.recA ⟨call.prevCap, call.prevPtr, some call.G⟩
            [call.enc] ⟨some call.sess⟩ ∗
          A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).sessStorePoll ∗ R))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre0
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨_hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'
    obtain ⟨⟨hx0, hx8, ⟨hcan, hlen⟩, haddr, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    let x : SessStorePollPrev1Ghost :=
      ⟨call.fut, self, call.out, call.addrA, call.addr, call.recA,
       call.prevCap, call.prevPtr, call.G, call.sess, call.enc, d⟩
    have hfit_hop : FitsEnv M lim st
        (CliStorePollPrev1Env (AddrTextEnv DecimalEnv) SerializePrev1EnvX DirPutEnv x) := hfit
    have hm_hop : s0.mem ⊨
        (sessStorePollPrev1SpecPlaced A lim
          (CliStorePollPrev1Env (AddrTextEnv DecimalEnv) SerializePrev1EnvX DirPutEnv)
          (cliKitStk B).sessStorePoll).pre (x, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [x]
      have h1 : s0.mem ⊨
          ⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
            call.addr.name.bytes.length < 2 ^ 32 ∧
            CanonSession call.G call.sess ∧
            (encodeRecordPrev1 call.sess call.enc).length < 2 ^ 32 ∧
            d.changed.length < 2 ^ 32 ∧
            FitsEnv M lim st
              (CliStorePollPrev1Env (AddrTextEnv DecimalEnv) SerializePrev1EnvX DirPutEnv x)⌝ ∗
          (sessStoreBoxAt call.fut self call.addrA call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.addr call.addrA ∗
            sessionRecordPrevAt A.repAlloc call.recA ⟨call.prevCap, call.prevPtr, some call.G⟩
              [call.enc] ⟨some call.sess⟩ ∗
            A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).sessStorePoll ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hname ▸ hinv.nameLt, hcan, hlen, hinv.changedLt.1, hfit_hop⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h570.mono_outcome (x, st) R s0 hpc hrun hm_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [sessStorePollPrev1SpecPlaced, withLsCodeRoLoaded, x] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, ⟨htr, hevs⟩, hm⟩ := hpost
      have hevs_kit :
          cliPollSessPrev1StorePollEnv d call.addr.val call.G call.sess call.enc evs := hevs
      have hinv_put : CliSessPrev1Inv peer
          (d.put (addressText call.addr.val) (encodeRecordPrev1 call.sess call.enc)) := by
        rw [haddr]
        exact ⟨hinv.nameLt,
          changedLt_put_self (encodeRecordPrev1 call.sess call.enc) hinv.changedLt⟩
      dsimp only [withLsCodeRoLoaded, kitStorePollPrev1PlacedSpecE, withEnvPre,
        kitStorePollPrev1PlacedSpec, kit, cliPollSessPrev1KitPlaced, cliPollSessPrev1Kit,
        cliPollSessKit, cliSessionStoreSpec, cliSessPrev1StoreAt, cliPollStorePrev1OpsPlaced,
        cliPollSessPrev1BudgetEnv]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.ok (), evs, ?_⟩
      dsimp only [storePollPlacedOutAt]
      have hgoal : sf.mem ⊨
          ⌜(Except.ok () : Except Unit Unit) = .ok () ∧ sf.trace = s0.trace ++ [] ∧
            cliPollSessPrev1StorePollEnv d call.addr.val call.G call.sess call.enc evs⌝ ∗
          (⌜CliSessPrev1Inv peer
              (d.put (addressText call.addr.val) (encodeRecordPrev1 call.sess call.enc))⌝ ∗
            (sessStoreBoxAt call.fut self call.addrA call.recA 1#8 ∗
              dirAt A.repAlloc self
                (d.put (addressText call.addr.val) (encodeRecordPrev1 call.sess call.enc)) ∗
              (call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (call.out + 8#64) 40 ∗
              protocolAddressAt A.repAlloc call.addr call.addrA ∗
              sessionRecordPrevAt A.repAlloc call.recA ⟨call.prevCap, call.prevPtr, some call.G⟩
                [call.enc] ⟨some call.sess⟩ ∗
              A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp (cliKitStk B).sessStorePoll ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨rfl, by rw [List.append_nil]; exact htr, hevs_kit⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv_put, Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr (Or.inl hex))
    · exact Or.inr (Or.inr (Or.inr hoom))
  change subroutine_ok callerProg (0#64 + lsmpl.base 570) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 570)
    h570_kit hblk (by decide) (by decide)

/-- Discharges `SessionPrev1KitPlacedOkSE` for `cliPollSessPrev1KitPlaced` under
`cliPollSessPrev1BudgetEnv` from `RunHooksPlaced` and `lsmpl.base 547 ≠ 0#64`. -/
theorem cliPollSess_prev1KitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    SessionPrev1KitPlacedOkSE A lim
      (cliPollSessPrev1KitPlaced A.repAlloc F0 peer (cliKitStk B))
      cliPollStorePrev1OpsPlaced
      (cliPollSessPrev1BudgetEnv A.repAlloc F0 peer (cliKitStk B))
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  storeShim hblk := cliPollSess_prev1StoreShim_rocl mmpl gh W B F0 peer hh hblk
  storePollPrev1 hblk := cliPollSess_prev1StorePoll_rocl mmpl gh W B F0 peer hh hblk
  storeFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliSessFutDrop_rocl_placed_ok hblk

theorem cliPollSess_prev1SeqFreeStorePoll_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let kit := cliPollSessPrev1KitPlaced A.repAlloc F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + kit.storePollOff)
      (withLsRoCl lsmpl
        (kitStorePollPrev1PlacedSpecE M A lim kit cliPollStorePrev1OpsPlaced
          (cliPollSessPrev1SeqFreeBudgetEnv A.repAlloc F0 peer (cliKitStk B)))) := by
  intro kit
  let hhSkel := toSkeletonRunHooks hh
  have hAddr := cliAddrText_placed_ok hhSkel
  have hSer := cliSerializePrev1Body_seqFree_placed_lscro mmpl gh W hh
    (callerProg := lsProg_570 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (callerBlk := 570) (by decide)
  have hPut := cliDirPut_placed_ok hhSkel
  have h570 := sessStorePollPrev1_placed_ok_of_deps
    hAddr hSer hPut (stk := (cliKitStk B).sessStorePoll) (by dsimp only [cliKitStk]; decide)
  have h570_kit : subroutine_ok (lsProg_570 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 570)
      (withLsCodeRoLoaded lsmpl
        (kitStorePollPrev1PlacedSpecE M A lim kit cliPollStorePrev1OpsPlaced
          (cliPollSessPrev1SeqFreeBudgetEnv A.repAlloc F0 peer (cliKitStk B)))) := by
    refine subroutine_ok.of_codeLoaded fun ⟨call, self, d, st⟩ R s0 hpc hrun hpre hsp _ => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitStorePollPrev1PlacedSpecE, withEnvPre, kitStorePollPrev1PlacedSpec,
      kit, cliPollSessPrev1KitPlaced, cliPollSessPrev1Kit, cliPollSessKit, cliSessionStoreSpec,
      cliSessPrev1StoreAt, cliPollStorePrev1OpsPlaced, cliPollSessPrev1SeqFreeBudgetEnv] at hpre0
    have hpre' : s0.mem ⊨
        ⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          (CanonSession call.G call.sess ∧
            (encodeRecordPrev1 call.sess call.enc).length < 2 ^ 32) ∧
          call.addr.val = peer.val ∧
          FitsEnv M lim st
            (cliPollSessPrev1SeqFreeStorePollEnv d call.addr.val call.G call.sess call.enc)⌝ ∗
        (⌜CliSessPrev1Inv peer d⌝ ∗
        (sessStoreBoxAt call.fut self call.addrA call.recA 0#8 ∗
          dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
          protocolAddressAt A.repAlloc call.addr call.addrA ∗
          sessionRecordPrevAt A.repAlloc call.recA ⟨call.prevCap, call.prevPtr, some call.G⟩
            [call.enc] ⟨some call.sess⟩ ∗
          A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).sessStorePoll ∗ R))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre0
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨_hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'
    obtain ⟨⟨hx0, hx8, ⟨hcan, hlen⟩, haddr, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    let x : SessStorePollPrev1Ghost :=
      ⟨call.fut, self, call.out, call.addrA, call.addr, call.recA,
       call.prevCap, call.prevPtr, call.G, call.sess, call.enc, d⟩
    have hfit_hop : FitsEnv M lim st
        (CliStorePollPrev1Env (AddrTextEnv DecimalEnv) SerializePrev1Env DirPutEnv x) := hfit
    have hm_hop : s0.mem ⊨
        (sessStorePollPrev1SpecPlaced A lim
          (CliStorePollPrev1Env (AddrTextEnv DecimalEnv) SerializePrev1Env DirPutEnv)
          (cliKitStk B).sessStorePoll).pre (x, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [x]
      have h1 : s0.mem ⊨
          ⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
            call.addr.name.bytes.length < 2 ^ 32 ∧
            CanonSession call.G call.sess ∧
            (encodeRecordPrev1 call.sess call.enc).length < 2 ^ 32 ∧
            d.changed.length < 2 ^ 32 ∧
            FitsEnv M lim st
              (CliStorePollPrev1Env (AddrTextEnv DecimalEnv) SerializePrev1Env DirPutEnv x)⌝ ∗
          (sessStoreBoxAt call.fut self call.addrA call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.addr call.addrA ∗
            sessionRecordPrevAt A.repAlloc call.recA ⟨call.prevCap, call.prevPtr, some call.G⟩
              [call.enc] ⟨some call.sess⟩ ∗
            A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).sessStorePoll ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hname ▸ hinv.nameLt, hcan, hlen, hinv.changedLt.1, hfit_hop⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h570.mono_outcome (x, st) R s0 hpc hrun hm_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [sessStorePollPrev1SpecPlaced, withLsCodeRoLoaded, x] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, ⟨htr, hevs⟩, hm⟩ := hpost
      have hevs_kit :
          cliPollSessPrev1SeqFreeStorePollEnv d call.addr.val call.G call.sess call.enc evs := hevs
      have hinv_put : CliSessPrev1Inv peer
          (d.put (addressText call.addr.val) (encodeRecordPrev1 call.sess call.enc)) := by
        rw [haddr]
        exact ⟨hinv.nameLt,
          changedLt_put_self (encodeRecordPrev1 call.sess call.enc) hinv.changedLt⟩
      dsimp only [withLsCodeRoLoaded, kitStorePollPrev1PlacedSpecE, withEnvPre,
        kitStorePollPrev1PlacedSpec, kit, cliPollSessPrev1KitPlaced, cliPollSessPrev1Kit,
        cliPollSessKit, cliSessionStoreSpec, cliSessPrev1StoreAt, cliPollStorePrev1OpsPlaced,
        cliPollSessPrev1SeqFreeBudgetEnv]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.ok (), evs, ?_⟩
      dsimp only [storePollPlacedOutAt]
      have hgoal : sf.mem ⊨
          ⌜(Except.ok () : Except Unit Unit) = .ok () ∧ sf.trace = s0.trace ++ [] ∧
            cliPollSessPrev1SeqFreeStorePollEnv d call.addr.val call.G call.sess call.enc evs⌝ ∗
          (⌜CliSessPrev1Inv peer
              (d.put (addressText call.addr.val) (encodeRecordPrev1 call.sess call.enc))⌝ ∗
            (sessStoreBoxAt call.fut self call.addrA call.recA 1#8 ∗
              dirAt A.repAlloc self
                (d.put (addressText call.addr.val) (encodeRecordPrev1 call.sess call.enc)) ∗
              (call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (call.out + 8#64) 40 ∗
              protocolAddressAt A.repAlloc call.addr call.addrA ∗
              sessionRecordPrevAt A.repAlloc call.recA ⟨call.prevCap, call.prevPtr, some call.G⟩
                [call.enc] ⟨some call.sess⟩ ∗
              A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp (cliKitStk B).sessStorePoll ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨rfl, by rw [List.append_nil]; exact htr, hevs_kit⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv_put, Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr (Or.inl hex))
    · exact Or.inr (Or.inr (Or.inr hoom))
  change subroutine_ok callerProg (0#64 + lsmpl.base 570) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 570)
    h570_kit hblk (by decide) (by decide)

/-- Discharges `SessionPrev1KitPlacedOkSE` for `cliPollSessPrev1KitPlaced` under SeqFree
`cliPollSessPrev1SeqFreeBudgetEnv` (`SerializePrev1Env`) from `RunHooksPlaced` and
`lsmpl.base 547 ≠ 0#64`. -/
theorem cliPollSess_prev1SeqFreeKitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    SessionPrev1KitPlacedOkSE A lim
      (cliPollSessPrev1KitPlaced A.repAlloc F0 peer (cliKitStk B))
      cliPollStorePrev1OpsPlaced
      (cliPollSessPrev1SeqFreeBudgetEnv A.repAlloc F0 peer (cliKitStk B))
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  storeShim hblk := cliPollSess_prev1StoreShim_rocl mmpl gh W B F0 peer hh hblk
  storePollPrev1 hblk := cliPollSess_prev1SeqFreeStorePoll_rocl mmpl gh W B F0 peer hh hblk
  storeFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliSessFutDrop_rocl_placed_ok hblk

/-! ## 2. Placed `Prev1` Stage P4 Instantiations (`StageP4Prev1CliPlacedStmt` & `StageP4Prev1VRegsPlacedStmt`) -/

/-- Parametric-kit budget-threaded Path C (`Prev1`) 4-kit Stage P4 (`+0x34dc → s0.readReg64.x30`)
on `dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem stageP4Prev1_placed_of_kits [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    {opsEnv : StorePrev1BudgetEnv (cliPollSessPrev1KitPlaced A.repAlloc F0 peer (cliKitStk B))}
    {ikitEnv : IdentityStoreBudgetEnv (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))}
    {pkKitEnv : PreKeyStoreBudgetEnv (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))}
    {kpkKitEnv : KyberPreKeyStoreBudgetEnv
      (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSkit : SessionPrev1KitPlacedOkSE A lim
      (cliPollSessPrev1KitPlaced A.repAlloc F0 peer (cliKitStk B))
      cliPollStorePrev1OpsPlaced opsEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)))
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
    let kit := cliPollSessPrev1KitPlaced A.repAlloc F0 peer σ
    let ops : StorePrev1Ops kit := cliPollStorePrev1OpsPlaced
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk σ
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
      (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
      (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
      (remoteIk : IdentityKey) (baseKey : PublicKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState)
      (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
      (G : SessionGhost) (ss : Session (List (BitVec 8))),
      FitsEnv M lim st_b
        (StageP4Prev1ExitEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
          sst0 ist0 pst0 kst0 opkId? peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey
          G ss enc) →
      SessionExtraRel G ss → ops.RecPrev1Ok G ss enc →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
      (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
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
        (stageP4Prev1PrePlaced A lim st_b kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevCap prevPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc
          peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss.state)
        (fun sf Pf =>
          Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4Prev1BranchPlaced A lim st_b kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
            kpkKit kpkKitEnv s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
            idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkId?
            kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
        (fun _ _ => False) := by
  intro σ kit ops ikit pkKit kpkKit st_b s0 s
    coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
    opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc remoteIk baseKey sst0 ist0 pst0 kst0 G ss
    hfits hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok
    hpt_le hcap_lt hptr_nz hsp_ub hfs hcro hpc hrun hsp_align _htr_pfx
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  have hdealloc : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_ultra_of_mem hh.codecHooks.dealloc (by decide)
  have hDrop : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
    drop_session_structure4_placed_ok_at
      (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
      hh.codecHooks.dealloc (by decide)
  have hSvt : SessionOnlyVtablesPlacedOk kit :=
    cliPollSess_prev1VtablesPlacedOk F0 peer σ hDropNz
  have hIvt : IdentityVtablesPlacedOk ikit :=
    cliPollId_vtablesPlacedOk F0 peer σ hDropNz
  have hPkVt : PreKeyVtablesPlacedOk pkKit :=
    cliPollPk_vtablesPlacedOk F0 pid σ hDropNz
  have hKpkVt : KyberPreKeyVtablesPlacedOk kpkKit :=
    cliPollKpk_vtablesPlacedOk F0 kpkId spkId kbk σ hDropNz
  exact stageP4_prev1_vregs_mark_remove_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))
    kit ops opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
    hdealloc hDrop hSkit hSvt hIkit hIvt hPkKit hPkVt hKpkKit hKpkVt
    st_b s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId
    signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
    hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok (fitsEnv_prev1Step_of_exit hfits)
    hpt_le hcap_lt hptr_nz hsp_ub hfs hcro hpc hrun hsp_align
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs

/-- Instantiates `StageP4Prev1CliPlacedStmt` via `stageP4_prev1_vregs_mark_remove_placed_ok`. -/
theorem stageP4Prev1_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP4Prev1CliPlacedStmt :=
  fun mmpl gh W B F0 peer pid kpkId spkId kbk hh hRead =>
    stageP4Prev1_placed_of_kits mmpl gh W B F0 peer pid kpkId spkId kbk hDropNz hh
      (cliPollSess_prev1KitPlacedOk mmpl gh W B F0 peer hDropNz hh)
      (cliPollId_kitPlacedOkI mmpl gh W B F0 peer hDropNz hh hRead)
      (cliPollPk_removeKitPlacedOk mmpl gh W B F0 pid hDropNz hh hRead)
      (cliPollKpk_markKitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hRead)

/-- Instantiates `StageP4Prev1VRegsPlacedStmt` at `cliPollStageP4Prev1Envs` once `lsReadFileSym` is
discharged across `(mmpl, gh, W, B)`. -/
theorem stageP4Prev1_vregs_placed_inst [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hRead : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets),
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    StageP4Prev1VRegsPlacedStmt A lim
      (fun B F0 peer pid kpkId spkId kbk =>
        cliPollStageP4Prev1Envs A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv) :=
  stageP4Prev1VRegsPlaced_of_cli A lim ReadEnv (stageP4Prev1_placed_inst hDropNz) hRead

/-- Instantiates `StageP4Prev1SeqFreeCliPlacedStmt` via `stageP4_prev1_vregs_mark_remove_placed_ok`. -/
theorem stageP4Prev1_seqFree_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP4Prev1SeqFreeCliPlacedStmt :=
  fun mmpl gh W B F0 peer pid kpkId spkId kbk hh hRead =>
    stageP4Prev1_placed_of_kits mmpl gh W B F0 peer pid kpkId spkId kbk hDropNz hh
      (cliPollSess_prev1SeqFreeKitPlacedOk mmpl gh W B F0 peer hDropNz hh)
      (cliPollId_kitPlacedOkI mmpl gh W B F0 peer hDropNz hh hRead)
      (cliPollPk_removeKitPlacedOk mmpl gh W B F0 pid hDropNz hh hRead)
      (cliPollKpk_markKitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hRead)

/-- Instantiates `StageP4Prev1VRegsPlacedStmt` at SeqFree `cliPollStageP4Prev1SeqFreeEnvs` once
`lsReadFileSym` is discharged across `(mmpl, gh, W, B)`. -/
theorem stageP4Prev1_seqFree_vregs_placed_inst [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hRead : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets),
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    StageP4Prev1VRegsPlacedStmt A lim
      (fun B F0 peer pid kpkId spkId kbk =>
        cliPollStageP4Prev1SeqFreeEnvs A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv) :=
  stageP4Prev1SeqFreeVRegsPlaced_of_cli A lim ReadEnv
    (stageP4Prev1_seqFree_placed_inst hDropNz) hRead

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlacedBudget
