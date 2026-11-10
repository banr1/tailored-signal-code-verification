/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlacedBudget
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# File-Descriptor-Threaded Inner Contract Instantiation for `decrypt_signal` (Placed)

Lifts `withFdsGe3Closed (dirGetSpecPlaced ...)` into `withFds A` when `lim.enforced = true`,
assembles session and identity store kits from a Block-`589` `dirGetSpecPlaced` contract, and
instantiates `InnerDecryptFrozenPlacedOk` at `decBinarySessKitPlacedBudgetFixed` and
`decBinaryIdKitPlacedBudgetFixed`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (
  IsLsBlockProg LibsignalFullPlacement LibsignalHooks LibsignalPlacement libsignalMutatedBlocks
  lsBlackBoxU8Sym lsmpl withLsCodeLoaded
)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt (region_ok_restrictPre_true)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (recEntryPlaced recExitPlaced)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.E2E (aesDecHookMallocng fmtWriteHook0 formatInnerHook0 pqxdhSpqrModel)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_46 lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withEnvPre withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall region_ok withLsFrozen)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced cliHookTablePlaced lsDropOffPlaced_eq lsFmtWriteSym lsFormatInnerSym
)
open CryptoVerification.SignalSession.Cli (
  DirGetGhost DirGhost ReadRule StoresGhost dirAt getResultAt pathOf
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliGhostExterns_blackBox cliIdentityVtRoSym cliSessionKitSpecPlaced
)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (
  cliIdentityKitSpecPlaced cliIdentityKitSpecPlaced_quiet savePollNeedPlaced saveShimNeedPlaced
  trustPollNeedPlaced trustShimNeedPlaced
)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (
  cliSessionKitSpecPlaced_quiet loadPollNeedPlaced loadShimNeedPlaced storePollNeedXPlaced
  storeShimNeedPlaced
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (
  blkPC_565 blkPl_565 lsProg_565 lsProg_569 lsProg_589
)
open CryptoVerification.SignalSession.Cli.RunCompose (withCodeOk)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  cliDecModelRecOkAt_opened fmtWrite_row_placed formatInner_row_placed
  scopeIn scopeKit scopeKit_pqrState_lt scopeKit_recordInScopeP
)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (
  ls_transfer_cl_to_lscro ls_transfer_lscro
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
)
open LibsignalBinary.Heap.Fine (fmtWriteHook0_budget_ok formatInnerHook0_budget_ok)
open LibsignalBinary.Heap.SpecBudget (
  FmtWriteEnv FormatInnerEnv aesDecBudgetSpec fmtWriteBudgetEnvSpec fmtWriteBudgetSpec
  formatInnerBudgetEnvSpec
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget (
  withStoresDecPlacedSpecVX
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget (
  recordDecryptPlacedSpecTPTight withStoresDecPlacedSpecVTPF
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget (
  cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_of_runHooks
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlacedBudget (
  recordDecryptV1_full_placed_region_vregs_ok_PTight_cli_of_tdEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnvOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (
  decBinaryIdKitPlacedBudgetFixed decBinarySessKitPlacedBudgetFixed
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeSeqFreeXBudget (
  serializeCanonSeqFreeSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (serializeCanonSpecX)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed ReadFileRuleEnvFixed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  withFds withFds_pool_enforced withFds_repAlloc
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget (
  cliDirPutStr_placed_ok cliIdKitOkIE_placed_of_polls cliIdentityKitDefaultBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (
  SessKitHooksPlaced cliAddrText_placed_ok_of_sessHooks cliDirPut_placed_ok_of_sessHooks
  cliSessFutDrop_rocl_placed_ok cliSessLoadPoll_rocl_placed_ok cliSessLoadShim_rocl_placed_ok
  cliSessStorePoll_rocl_placed_ok cliSessStorePoll_rocl_seqFree_placed_ok
  cliSessStoreShim_rocl_placed_ok cliSessionKitDefaultBudgetEnv cliSessionKitSeqFreeBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget (
  InnerDecryptFrozenPlacedOk decIdKitPlaced decSessKitPlaced
  withStoresDecFrozenPlacedSpecVTP withStoresDecPlacedSpecVTP
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  dirGetSpecPlaced idSavePollSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget (
  CliIdSavePollEnv publicKeySerialize_lscro_of_cli
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlacedBudget (
  idSavePoll_placed_ok_of_deps_core
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget (
  idTrustPoll_placed_ok_of_deps identityKey_decode_placed_ok publicKeyEq_placed_ok_of_bb
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (
  sessDeserialize_cli_dcan_byBytes_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget (
  serializeCanonSeqFree_cli_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## Lifting `withFdsGe3Closed` on `dirGetSpecPlaced` -/

/-- Equates `withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv stk)` with
`dirGetSpecPlaced rd pathOk (withFds A) lim GetEnv stk` when `lim.enforced = true`. -/
theorem subroutine_ok_dirGet_withFds [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {entry : BitVec 64} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true)
    (hGet : subroutine_ok P entry
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv stk))) :
    subroutine_ok P entry
      (dirGetSpecPlaced rd pathOk (withFds A) lim GetEnv stk) := by
  refine subroutine_ok_mono hGet ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded, withCodeOk,
      withFds_repAlloc] at hpre ⊢
    rw [withFds_pool_enforced A henf] at hpre
    refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hpre; sep_ac_rfl
  · rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded, withCodeOk,
      withFds_repAlloc] at hpost ⊢
    have hpost' : sf.mem ⊨
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((∃∗ evs : List AllocEvent,
            (∃∗ r : Except Unit (List (BitVec 8)),
              ⌜r = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace ∧
                GetEnv s0.fs.files x.dir x.name evs⌝ ∗
                getResultAt A.repAlloc x.ret r) ∗
              dirAt A.repAlloc x.self x.dir ∗
              CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
              stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf) ∗
            R) := by
      refine Eq.mp (congrArg (sf.mem ⊨ ·) ?_) hpost; sep_ac_rfl
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨hClosedF, hpostRest⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpostRest ⊢
    rcases hpostRest with ⟨evs, hm⟩
    refine ⟨evs, ?_⟩
    rw [withFds_pool_enforced A henf]
    have hm' : sf.mem ⊨ ⌜FdsGe3Closed sf.fs⌝ ∗
        (((∃∗ r : Except Unit (List (BitVec 8)),
          ⌜r = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace ∧
            GetEnv s0.fs.files x.dir x.name evs⌝ ∗
            getResultAt A.repAlloc x.ret r) ∗
          dirAt A.repAlloc x.self x.dir ∗
          CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨hClosedF, hm⟩
    refine Eq.mp (congrArg (sf.mem ⊨ ·) ?_) hm'; sep_ac_rfl

/-! ## Store-kit assembly from `dirGetSpecPlaced` -/

/-- Assembles `SessionOnlyKitPlacedOkSE` for `cliSessionKitDefaultBudgetEnv` from a Block-`589` `dirGetSpecPlaced` contract. -/
theorem cliSessKitOkSE_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {deserProg serProg : Program} {deserBlk serBlk : Nat}
    [IsLsBlockProg deserProg deserBlk H]
    [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : SessKitHooksPlaced A lim H)
    (hGet : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (DirGetEnv PathEnv ReadEnv rd)
        (RunBudgets.dirGetNeed ⟨readStk⟩)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord H := by
  have hAddr := cliAddrText_placed_ok_of_sessHooks hh
  have hPut := cliDirPut_placed_ok_of_sessHooks hh
  exact
    { loadShim := fun hblk => cliSessLoadShim_rocl_placed_ok hh.alloc hs1 hblk
      loadPoll := fun hblk => cliSessLoadPoll_rocl_placed_ok hh.alloc hAddr hGet hDeser
        (hh.fs (lsProg_569 H) 569) hs2 hblk (by decide) (by decide) (by decide) (by decide)
        hDeserBlk hDeserUnmut
      loadFutDrop := fun hblk => by
        dsimp only [cliSessionKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliSessFutDrop_rocl_placed_ok hblk
      storeShim := fun hblk => cliSessStoreShim_rocl_placed_ok hh.alloc hs3 hblk
      storePoll := fun hblk => cliSessStorePoll_rocl_placed_ok hh.alloc hAddr hSer hPut hs4 hblk
        (by decide) (by decide) hSerBlk hSerUnmut (by decide) (by decide)
      storeFutDrop := fun hblk => by
        dsimp only [cliSessionKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliSessFutDrop_rocl_placed_ok hblk }

theorem cliSessKitOkSE_seqFree_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {deserProg serProg : Program} {deserBlk serBlk : Nat}
    [IsLsBlockProg deserProg deserBlk H]
    [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim H)
    (hGet : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (DirGetEnv PathEnv ReadEnv rd)
        (RunBudgets.dirGetNeed ⟨readStk⟩)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hSerSeqFree : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitSeqFreeBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord H := by
  let hsh := SessKitHooksPlaced.of_runHooks hh
  have hAddr := cliAddrText_placed_ok_of_sessHooks hsh
  have hPut := cliDirPut_placed_ok_of_sessHooks hsh
  exact
    { loadShim := fun hblk => cliSessLoadShim_rocl_placed_ok hsh.alloc hs1 hblk
      loadPoll := fun hblk => cliSessLoadPoll_rocl_placed_ok hsh.alloc hAddr hGet hDeser
        (hsh.fs (lsProg_569 H) 569) hs2 hblk (by decide) (by decide) (by decide) (by decide)
        hDeserBlk hDeserUnmut
      loadFutDrop := fun hblk => by
        dsimp only [cliSessionKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliSessFutDrop_rocl_placed_ok hblk
      storeShim := fun hblk => cliSessStoreShim_rocl_placed_ok hsh.alloc hs3 hblk
      storePoll := fun hblk => cliSessStorePoll_rocl_seqFree_placed_ok hsh.alloc hAddr hSerSeqFree
        hPut hs4 hblk (by decide) (by decide) hSerBlk hSerUnmut (by decide) (by decide)
      storeFutDrop := fun hblk => by
        dsimp only [cliSessionKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliSessFutDrop_rocl_placed_ok hblk }

/-- Assembles `IdentityStoreKitPlacedOkI` from a Block-`589` `dirGetSpecPlaced` contract. -/
theorem cliIdKitOkIE_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim H)
    (hGet : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (DirGetEnv PathEnv ReadEnv rd)
        (RunBudgets.dirGetNeed ⟨readStk⟩)))
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4) :
    IdentityStoreKitPlacedOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitDefaultBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym ReadEnv)
      H := by
  have hPut := cliDirPutStr_placed_ok hh
  have hEq := publicKeyEq_placed_ok_of_bb h_bb
  have h566 := idTrustPoll_placed_ok_of_deps hh.alloc hGet
    (identityKey_decode_placed_ok (A := A) H) hEq hs2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hSer := publicKeySerialize_lscro_of_cli
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hh.alloc (by decide)
  have hGet' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hGet (by decide) (by decide) (by decide)
  have hPut' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hPut (by decide) (by decide) (by decide)
  have hDec' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    (identityKey_decode_placed_ok (A := A) H) (by decide) (by decide) (by decide)
  have hEq' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hEq (by decide) (by decide) (by decide)
  have h565 : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (idSavePollSpecPlaced rd pathOk A lim
        (CliIdSavePollEnv rd (DirGetEnv PathEnv ReadEnv rd) DirPutStrEnv) s4) :=
    idSavePoll_placed_ok_of_deps_core hh.alloc hSer hGet' hPut' hDec' hEq' hs4
  exact cliIdKitOkIE_placed_of_polls hDropNz hh.alloc h566 h565 hs1 hs3

/-! ## Fixed-kit inner instantiation -/

theorem w2_decBinarySessKitPlacedFixed_okSE_of_dirGet [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (RunBudgets.dirGetNeed ⟨B.readFile⟩))) :
    SessionOnlyKitPlacedOkSE A lim
      (decSessKitPlaced A.repAlloc F0 peer B)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_seqFree_of_dirGet
    (deserProg := lsProg_46 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (deserBlk := 46)
    (serProg := lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz hh hGet
    (sessDeserialize_cli_dcan_byBytes_placed_ok mmpl gh W hG (fun _ h => h))
    (serializeCanonSeqFree_cli_placed mmpl gh W hG)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide)

theorem w2_decBinaryIdKitPlacedFixed_okIE_of_dirGet [LibsignalPlacement]
    {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (RunBudgets.dirGetNeed ⟨B.readFile⟩))) :
    IdentityStoreKitPlacedOkI A lim
      (decIdKitPlaced A.repAlloc F0 peer B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliIdKitOkIE_of_dirGet
    (vtSym := cliIdentityVtRoSym)
    hDropNz hh hGet
    (cliGhostExterns_blackBox mmpl gh W)
    (by decide) (Nat.le_refl _) (by decide) (Nat.le_refl _)

theorem w2_inner_binaryKitFixed_frozen_placed_ok_of_dirGet_and_region [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (RunBudgets.dirGetNeed ⟨B.readFile⟩)))
    (hrec : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv)).withVRegs.restrictPre (fun _ => True))) :
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) := by
  intro F0 peer hPeer
  have hSess := w2_decBinarySessKitPlacedFixed_okSE_of_dirGet mmpl gh W A lim B F0 peer
    hDropNz hG hh hGet
  have hId := w2_decBinaryIdKitPlacedFixed_okIE_of_dirGet mmpl gh W A lim B F0 peer
    hDropNz hh hGet
  have hq : (decSessKitPlaced A.repAlloc F0 peer B).Quiet ∧
      (decIdKitPlaced A.repAlloc F0 peer B).Quiet :=
    ⟨cliSessionKitSpecPlaced_quiet, cliIdentityKitSpecPlaced_quiet⟩
  have hraw :=
    cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_of_runHooks
      mmpl gh W
      (A := A) (lim := lim) (ctl := 0#64) (S := pqxdhSpqrModel ⟨W.C, W.Q⟩) (tdEnv := tdEnv)
      (kit := decSessKitPlaced A.repAlloc F0 peer B)
      (kitEnv := decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (ikit := decIdKitPlaced A.repAlloc F0 peer B)
      (ikitEnv := decBinaryIdKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (st0 := StoresGhost.opened.sessions) (ist0 := StoresGhost.opened.identity)
      (Scope := scopeKit) (Q := fun _ => True)
      hh hSess hId hq
      (fun _ hr => scopeKit_recordInScopeP hr)
      (fun x rec pt rec' haddr hsc hdec =>
        cliDecModelRecOkAt_opened
          (A := A.repAlloc) (b := 0#64) (pathOk := cliWrOk)
          (Scope₀ := scopeIn) (F0 := F0) (peer := peer)
          (s1 := 0) (s2 := 0) (s3 := 0) (s4 := 0)
          (C := W.C) (K := W.Q.K) (parse := uuidTryParse)
          (fun _ h => h) hPeer x rec rec' pt haddr hsc hdec)
      hrec
      (fun _ _ ses hsc hcur => ⟨scopeKit_pqrState_lt hsc.1 ses hcur, trivial⟩)
  refine subroutine_ok_mono hraw ?_ ?_
  · intro xs R s0 hpre
    dsimp only [withEnvPre, withStoresDecFrozenPlacedSpecVTP, withLsFrozen,
      withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      withStoresDecPlacedSpecVTPF, Spec.restrictPre] at hpre ⊢
    generalize (withStoresDecPlacedSpecVX W.C A lim 0#64 uuidTryParse
      (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv encodeRecord
      (decSessKitPlaced A.repAlloc F0 peer B)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (decIdKitPlaced A.repAlloc F0 peer B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B F0 peer)
      StoresGhost.opened.sessions StoresGhost.opened.identity
      scopeKit (fun _ _ => False)).pre xs s0 = Bpre at hpre ⊢
    generalize tokenInitPlacedAt = T at hpre ⊢
    refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hpre; sep_ac_rfl
  · intro xs R s0 sf hpost
    dsimp only [withEnvPre, withStoresDecFrozenPlacedSpecVTP, withLsFrozen,
      withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      withStoresDecPlacedSpecVTPF, Spec.restrictPre] at hpost ⊢
    exact hpost

private theorem cliGhost_row_other (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State}
    (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (hne1 : sym ≠ CryptoVerification.SignalSession.lsRustAllocSymCli := by decide)
    (hne2 : sym ≠ CryptoVerification.SignalSession.lsRustDeallocSymCli := by decide)
    (hne3 : sym ≠ CryptoVerification.SignalSession.lsRustReallocSymCli := by decide)
    (hne4 : sym ≠ CryptoVerification.SignalSession.lsRustAllocZeroedSymCli := by decide)
    (hne5 : sym ≠ CryptoVerification.SignalSession.lsRustNoAllocShimSymCli := by decide)
    (hne6 : sym ≠ CryptoVerification.SignalSession.lsStringCloneSym := by decide)
    (hne7 : sym ≠ CryptoVerification.SignalSession.lsReadFileSym := by decide)
    (hne8 : sym ≠ CryptoVerification.SignalSession.lsReadStdinSym := by decide)
    (hne9 : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (hne10 : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some f :=
  (cliGhostExterns_other gh _ hne1 hne2 hne3 hne4 hne5 hne6 hne7 hne8 hne9 hne10).trans
    (cliExternsPlaced_row mmpl W hrow)

private theorem fmtWrite_hookSat {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim FmtWriteEnv) :=
  ⟨fmtWriteHook0, cliGhost_row_other mmpl gh W (fmtWrite_row_placed mmpl W),
   fmtWriteHook0_budget_ok M A lim⟩

private theorem formatInner_hookSat {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim FormatInnerEnv) :=
  ⟨formatInnerHook0, cliGhost_row_other mmpl gh W (formatInner_row_placed mmpl W),
   formatInnerHook0_budget_ok M A lim⟩

theorem w2_inner_binaryKitFixed_full_placed_ok_of_dirGet_ofEnv [LibsignalFullPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (RunBudgets.dirGetNeed ⟨B.readFile⟩)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv a evs) :
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) :=
  w2_inner_binaryKitFixed_frozen_placed_ok_of_dirGet_and_region mmpl gh W A lim
    hDropNz hG hh hGet
    (region_ok_restrictPre_true
      (recordDecryptV1_full_placed_region_vregs_ok_PTight_cli_of_tdEnv
        mmpl gh W 0#64 hG hAesDec hSpqr
        (fmtWrite_hookSat mmpl gh W A lim)
        (formatInner_hookSat mmpl gh W A lim)
        hRecv_ne ⟨[], rfl⟩ ⟨[], rfl⟩ htd))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudgetFd
