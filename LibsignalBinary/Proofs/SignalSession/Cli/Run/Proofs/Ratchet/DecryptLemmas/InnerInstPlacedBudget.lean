/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Inner Contract Instantiation for `decrypt_signal` (Placed)

Defines the session and identity store budget envelopes `w2SessKitBudgetEnv` and `w2IdKitBudgetEnv`
and instantiates budget-threaded `InnerDecryptPlacedOk` and `InnerDecryptFrozenPlacedOk` on
Block `463` (`signal_session_ratchet::decrypt_signal`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt (region_ok_restrictPre_true)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (recEntryPlaced recExitPlaced)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.E2E (aesDecHookMallocng pqxdhSpqrModel)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles subroutine_ok_withLsCodeRoLoaded_of_plain withEnvPre
)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall region_ok)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (logClosurePlacedSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsFmtWriteSym lsFormatInnerSym lsReadFileSym
)
open CryptoVerification.SignalSession.Cli (StoresGhost cliIdentityVtSym cliSessionVtSym)
open CryptoVerification.SignalSession.Cli.KitInst (cliGhostExterns_blackBox)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks CliGhostHooksFs cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (
  cliIdentityKitSpecPlaced_quiet savePollNeed saveShimNeed trustPollNeed trustShimNeed
)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (
  cliSessionKitSpecPlaced_quiet loadPollNeed loadShimNeed storePollNeedX storeShimNeed
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (instIsLsBlockProg_589 lsProg_589)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  cliDecModelRecOkAt_opened scopeIn scopeKit scopeKit_pqrState_lt scopeKit_recordInScopeP
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (
  aesDecBudgetSpec fmtWriteBudgetEnvSpec formatInnerBudgetEnvSpec withVmPreserved
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget (
  withStoresDecPlacedSpecVX
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget (
  recordDecryptPlacedSpecTPTight withStoresDecPlacedSpecVTPF
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget (
  cliDecryptSignalWithStores_placed_okVTP_distinct_fs_of_runHooks
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlacedBudget (
  recordDecryptV1_placed_region_vregs_ok_PTight_cli
  recordDecryptV1_placed_region_vregs_ok_PTight_cli_ofEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (
  TryDecryptCliEnv TryDecryptCliEnvOf
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget (
  sessDeserEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget (
  cliIdKitOkIE_placed cliIdentityKitDefaultBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (
  cliSessionKitDefaultBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget (
  InnerDecryptPlacedOk decIdKitPlaced decSessKitPlaced withStoresDecPlacedSpecVTP
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  ReadFileRuleEnv readFileSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (
  SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (
  SessDeserExactEnv cliSessKitOkSE_cli_of_sessDeserEvents_readHook
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## Session and identity store budget envelopes -/

/-- Session-store budget envelope for `decSessKitPlaced A F0 peer B`, parameterized by `DeserEnv` and `ReadEnv`. -/
abbrev w2SessKitBudgetEnv [LibsignalPlacement] (A : RustAlloc) (B : RunBudgets)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop := SessDeserExactEnv)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv cliIo.rd)
    (F0 : FsFiles) (peer : AddrGhost) :
    SessionStoreBudgetEnv (decSessKitPlaced A F0 peer B) :=
  cliSessionKitDefaultBudgetEnv A cliIo.rd F0 cliWrOk scopeKit peer
    loadShimNeed (loadPollNeed B.readFile) storeShimNeed storePollNeedX
    DeserEnv cliSessionVtSym cliIdentityVtSym ReadEnv

/-- Identity-store budget envelope for `decIdKitPlaced A F0 peer B`, parameterized by `ReadEnv`. -/
abbrev w2IdKitBudgetEnv [LibsignalPlacement] (A : RustAlloc) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv cliIo.rd)
    (F0 : FsFiles) (peer : AddrGhost) :
    IdentityStoreBudgetEnv (decIdKitPlaced A F0 peer B) :=
  cliIdentityKitDefaultBudgetEnv A cliIo.rd F0 cliWrOk peer
    trustShimNeed (trustPollNeed B.readFile) saveShimNeed (savePollNeed B.readFile)
    cliIdentityVtSym ReadEnv

/-! ## Block `463` inner contract instantiation -/

/-- Reduces budget-threaded `InnerDecryptPlacedOk` on Block `463` to the `recordDecryptPlacedSpecTPTight` region obligation. -/
theorem w2_inner_placed_ok_of_region_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hMem : ∀ r, scopeKit r → DeserEnv r (sessDeserEvents r))
    (hrec : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv).withVRegs.restrictPre (fun _ => True))) :
    InnerDecryptPlacedOk ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv
      (w2SessKitBudgetEnv A.repAlloc B DeserEnv ReadEnv)
      (w2IdKitBudgetEnv A.repAlloc B ReadEnv) := by
  intro F0 peer hPeer
  have hSess : SessionOnlyKitPlacedOkSE A lim (decSessKitPlaced A.repAlloc F0 peer B)
      (w2SessKitBudgetEnv A.repAlloc B DeserEnv ReadEnv F0 peer)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliSessKitOkSE_cli_of_sessDeserEvents_readHook mmpl gh W
      (F0 := F0) (Scope := scopeKit) (peer := peer) (readStk := B.readFile)
      (vtSym := cliSessionVtSym) (idVtSym := cliIdentityVtSym)
      hDropNz hG hFs.allocZeroed_fsT hFs.stringClone_fsT hReadHook (fun _ h => h) hMem
      (by decide) (Nat.le_refl _) (by decide) (by decide)
  have hId : IdentityStoreKitPlacedOkI A lim (decIdKitPlaced A.repAlloc F0 peer B)
      (w2IdKitBudgetEnv A.repAlloc B ReadEnv F0 peer)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliIdKitOkIE_placed
      (readProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
      (vtSym := cliIdentityVtSym)
      hDropNz
      (fun _ hp => hp.2)
      hh
      (subroutine_ok_withLsCodeRoLoaded_of_plain
        (ls_hook_ok_ultra_of_mem
          (prog := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 589)
          hReadHook (by decide) (by decide) (by decide)))
      (cliGhostExterns_blackBox mmpl gh W)
      (by decide) (Nat.le_refl _) (by decide) (Nat.le_refl _)
  have hq : (decSessKitPlaced A.repAlloc F0 peer B).Quiet ∧
      (decIdKitPlaced A.repAlloc F0 peer B).Quiet :=
    ⟨cliSessionKitSpecPlaced_quiet, cliIdentityKitSpecPlaced_quiet⟩
  have hraw := cliDecryptSignalWithStores_placed_okVTP_distinct_fs_of_runHooks mmpl gh W
    (A := A) (lim := lim) (ctl := 0#64) (S := pqxdhSpqrModel ⟨W.C, W.Q⟩) (tdEnv := tdEnv)
    (kit := decSessKitPlaced A.repAlloc F0 peer B)
    (kitEnv := w2SessKitBudgetEnv A.repAlloc B DeserEnv ReadEnv F0 peer)
    (ikit := decIdKitPlaced A.repAlloc F0 peer B)
    (ikitEnv := w2IdKitBudgetEnv A.repAlloc B ReadEnv F0 peer)
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
    dsimp only [withEnvPre, withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      withStoresDecPlacedSpecVTPF, Spec.restrictPre] at hpre ⊢
    generalize (withStoresDecPlacedSpecVX W.C A lim 0#64 uuidTryParse
      (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv encodeRecord
      (decSessKitPlaced A.repAlloc F0 peer B)
      (w2SessKitBudgetEnv A.repAlloc B DeserEnv ReadEnv F0 peer)
      (decIdKitPlaced A.repAlloc F0 peer B)
      (w2IdKitBudgetEnv A.repAlloc B ReadEnv F0 peer)
      StoresGhost.opened.sessions StoresGhost.opened.identity
      scopeKit (fun _ _ => False)).pre xs s0 = Bpre at hpre ⊢
    generalize tokenInitPlacedAt = T at hpre ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · intro xs R s0 sf hpost
    dsimp only [withEnvPre, withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      withStoresDecPlacedSpecVTPF, Spec.restrictPre] at hpost ⊢
    exact hpost

theorem w2_inner_placed_ok_of_region [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnv cliIo.rd)))
    (hrec : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv).withVRegs.restrictPre (fun _ => True))) :
    InnerDecryptPlacedOk ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv
      (w2SessKitBudgetEnv A.repAlloc B)
      (w2IdKitBudgetEnv A.repAlloc B) :=
  w2_inner_placed_ok_of_region_ofEnv mmpl gh W A lim hDropNz hG hFs hh hReadHook
    (fun _ _ => rfl) hrec

/-- Instantiates envelope-parametric `InnerDecryptPlacedOk` on Block `463` via `recordDecryptV1_placed_region_vregs_ok_PTight_cli_ofEnv`. -/
theorem w2_inner_placed_ok_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hMem : ∀ r, scopeKit r → DeserEnv r (sessDeserEvents r))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtWrite : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (hFmtInner : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs)
    (hclosure : subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 462)
      (CryptoVerification.withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec))) :
    InnerDecryptPlacedOk ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) B
      (TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv)
      (w2SessKitBudgetEnv A.repAlloc B DeserEnv ReadEnv)
      (w2IdKitBudgetEnv A.repAlloc B ReadEnv) :=
  w2_inner_placed_ok_of_region_ofEnv mmpl gh W A lim hDropNz hG hFs hh hReadHook hMem
    (region_ok_restrictPre_true
      (recordDecryptV1_placed_region_vregs_ok_PTight_cli_ofEnv
        mmpl gh W 0#64 hG hAesDec hSpqr hFmtWrite hFmtInner
        hRecv_ne hFmtWrite_ne hFmtInner_ne hclosure))

theorem w2_inner_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnv cliIo.rd)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hclosure : subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 462)
      (CryptoVerification.withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec))) :
    InnerDecryptPlacedOk ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) B
      (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K))
      (w2SessKitBudgetEnv A.repAlloc B)
      (w2IdKitBudgetEnv A.repAlloc B) :=
  w2_inner_placed_ok_of_region mmpl gh W A lim hDropNz hG hFs hh hReadHook
    (region_ok_restrictPre_true
      (recordDecryptV1_placed_region_vregs_ok_PTight_cli mmpl gh W 0#64 hG hAesDec hSpqr hclosure))

/-- Reduces `withLsFrozen`-guarded budget-threaded `InnerDecryptFrozenPlacedOk` on Block `463` to the frozen region obligation. -/
theorem w2_inner_frozen_placed_ok_of_region_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hMem : ∀ r, scopeKit r → DeserEnv r (sessDeserEvents r))
    (hrec : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv)).withVRegs.restrictPre (fun _ => True))) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
      ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv
      (w2SessKitBudgetEnv A.repAlloc B DeserEnv ReadEnv)
      (w2IdKitBudgetEnv A.repAlloc B ReadEnv) := by
  intro F0 peer hPeer
  have hSess : SessionOnlyKitPlacedOkSE A lim (decSessKitPlaced A.repAlloc F0 peer B)
      (w2SessKitBudgetEnv A.repAlloc B DeserEnv ReadEnv F0 peer)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliSessKitOkSE_cli_of_sessDeserEvents_readHook mmpl gh W
      (F0 := F0) (Scope := scopeKit) (peer := peer) (readStk := B.readFile)
      (vtSym := cliSessionVtSym) (idVtSym := cliIdentityVtSym)
      hDropNz hG hFs.allocZeroed_fsT hFs.stringClone_fsT hReadHook (fun _ h => h) hMem
      (by decide) (Nat.le_refl _) (by decide) (by decide)
  have hId : IdentityStoreKitPlacedOkI A lim (decIdKitPlaced A.repAlloc F0 peer B)
      (w2IdKitBudgetEnv A.repAlloc B ReadEnv F0 peer)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliIdKitOkIE_placed
      (readProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
      (vtSym := cliIdentityVtSym)
      hDropNz
      (fun _ hp => hp.2)
      hh
      (subroutine_ok_withLsCodeRoLoaded_of_plain
        (ls_hook_ok_ultra_of_mem
          (prog := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 589)
          hReadHook (by decide) (by decide) (by decide)))
      (cliGhostExterns_blackBox mmpl gh W)
      (by decide) (Nat.le_refl _) (by decide) (Nat.le_refl _)
  have hq : (decSessKitPlaced A.repAlloc F0 peer B).Quiet ∧
      (decIdKitPlaced A.repAlloc F0 peer B).Quiet :=
    ⟨cliSessionKitSpecPlaced_quiet, cliIdentityKitSpecPlaced_quiet⟩
  have hraw :=
    LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_of_runHooks
      mmpl gh W
      (A := A) (lim := lim) (ctl := 0#64) (S := pqxdhSpqrModel ⟨W.C, W.Q⟩) (tdEnv := tdEnv)
      (kit := decSessKitPlaced A.repAlloc F0 peer B)
      (kitEnv := w2SessKitBudgetEnv A.repAlloc B DeserEnv ReadEnv F0 peer)
      (ikit := decIdKitPlaced A.repAlloc F0 peer B)
      (ikitEnv := w2IdKitBudgetEnv A.repAlloc B ReadEnv F0 peer)
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
    dsimp only [withEnvPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      withStoresDecPlacedSpecVTPF, Spec.restrictPre] at hpre ⊢
    generalize (withStoresDecPlacedSpecVX W.C A lim 0#64 uuidTryParse
      (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv encodeRecord
      (decSessKitPlaced A.repAlloc F0 peer B)
      (w2SessKitBudgetEnv A.repAlloc B DeserEnv ReadEnv F0 peer)
      (decIdKitPlaced A.repAlloc F0 peer B)
      (w2IdKitBudgetEnv A.repAlloc B ReadEnv F0 peer)
      StoresGhost.opened.sessions StoresGhost.opened.identity
      scopeKit (fun _ _ => False)).pre xs s0 = Bpre at hpre ⊢
    generalize tokenInitPlacedAt = T at hpre ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · intro xs R s0 sf hpost
    dsimp only [withEnvPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      withStoresDecPlacedSpecVTPF, Spec.restrictPre] at hpost ⊢
    exact hpost

theorem w2_inner_frozen_placed_ok_of_region [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnv cliIo.rd)))
    (hrec : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv)).withVRegs.restrictPre (fun _ => True))) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
      ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv
      (w2SessKitBudgetEnv A.repAlloc B)
      (w2IdKitBudgetEnv A.repAlloc B) :=
  w2_inner_frozen_placed_ok_of_region_ofEnv mmpl gh W A lim hDropNz hG hFs hh hReadHook
    (fun _ _ => rfl) hrec

theorem w2_inner_full_placed_ok_ofEnv [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hMem : ∀ r, scopeKit r → DeserEnv r (sessDeserEvents r))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtWrite : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (hFmtInner : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
      ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) B
      (TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv)
      (w2SessKitBudgetEnv A.repAlloc B DeserEnv ReadEnv)
      (w2IdKitBudgetEnv A.repAlloc B ReadEnv) :=
  w2_inner_frozen_placed_ok_of_region_ofEnv mmpl gh W A lim hDropNz hG hFs hh hReadHook hMem
    (region_ok_restrictPre_true
      (LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlacedBudget.recordDecryptV1_full_placed_region_vregs_ok_PTight_cli_ofEnv
        mmpl gh W 0#64 hG hAesDec hSpqr hFmtWrite hFmtInner
        hRecv_ne hFmtWrite_ne hFmtInner_ne))

/-- Instantiates `InnerDecryptFrozenPlacedOk` on Block `463` under `[LibsignalFullPlacement]`. -/
theorem w2_inner_full_placed_ok [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnv cliIo.rd)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
      ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) B
      (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K))
      (w2SessKitBudgetEnv A.repAlloc B)
      (w2IdKitBudgetEnv A.repAlloc B) :=
  w2_inner_frozen_placed_ok_of_region mmpl gh W A lim hDropNz hG hFs hh hReadHook
    (region_ok_restrictPre_true
      (LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlacedBudget.recordDecryptV1_full_placed_region_vregs_ok_PTight_cli
        mmpl gh W 0#64 hG hAesDec hSpqr))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudget
