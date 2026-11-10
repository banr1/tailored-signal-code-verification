/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0PostBob
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAOverD3Wire
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkFresh
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget

/-!
# Unbundled `MainOkOverD3F3` Assembly on `cliElfBytes`

**Checked by Lean.**

Proves `hole_m24slot_overD3_assembly_closed`, establishing `MainOkOverD3F3` on
`cliElfBytes` from unbundled ghost-witness hypotheses via the post-Bob `prev1` W4
budget envelope.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinOverD3

open Arm64 (GhostName HookSat Memory subroutine_ok)
open Arm64.Obj (Image MultiPlacement)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoVerification
  (LibsignalFrozen LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym
   lsRustAllocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliMainStk cliResStack cliRunBudgets cliWrOk mainFrameSize)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks CliGhostHooksFs cliGhostExterns cliGhostExterns_other cliGhostExterns_shim)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
  (ckx2_w1EncExact_groupSpec ckx2_w1EncExact_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0 (d3SlotMainFitsOneGiBOf)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom (PostBobPrev1Dom W4RecvPrekeyCmkDom0Of')
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
  (W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
   w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed_of_cliPqOrD3RecvDom)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0PostBob
  (fits2_zbDom0'Cum fits2_zbDom0'GrpS109 fits2_zbDom0'Live fits2_zbDom0'MaxReq fits2_zbDom0'Peak
   w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec')
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux (w4c_repairedStatesRecvEnvFam)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4BinaryRecvPrekeyParamsCmk w4c_defaultDecodeMaxOps)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3 (Block617TransferFixedHyp)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 (MainOkOverD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob
  (h7w_decPkValidOverTight_sub_zbDom0'FixedOf)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAOverD3Wire
  (H7RAOut1DomPred h7ra_overD3_wire_tightRaw_of_out1Dom)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (ExternNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliRunHooksBundle)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks cliExternsPlaced_alloc_budget_sat
   cliExternsPlaced_realloc_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
  (CliSpqrRecvTightLinkedEnv SpqrSendCoinsTightLinkedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge
  (gu2b_SpqrSendCoinsExactFromPbLinkedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (allocContractsBudgetPlaced_cli sessDeserialize_of_sessDeserEvents_caller_ok)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
  (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (hole3_decSigEnv_r3a_congr hole3_encEnv_r2_congr hole3_w1_inner hole3_w2_inner hole3_w3_init)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkFresh
  (w4f_dpPollProgPlaced_helpers_eq_poll w4f_pollCallees_of_f3Hooks)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
  (w4s2_SpqrRecvTopStateGuardedBytesEnv w4s2_TryDecryptTopStateGuardedEnv
   w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty w4s2_spqrSeams_topStateGuarded
   w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)

private theorem etjo_hDeserHelpers [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (hG : CliGhostAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits gh) :
    subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        SessDeserializeCancelEnv) := by
  rw [w4f_dpPollProgPlaced_helpers_eq_poll mmpl gh W]
  dsimp only [CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP1ProgPlaced]
  exact sessDeserialize_of_sessDeserEvents_caller_ok
    (callerBlk := 518)
    (allocContractsBudgetPlaced_cli mmpl gh W hG)
    (fun _ h => h)
    (fun _ hr => ⟨hr, rfl⟩)
    (by decide)

private theorem etjo_growOneVecU8_lsProg51_withLsCl_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (CryptoVerification.lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621)
      (CryptoVerification.withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)) :=
  LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget.growOneVecU8_caller_withLsCl_ok
    (callerProg := CryptoVerification.lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (i := 51)
    ((show CryptoVerification.lsHandleErrorSym =
          CryptoVerification.SpqrV1.Alloc.spqrHandleErrorSym by decide) ▸
      ((cliGhostExterns_other gh (cliExternsPlaced mmpl W)
          (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)).trans
        (CryptoVerification.SignalSession.Cli.Slots.cliExternsPlaced_panic_handle_error mmpl W)))
    ((show lsRustNoAllocShimSymCli =
          CryptoVerification.SpqrV1.Alloc.spqrRustNoAllocShimSym by decide) ▸
      (⟨ProofLib.hookNoop,
        (cliGhostExterns_shim gh _).trans (congrArg some hG.shim_eq),
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShim_hookOk⟩ :
        HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
          lsRustNoAllocShimSymCli
          LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimSpec))
    ((show lsRustAllocSymCli = CryptoVerification.SpqrV1.Alloc.spqrRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show lsRustReallocSymCli = CryptoVerification.SpqrV1.Alloc.spqrRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hG)

private noncomputable def etjo_w4TargetEnvOf
    (_Out1Dom : H7RAOut1DomPred) (_X : UnreachedPqxdhPrimitives) (_W : CliHooks)
    (_γ : GhostName) (_tp : BitVec 64) (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
    w4.base.peer.val = x.peer.val ∧
    w4.base.peer.name.bytes.length ≤ 40 ∧
    w4.base.files = x.F ∧
    w4.base.rd = cliIo.rd ∧
    W4RecvPrekeyCmkDom0Of'
      w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps
      sessionCapBytes msgCapBytes w4.base ∧
    W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
      w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps w4 evs

/-- Establishes `MainOkOverD3F3` on `cliElfBytes` from unbundled ghost-witness field hypotheses. -/
theorem hole_m24slot_overD3_assembly_closed
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (ghFixed : CliGhostHooks)
    (hookStack : Nat)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (hMainStk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk)
    (hTrFrozen : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostSpqrAllocHooks fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hReadSat : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
        (readFileSpecPlaced cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none)))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd))
    (hHooksBundle : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd))
    (_hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (_hSpqr : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        mmpl ghFixed W
        (InitialStateEnv W.C.F)
        (CliSpqrRecvTightLinkedEnv W)
        (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K)) :
    MainOkOverD3F3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  exact h7ra_overD3_wire_tightRaw_of_out1Dom
    hLs hblk hext_nodup ghFixed (default : Image)
    PostBobPrev1Dom
    etjo_w4TargetEnvOf
    (fun W => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K)
    (fun W => gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K)
    (fun _γ _tp W => w4s2_TryDecryptTopStateGuardedEnv W)
    fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak fits2_zbDom0'MaxReq fits2_zbDom0'GrpS109
    rfl
    hTrFrozen
    (letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
     fun γ tp => (hGSpqr γ tp).toCliGhostAllocHooks)
    hioOf
    hMainStk
    hHooksBundle
    (fun W γ tp g peerV peerG meG fsp hp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      have hEq := congrArg
        (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) =>
          f (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [← hEq]
      exact hole3_encEnv_r2_congr W (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        g peerV peerG meG fsp hp)
    (fun W γ tp g fsp w peerV meG msgG m => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      have hEq := congrArg
        (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) =>
          f (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [← hEq]
      exact hole3_decSigEnv_r3a_congr W (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        g fsp w peerV meG msgG m)
    (fun h547 X W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      have hEq := congrArg
        (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) =>
          f (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [← hEq]
      exact hole3_w1_inner hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
        (hGSpqr γ tp) hFs (hReadSat W γ tp) (hHooksBundle W γ tp) h547)
    (fun h547 X W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      have hEq := congrArg
        (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) =>
          f (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [← hEq]
      exact hole3_w2_inner hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
        (hGSpqr γ tp) hFs (hReadSat W γ tp) (hHooksBundle W γ tp) h547)
    (fun h547 X W γ tp =>
      hole3_w3_init hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
        (hGSpqr γ tp) hFs (hReadSat W γ tp) hghNoAlloc (hHooksBundle W γ tp) h547)
    (fun _h547 W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact (w4f_pollCallees_of_f3Hooks mmpl ghFixed W γ tp cliElfImage.brkStart
        hPl_mng (hGSpqr γ tp) (hReadSat W γ tp) (hHooksBundle W γ tp)).hReadPoll)
    (fun _h547 W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact etjo_hDeserHelpers mmpl ghFixed W γ tp cliElfImage.brkStart
        (hGSpqr γ tp).toCliGhostAllocHooks)
    (fun _h547 W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact (w4f_pollCallees_of_f3Hooks mmpl ghFixed W γ tp cliElfImage.brkStart
        hPl_mng (hGSpqr γ tp) (hReadSat W γ tp) (hHooksBundle W γ tp)).hRaw)
    (fun _h547 W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact etjo_growOneVecU8_lsProg51_withLsCl_ok mmpl ghFixed W
        (hGSpqr γ tp).toCliGhostAllocHooks)
    (fun _h547 W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact (w4f_pollCallees_of_f3Hooks mmpl ghFixed W γ tp cliElfImage.brkStart
        hPl_mng (hGSpqr γ tp) (hReadSat W γ tp) (hHooksBundle W γ tp)).hAesDec)
    (fun _h547 W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact w4s2_spqrSeams_topStateGuarded mmpl ghFixed hPl_mng W γ tp cliElfImage.brkStart
        (hGSpqr γ tp))
    (fun W stBs msgBs => w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty W.C.F W.Q.K stBs msgBs)
    (fun _W _γ _tp _a _evs h => h)
    (fun _h547 W => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact ckx2_w1EncExact_phaseCredit W)
    (fun _h547 W => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact ckx2_w1EncExact_groupSpec W)
    (fun _h547 X W γ tp _g _meV peerV _rest _pm x'
        hi hp _hin _hc _hstdin _hpk hct _hp640 _hprev0 hx'F hx'p hx'm evs hevs => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      have hct' : x'.msg.message.ciphertext.length ≤ msgCapBytes :=
        (congrArg (fun m => m.message.ciphertext.length) hx'm).trans_le hct
      obtain ⟨w4, hw4Dom, _hrem, _hbase, henvFixed⟩ :=
        h7w_decPkValidOverTight_sub_zbDom0'FixedOf
          (SR := w4c_repairedStatesRecvEnvFam)
          (LoopAdvEnv := CmkLoopAdvanceEvs)
          (maxOps := w4c_defaultDecodeMaxOps)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc W X
          (tdEnv := fun W' => w4s2_TryDecryptTopStateGuardedEnv W')
          (fun a e hTop _hct_a he => by
            rw [w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top W a hTop] at he
            exact he)
          hi hp hx'F hx'p hct' evs hevs
      obtain ⟨hpv, hp40, hfiles, hrd, hd0⟩ := hw4Dom peerV rfl
      have henvAll :
          W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
            w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps w4 evs := by
        rwa [w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed_of_cliPqOrD3RecvDom hi hfiles hrd]
      exact ⟨w4, hpv, hp40, hfiles, hrd, hd0, henvAll⟩)
    (fun _h547 _X W _γ _tp _g _meV peerV _rest _pm hi _hp _hct _hp640 _hprev0 => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      refine (w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec' (c := .recv peerV) hi).credit.of_imp ?_
      rintro evs ⟨w4, hpv, hp40, hfiles, hrd, hd0, henvAll⟩
      refine ⟨w4, ?_, henvAll⟩
      intro p hp_eq; cases hp_eq
      exact ⟨hpv, hp40, hfiles, hrd, hd0⟩)
    (Nat.le_refl _)
    (fun _h547 _X W _γ _tp _g _meV peerV _rest _pm hi _hp _hct _hp640 _hprev0 => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      refine (w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec' (c := .recv peerV) hi).groups.of_imp ?_
      rintro evs ⟨w4, hpv, hp40, hfiles, hrd, hd0, henvAll⟩
      refine ⟨w4, ?_, henvAll⟩
      intro p hp_eq; cases hp_eq
      exact ⟨hpv, hp40, hfiles, hrd, hd0⟩)
    (by unfold d3SlotMainFitsOneGiBOf; decide)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinOverD3
