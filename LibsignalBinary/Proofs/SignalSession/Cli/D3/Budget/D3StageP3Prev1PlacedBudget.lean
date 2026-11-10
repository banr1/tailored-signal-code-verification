/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Stage P3 (`Prev1`) and `try_decrypt` Dischargers for Non-Matching Overwrite

Discharges the Stage-P3 leaf callees (blocks `524`, `512`, `42`, `48`), `StageP3Prev1D3PlacedStmt`
(and its unconditional `[LibsignalFullPlacement]` variant `stageP3_prev1_d3_full_placed_ok`), and
block-`507` `overPollTryDecryptPlacedSpecTPTight` on `dpPollProgPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto SessionState SignalMessage SignalProtocolError)
open CryptoVerification (
  IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalPlacement lsHandleErrorSym
  lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsRustReallocSym
  ls_hook_ok_ultra_of_mem lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (
  genP3S5Model genP3S5ModelPanicProp
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (LsTokenInitM3)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  OverPrevEncOK overScratch stageP3Sub5ExtraPrePrev1
)
open CryptoVerification.CliHandshake.RespClosurePlaced (instIsLsBlockProg_518 lsProg_518)
open CryptoVerification.E2E (aesDecHookMallocng)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32 SpqrModel extHookStack rootStack)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost UuidParser decryptDraws uuidTryParse
)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
  lsRustReallocSymCli
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_shim
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit dpPollEntryPlaced dpPollProgPlaced
)
open CryptoVerification.SignalSession.Cli.Slots (
  cliGhostExterns_panic_handle_error cliGhostExterns_sat_of_cliExternsPlaced
)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (aesDecBudgetSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget (
  TryDecryptCliEnv tryDecryptPqV1_placed_ok_PTight_cli_at_block
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  ChainClone3OkPlaced SenderChainClone3OkPlaced
  chainClone3_placed_ok_of_hooks senderChainClone3_placed_ok_of_hooks
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget (
  drop_session_structure4_placed_ok_at
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  StageP3ErrM3Env StageP3OkPrefixM3Env grow_one_spe_placed_ok_at
  pollTryDecryptM3PlacedSpecP pollTryDecryptM3PlacedSpecTPTight set_session_state_placed_ok_at
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget (
  OverVerNe1e04CliAtFrozenPlacedBody OverVerNe1e04CliAtPlacedBody
  overVerNe1e04CliAtFrozenPlacedBody_of_hooks_chain5 overVerNe1e04CliAtPlacedBody_of_hooks_chain5
  stageP3Gen_prev1_vregs_at_full_placed_ok stageP3Gen_prev1_vregs_at_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlacedBudget (
  chainMerge5CroPlacedOkExt_cli
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget (
  pqxdhLogClosurePlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux (VerNeTopEnv)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget (
  hookSat_noAllocShimBudget_of_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  overGenP3Pre_placed overGenP3S5PostFrame_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  overPollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  overStageP3ErrPostPrevEmptyAt_placed stageP3DispatchOkMidPrev1At_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  pollTryDecryptPlacedSpecP pollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_framelessMemcpy_budget_sat cliExternsPlaced_noAllocShim_budget_sat
  cliExternsPlaced_realloc_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat
  cliExternsPlaced_sessionMemmove_budget_sat cliExternsPlaced_shim_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeams)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec growOneSpeSpec setSessionStateSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. `cliGhostExterns gh (cliExternsPlaced mmpl W)` Hook & Leaf-Callee Witnesses -/

private theorem hookNoop_rustAllocShimVm_hookOk : HookOk hookNoop rustAllocShimVmSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  dsimp only [rustAllocShimVmSpec, hookNoop, retHook, id_eq] at hpre ⊢
  rw [emp_sepConj] at hpre
  rw [satisfies_pure_sepConj]
  exact ⟨⟨⟨by cases s0; rfl, by cases s0; rfl, by cases s0; rfl, by cases s0; rfl,
    by cases s0; rfl, by cases s0; rfl, by cases s0; rfl⟩,
    ⟨⟨by cases s0; rfl, by cases s0; rfl, by cases s0; rfl⟩,
     by cases s0; rfl, fun _ => by cases s0; rfl, fun _ _ _ => by cases s0; rfl⟩⟩, hpre⟩

private theorem cli_rustAllocShimVm_sat (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (hShim : gh.shim = hookNoop) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      rustAllocShimVmSpec :=
  (show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
    ⟨hookNoop, (cliGhostExterns_shim gh (cliExternsPlaced mmpl W)).trans (congrArg some hShim),
      hookNoop_rustAllocShimVm_hookOk⟩

private theorem cli_framelessMemcpy_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (hG : CliGhostAllocHooks M A lim gh) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsMemcpySym
      framelessMemcpyBudgetSpec := by
  rcases cliExternsPlaced_framelessMemcpy_budget_sat mmpl gh W hG with ⟨f, hf, hok⟩
  refine (show ("memcpy" : String) = lsMemcpySym by decide) ▸ ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

/-- Block-`524` `ChainClone3OkPlaced` at `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliChainClone3_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    ChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  chainClone3_placed_ok_of_hooks
    ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
      cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
      cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)

/-- Block-`524` `SenderChainClone3OkPlaced` at `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliSenderChainClone3_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    SenderChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  senderChainClone3_placed_ok_of_hooks
    ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
      cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
      cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)

/-- Caller-lifted Block-`512` `dropSessionStructureLocal2Spec M A lim` at `cliGhostExterns`. -/
theorem cliDropSessionStructure4_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_ok_at
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
    hi

/-- Block-`42` `growOneSpeSpec M A lim` on `lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem cliGrowOneSpe_518_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) :=
  grow_one_spe_placed_ok_at
    ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
      hookSat_noAllocShimBudget_of_withVmPreserved
        (cliExternsPlaced_noAllocShim_budget_sat mmpl gh W hG.shim_eq))
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show lsRustReallocSymCli = lsRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hG)

/-- Block-`48` `setSessionStateSpec M A lim` on `lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem cliSetSessionState_518_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)) :=
  set_session_state_placed_ok_at
    ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
      cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)

private theorem pollTryDecryptM3PlacedSpecTPTight_eq_over [LibsignalPlacement]
    {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    pollTryDecryptM3PlacedSpecTPTight C A lim ctl uuidParse S tdEnv =
      overPollTryDecryptPlacedSpecTPTight C A lim ctl uuidParse S tdEnv := by
  dsimp only [pollTryDecryptM3PlacedSpecTPTight, overPollTryDecryptPlacedSpecTPTight,
    pollTryDecryptPlacedSpecTPTight, pollTryDecryptM3PlacedSpecP, pollTryDecryptPlacedSpecP,
    LsTokenInitM3, LsTokenInit]
  rfl

/-! ## 2. `StageP3Prev1D3PlacedStmt` & `stageP3_prev1_d3_placed_ok` -/

/-- Budget-threaded `[LibsignalPlacement]` `StageP3Prev1D3AtPlacedStmt` over `RustCliAllocBudget M`
and `PrevEncOK`, parameterized over the honest binary Stage-P3 `Prev1` envelopes
(`StageP3Prev1Env`, `StageP3OkPrefixM3Env`, `StageP3ErrM3Env`, `StageP3VerNePrev1Env VerNeTopEnv`)
and eliminating `allocFailedIn` from `onPanic` (`genP3S5ModelPanicProp`). -/
def StageP3Prev1D3AtPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (st_b : M.σ),
    CliGhostAllocHooks M A lim gh →
    AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    ChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    SenderChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b
        (StageP3Prev1Env (tdEnv W) VerNeTopEnv recG st rem loc msgG msg msgVer enc rest) →
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      PrevEncOK enc →
      st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrev1At_placed A lim (M.stepEvents evs_p3 st_b) s0 s s'
            coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr enc pt b_2c0 G'
            (genP3S5Model W.C W.Q.K rem loc msg rest st).2 ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws W.C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf
            coroPtr outPtr e ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws W.C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_p3 : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNePrev1Env VerNeTopEnv recG st enc evs_p3 →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr
            outPtr (.invalidMessage .preKey .decryptionFailed) ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg (coinsAtPlaced cur rest) ∗
          overScratch s.sp ∗
          anyHeap) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (s0.readReg64 .x30) s
        (LsTokenInit ∗
          overGenP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr
            locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            enc b_2c0 ∗
          overScratch s.sp ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)

/-- `StageP3Prev1D3AtPlacedStmt` specialized to `OverPrevEncOK`. -/
abbrev StageP3Prev1D3PlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  StageP3Prev1D3AtPlacedStmt A lim tdEnv OverPrevEncOK

/-- Discharges `OverVerNe1e04CliAtPlacedBody` on `cliGhostExterns gh (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks` and Block-`519` `pqxdhLogClosurePlacedSpec`. -/
theorem cliVerNe1e04_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (hLog519 : subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)) :
    OverVerNe1e04CliAtPlacedBody A lim OverPrevEncOK VerNeTopEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  overVerNe1e04CliAtPlacedBody_of_hooks_chain5 (fun _ h => h)
    (cliGhostExterns gh (cliExternsPlaced mmpl W))
    hLog519
    (cliGrowOneSpe_518_placed_ok mmpl gh W hG)
    (cliDropSessionStructure4_placed_ok_at
      (callerProg := lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (i := 518) mmpl gh W hG (by decide))
    (cli_rustAllocShimVm_sat mmpl gh W hG.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show lsRustReallocSymCli = lsRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hG)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
    (cli_framelessMemcpy_sat mmpl gh W hG)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_sessionMemmove_budget_sat mmpl W extHookStack))
    (cliGhostExterns_panic_handle_error mmpl gh W)
    (chainMerge5CroPlacedOkExt_cli mmpl gh W hG)

/-- Discharges `StageP3Prev1D3AtPlacedStmt` from `hLog519` and `hVerNeAt`. -/
theorem stageP3Prev1D3_placed_of_verNeAt [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {PrevEncOK : List (BitVec 8) → Prop}
    (hLog519 : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim gh →
      subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hVerNeAt : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim gh →
      AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
      OverVerNe1e04CliAtPlacedBody A lim PrevEncOK VerNeTopEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP3Prev1D3AtPlacedStmt A lim tdEnv PrevEncOK := by
  intro mmpl gh W st_b hG hAllocX hcc hscc hroot hDropSS3 s0 s coroPtr ctxPtr outPtr initErrsPtr
    prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest recG st rem loc
    msgG msg F_frame Q hfits hinit hcap hprev hv4 hns hsd hrc hpq hcro hpc hrun hsp hroot_sp hfp
    htr hvregs hOk hErr hVerNe
  let ext := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hshim : subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym)
      sessionShimBudgetSpec :=
    ls_hook_ok_ultra_of_mem
      ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
        cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq)
      (by decide)
  have halloc : subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false) :=
    ls_hook_ok_ultra_of_mem
      ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
        cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
      (by decide)
  have hdealloc : subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_ultra_of_mem
      ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
        cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
      (by decide)
  have hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym)
      sessionMemcpyRegionBudgetSpec :=
    ls_hook_ok_ultra_of_mem
      ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
        cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)
      (by decide)
  have hrootM3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))) := by
    rw [pollTryDecryptM3PlacedSpecTPTight_eq_over]
    exact hroot
  exact stageP3Gen_prev1_vregs_at_placed_ok ext W.C 0#64 W.Q.K
    hshim halloc hdealloc hmemcpy
    (cliGrowOneSpe_518_placed_ok mmpl gh W hG)
    (cliSetSessionState_518_placed_ok mmpl gh W hG)
    hDropSS3 (hLog519 mmpl gh W hG) hcc hscc hrootM3 (hVerNeAt mmpl gh W hG hAllocX hDropSS3)
    st_b s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr
    cur msgVer b_2c0 enc rest recG st rem loc msgG msg F_frame Q
    hfits hinit hcap hprev hv4 hns hsd hrc hpq hcro hpc hrun hsp hroot_sp hfp htr hvregs
    (fun G₁ G' pt ptCap ptPtr evs_ok s' P_s' => hOk G₁ G' evs_ok pt ptCap ptPtr s' P_s')
    (fun G₁ G' e evs_err sf P_f => hErr G₁ G' evs_err e sf P_f)
    (fun evs_vn sf P_f hver hevs hPf => hVerNe evs_vn sf P_f hver hevs
      (Entails.trans hPf (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
          (sepConj_mono_right (entails_anyHeap emp)))))))))

/-- Discharges `StageP3Prev1D3PlacedStmt A lim tdEnv` under `[LibsignalPlacement]` from the
Block-`519` mutated-callee seam `hLog519`. -/
theorem stageP3_prev1_d3_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (hLog519 : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim gh →
      subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)) :
    StageP3Prev1D3PlacedStmt A lim tdEnv :=
  stageP3Prev1D3_placed_of_verNeAt hLog519
    (fun mmpl gh W hG _ _ => cliVerNe1e04_placed_ok mmpl gh W hG (hLog519 mmpl gh W hG))

/-! ## 3. Block-`507` `overPollTryDecryptPlacedSpecTPTight` Pointwise Discharger -/

/-- Discharges Block-`507` `overPollTryDecryptPlacedSpecTPTight` at
`TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)` on `dpPollProgPlaced` from `CliGhostAllocHooks`,
`aesDecBudgetSpec`, and `SpqrV1PlacedSeams`. -/
theorem over_tryDecrypt_cli_placed_ok_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
          (spqrV1 W.C.F W.Q.K) (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))) :=
  tryDecryptPqV1_placed_ok_PTight_cli_at_block
    (callerProg := lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
    mmpl gh W ctl hG hAesDec hSpqr (by decide)

/-! ## 4. `[LibsignalFullPlacement]` / `LibsignalFrozen` Variants -/

/-- `LibsignalFrozen`-guarded `StageP3Prev1D3AtFrozenPlacedStmt` over `RustCliAllocBudget M` and
`PrevEncOK` (`s.mem` guarded by `LibsignalFrozen`, `s'.mem` / `sf.mem` guarded by
`LibsignalCodeRoLoaded`). -/
def StageP3Prev1D3AtFrozenPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (st_b : M.σ),
    CliGhostAllocHooks M A lim gh →
    AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    ChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    SenderChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b
        (StageP3Prev1Env (tdEnv W) VerNeTopEnv recG st rem loc msgG msg msgVer enc rest) →
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      PrevEncOK enc →
      st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      LibsignalFrozen lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrev1At_placed A lim (M.stepEvents evs_p3 st_b) s0 s s'
            coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr enc pt b_2c0 G'
            (genP3S5Model W.C W.Q.K rem loc msg rest st).2 ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws W.C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf
            coroPtr outPtr e ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws W.C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_p3 : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNePrev1Env VerNeTopEnv recG st enc evs_p3 →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr
            outPtr (.invalidMessage .preKey .decryptionFailed) ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg (coinsAtPlaced cur rest) ∗
          overScratch s.sp ∗
          anyHeap) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (s0.readReg64 .x30) s
        (LsTokenInit ∗
          overGenP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr
            locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            enc b_2c0 ∗
          overScratch s.sp ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)

/-- `StageP3Prev1D3AtFrozenPlacedStmt` specialized to `OverPrevEncOK`. -/
abbrev StageP3Prev1D3FrozenPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  StageP3Prev1D3AtFrozenPlacedStmt A lim tdEnv OverPrevEncOK

/-- Discharges `OverVerNe1e04CliAtFrozenPlacedBody` on
`cliGhostExterns gh (cliExternsPlaced mmpl W)` under `[LibsignalFullPlacement]`. -/
theorem cliVerNe1e04_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    OverVerNe1e04CliAtFrozenPlacedBody A lim OverPrevEncOK VerNeTopEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  overVerNe1e04CliAtFrozenPlacedBody_of_hooks_chain5 (fun _ h => h)
    (cliGhostExterns gh (cliExternsPlaced mmpl W))
    (cliGrowOneSpe_518_placed_ok mmpl gh W hG)
    (cliDropSessionStructure4_placed_ok_at
      (callerProg := lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (i := 518) mmpl gh W hG (by decide))
    (cli_rustAllocShimVm_sat mmpl gh W hG.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show lsRustReallocSymCli = lsRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hG)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
    (cli_framelessMemcpy_sat mmpl gh W hG)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_sessionMemmove_budget_sat mmpl W extHookStack))
    (cliGhostExterns_panic_handle_error mmpl gh W)
    (chainMerge5CroPlacedOkExt_cli mmpl gh W hG)

/-- Discharges `StageP3Prev1D3AtFrozenPlacedStmt` under `[LibsignalFullPlacement]` from `hVerNeAt`. -/
theorem stageP3Prev1D3_full_placed_of_verNeAt [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {PrevEncOK : List (BitVec 8) → Prop}
    (hVerNeAt : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim gh →
      AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
      OverVerNe1e04CliAtFrozenPlacedBody A lim PrevEncOK VerNeTopEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP3Prev1D3AtFrozenPlacedStmt A lim tdEnv PrevEncOK := by
  intro mmpl gh W st_b hG hAllocX hcc hscc hroot hDropSS3 s0 s coroPtr ctxPtr outPtr initErrsPtr
    prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest recG st rem loc
    msgG msg F_frame Q hfits hinit hcap hprev hv4 hns hsd hrc hpq hfr hpc hrun hsp hroot_sp hfp
    htr hvregs hOk hErr hVerNe
  let ext := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hshim : subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym)
      sessionShimBudgetSpec :=
    ls_hook_ok_ultra_of_mem
      ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
        cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq)
      (by decide)
  have halloc : subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false) :=
    ls_hook_ok_ultra_of_mem
      ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
        cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
      (by decide)
  have hdealloc : subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_ultra_of_mem
      ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
        cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
      (by decide)
  have hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym)
      sessionMemcpyRegionBudgetSpec :=
    ls_hook_ok_ultra_of_mem
      ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
        cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)
      (by decide)
  have hrootM3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))) := by
    rw [pollTryDecryptM3PlacedSpecTPTight_eq_over]
    exact hroot
  exact stageP3Gen_prev1_vregs_at_full_placed_ok ext W.C 0#64 W.Q.K
    hshim halloc hdealloc hmemcpy
    (cliGrowOneSpe_518_placed_ok mmpl gh W hG)
    (cliSetSessionState_518_placed_ok mmpl gh W hG)
    hDropSS3 hcc hscc hrootM3 (hVerNeAt mmpl gh W hG hAllocX hDropSS3)
    st_b s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr
    cur msgVer b_2c0 enc rest recG st rem loc msgG msg F_frame Q
    hfits hinit hcap hprev hv4 hns hsd hrc hpq hfr hpc hrun hsp hroot_sp hfp htr hvregs
    (fun G₁ G' pt ptCap ptPtr evs_ok s' P_s' => hOk G₁ G' evs_ok pt ptCap ptPtr s' P_s')
    (fun G₁ G' e evs_err sf P_f => hErr G₁ G' evs_err e sf P_f)
    (fun evs_vn sf P_f hver hevs hPf => hVerNe evs_vn sf P_f hver hevs
      (Entails.trans hPf (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
          (sepConj_mono_right (entails_anyHeap emp)))))))))

/-- Unconditional discharge of `StageP3Prev1D3FrozenPlacedStmt A lim tdEnv` under `[LibsignalFullPlacement]`. -/
theorem stageP3_prev1_d3_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop} :
    StageP3Prev1D3FrozenPlacedStmt A lim tdEnv :=
  stageP3Prev1D3_full_placed_of_verNeAt
    (fun mmpl gh W hG _ _ => cliVerNe1e04_full_placed_ok mmpl gh W hG)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget
