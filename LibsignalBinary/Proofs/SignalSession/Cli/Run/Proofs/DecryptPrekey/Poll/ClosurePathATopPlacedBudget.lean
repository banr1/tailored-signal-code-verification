/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATop
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll New-Session Path A Top-Level Branch

Defines budget-threaded `StageP2PathAQpanCliPlacedStmt` over `StageP2PathAEnv` and proves
`stageP3_exit_pathA_to_pollPost_placed` and `closure_pathA_placed_ok` (plus `LibsignalFrozen`
variants) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp Bytes eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced
open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Coins.Placed
open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  StageP2PathAQpanCliPlacedStmt
  stageP3_exit_pathA_to_pollPost_placed
  closure_pathA_placed_ok
  StageP2MatchedFramedCliPlacedStmt
  storesAt_opened_entails_cliPollStoresKitsAtPlaced
  sepWPp_pollGoal_frame_placed
  stageP3_exit_prevEmpty_to_pollPost_placed
  sepWPp_genP3_to_tailQpan_placed
  closure_pathB_placed_ok
  cliFiles_eq_of_trace_eq_placed
  cliPollStageP1_fsAt_placed
  cliPollStageP4Stack_placed_le_subStack
  cliPollStageP4MatchedStack_placed_le_subStack
  cliPollStageP4_fsAt_placed
  closure_pathA_p4_cont_placed
  stageP3ErrPathA_entails_exit_placed
  stageP3ErrPrevEmpty_entails_exit_placed
  pathAP4RemAtPlaced
  pathBP4RemAtPlaced
  stageP3MidPathA_eq_p4_placed
  stageP3MidPrevEmpty_eq_p4_placed
  stageP4PathAExit_entails_exit_placed
  stageP4MatchedExit_entails_exit_placed
  exit_entails_dpPollPost_placed
  sepWPp_genP3_to_pollGoal_placed
  closure_pathB_p4_cont_placed
  genP3Pre_placed genP3CallFrame_placed genP3S5PostFrame_placed
  stageP3DispatchOkMid_placed stageP3ErrPost_placed
  stageP3DispatchOkMidPrevEmpty_placed stageP3ErrPostPrevEmpty_placed
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced
  StageP4RawBranchPlaced StageP4BranchPlaced StageP4PathAPlacedStmt
  stageP4MatchedSharedPlaced stageP4MatchedPrePlaced stageP4MatchedExitAtPlaced
  StageP4MatchedBranchPlaced StageP4MatchedPlacedStmt
  StageP2PathAErrPlaced StageP2PathACliPlacedStmt
  StageP3PrevEmptyVRegsPlacedStmt StageP3GenStepsVRegsPlacedStmt CliTryDecryptPqV1PlacedStmt
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (PreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (KyberPreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  chainClone3_placed_ok_of_hooks senderChainClone3_placed_ok_of_hooks
)
open CryptoVerification.SignalSession.Cli.Slots (cliGhostExterns_sat_of_cliExternsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  cliExternsPlaced_sessionMemcpyRegion_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  ChainClone3OkPlaced SenderChainClone3OkPlaced
  genP3Pre_placed genP3S5PostFrame_placed
  stageP3DispatchOkMid_placed stageP3ErrPost_placed
  StageP3Env StageP3OkPrefixEnv StageP3ErrEnv StageP3VerNeEnv
  pollTryDecryptPlacedSpecTPTight StageP3GenStepsVRegsPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced StageP2PathAEnv StageP2PathAErrPlaced
  StageP4PathAEnv StageP4PathAStoreStepEnv StageP4PathAMarkErrEnv StageP4PathAPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAPlacedBudget (
  stageP3ErrPathA_entails_exit_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget (
  cliFiles_eq_of_trace_eq_placed exit_entails_dpPollPost_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget (
  storesAt_opened_entails_cliPollStoresKitsAtPlaced
  sepWPp_pollGoal_frame_placed
  sepWPp_genP3_to_tailQpan_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4ContPlacedBudget (
  closure_pathA_p4_cont_placed
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Budget-Threaded General-`Qpan` CPS Stage P2 Statement for Path A (`StageP2PathAQpanCliPlacedStmt`) -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` general-`Qpan` CPS Stage P2 contract for
Path A (`opt = none`, `DecPkOk₀`): rules out Stage-P2 OOM panics via
`FitsEnv M lim st_b (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g)` so `hok` continues directly
into Stage P3 (`genP3S5ModelPanicProp`). -/
def StageP2PathAQpanCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {st_b : M.σ}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv) →
    FitsEnv M lim st_b (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → Slots.scopeIn r') →
    Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
    Slots.loadRec Scope y.g.F y.g.peer.val = .ok none →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 →
    StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    dpClosSubStack B ≤ sp.toNat →
    s1.pc = dpPollEntryPlaced + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2PathAErrPlaced A lim st_b P2PathAErrEnv X W B S Scope y s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (evs : List AllocEvent) (s2 : State)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (recG : SessionGhost)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2PathAOkEnv y.g evs →
      whisperG = y.g.msgG.msg →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG
        (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = dpPollEntryPlaced + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         genP3Pre_placed A lim (M.stepEvents evs st_b) s2.sp (s2.readReg64 .x29) y.fut y.cx
           y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A.repAlloc y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores g1 ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

private theorem hookSat_sessionMemcpyRegionBudget_of_codec {H : LibsignalHooks}
    (h : HookSat H CryptoVerification.lsMemcpySym
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · exact ⟨hkeep, hsym, Or.inl ⟨hret, hcc, hpost⟩⟩
  · exact ⟨hkeep, hsym, Or.inr hrest⟩

private theorem cliChainClone3_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    ChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  chainClone3_placed_ok_of_hooks
    ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)

private theorem cliSenderChainClone3_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    SenderChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  senderChainClone3_placed_ok_of_hooks
    ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)

/-! ## 2. Stage P3 `hErr` / `hVerNe` Exit Packaging on Path A -/

set_option maxHeartbeats 800000 in
/-- Packages both `hErr` and `hVerNe` exits of `StageP3GenStepsVRegsPlacedStmt` on Path A into
`dpPollSpecStateBudget.post` under `[LibsignalPlacement]`. -/
theorem stageP3_exit_pathA_to_pollPost_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (evs : List AllocEvent)
    (s0 s2 sf : State)
    (rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost P_f R : SepProp)
    (opkId? : Option (BitVec 32))
    (kpkId spkId : BitVec 32)
    (e : SignalProtocolError)
    (hevs : DecPkEnv y.g evs)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hdec : decPkDef X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none)
    (hent : P_f ⊢
      ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      memRegion (s2.sp + 0x3e0#64) 344 ∗
      stageP3ErrPost_placed A lim (M.stepEvents evs y.st) s0 s2 sf y.fut y.out 8#64 e ∗
      genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        coinsPost)
    (hsf_sp : sf.sp = s2.sp + 0xcd0#64)
    (htr_f : sf.trace = s0.trace)
    (hcs_f : ClosureCalleeSaved s0 sf)
    (hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut opkId?)
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    let Fr_tail : SepProp :=
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32
    (Steps prog s0 sf → (sf.mem ⊨ (P_f ∗ F_p3) ∗ (Fr_tail ∗ R)) →
      (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .decryptionFailed)
  have hsf_sp0 : sf.sp = s0.sp := by rw [hsf_sp, hs2_sp, sp_frame_sub_add]
  have hcs_full : CalleeSavedPreserved s0 sf :=
    closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
  refine ⟨?_, hsf_sp0, hcs_full⟩
  intro hsteps0f hm_f
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm_f
  rw [hs2_sp] at hm1
  have hexit := stageP3ErrPathA_entails_exit_placed A lim (M.stepEvents evs y.st) B y s0 s2 sf
    rngPtr whisperMsgPtr whisperG preKeyMsgRem coinsPost opkId?
    (y.g.msg.message.messageVersion.zeroExtend 32) kpkId spkId e err
    StoresGhost.opened hs2_sp hsp_sub hmsg_fold
  dsimp only at hexit
  have hm2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm1
  have hm3 : sf.mem ⊨
      (decResAt A.repAlloc y.out (.error err) ∗
        storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        FromRecordCallees.lsLogOff ∗
        A.pool lim (M.stepEvents evs y.st) sf ∗
        (LsTokenInit ∗ coinsPost) ∗
        dpFutDoneAt y.fut ∗
        memRegion y.cx 32 ∗
        memRegion sp 3280 ∗
        stackAt sp (dpClosSubStack B) ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
    Arm64.Satisfies.mono (by dsimp only [sp]; sep_frame) hm2
  have hout : slotOutTr
      (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      StoresGhost.opened (.error err) s0.trace sf.trace :=
    slotOutTr_of_reject StoresGhost.opened hS (err := err) nofun nofun hdec
  have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
    evs StoresGhost.opened (.error err) (LsTokenInit ∗ coinsPost) hevs hh hsteps0f htr_f hout
  exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm3

/-! ## 3. Top-Level New-Session Path A Branch (`closure_pathA_placed_ok`) -/

set_option maxHeartbeats 1000000 in
/-- Budget-threaded top-level new-session Path A branch (`opt = none`) from
`dpPollEntryPlaced + 0x0868#64` to `s0.readReg64.x30`. -/
theorem closure_pathA_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hP2A : StageP2PathAQpanCliPlacedStmt)
    (hP3 : StageP3GenStepsVRegsPlacedStmt)
    (hP4 : StageP4PathAPlacedStmt)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kitEnv : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)))
    (pkKitEnv : PreKeyStoreBudgetEnv
      (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)))
    (kpkKitEnv : ∀ kpkId spkId, KyberPreKeyStoreBudgetEnv
      (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey (cliKitStk B)))
    (evs_p1 : List AllocEvent)
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok none))
    (hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g))
    (hevs_p2_err : ∀ evs_p2, P2PathAErrEnv y.g evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2))
    (hfits_p3 : ∀ evs_p2 m i k kp reg dk recG,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
        (StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
          y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins))
    (hfits_p4 : ∀ evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      FitsEnv M lim (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st)
        (StageP4PathAEnv
          (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
          (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)) pkKitEnv
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
            (kpkKitEnv m.kpkId m.spkId)
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          y.g.peer.val y.g.msg.identityKey m.opkId m.kpkId m.spkId y.g.msg.baseKey
          { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
            state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
              (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
            pendingPreKey := none
            pendingKyberPreKey := none }))
    (hevs_ok : ∀ evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      StageP4PathAStoreStepEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)) pkKitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (kpkKitEnv m.kpkId m.spkId)
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.opkId m.kpkId m.spkId y.g.msg.baseKey
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
          pendingPreKey := none
          pendingKyberPreKey := none } evs_p4 →
      DecPkEnv y.g (((evs_p1 ++ evs_p2) ++ evs_p3) ++ evs_p4))
    (hevs_markErr : ∀ evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      StageP4PathAMarkErrEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (kpkKitEnv m.kpkId m.spkId)
        StoresGhost.opened.identity StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey evs_p4 →
      DecPkEnv y.g (((evs_p1 ++ evs_p2) ++ evs_p3) ++ evs_p4))
    (hevs_err : ∀ evs_p2 m i k kp reg dk recG G₁ G' evs_p3 e,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
      G₁.AfterTryDecrypt false G' →
      StageP3ErrEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .error e →
      e ≠ .panic →
      DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3))
    (hevs_verNe : ∀ evs_p2 m i k kp reg dk recG evs_p3,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version ≠
        y.g.msg.message.messageVersion.zeroExtend 32 →
      StageP3VerNeEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) evs_p3 →
      DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3))
    (hsteps01 : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1)
    (htr1 : s1.trace = s0.trace)
    (hro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  dsimp only [cliPollSessKitPlaced] at hload_rel
  have hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok none :=
    loadRec_of_cliPollSess_loadRel (A := A.repAlloc) (b := 0#64) (σ := σ)
      hinjK hsub hfPeer hload_rel
  have hcur : (none : Option (SessionRecord (List (BitVec 8)))).bind (·.currentSession) = none := rfl
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  have hs1_files : s1.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps01 htr1).trans hf0
  have hfiles1 : FsAt (fun f => f = y.g.F) True
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 :=
    .inr ⟨trivial, hh.fs (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) 518, hs1_files⟩
  let Fr_tail : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hpre_split :
      stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B)) ∗ Fr_tail := by
    dsimp only [Fr_tail]
    sep_frame
  refine sepWPp_conseq_pre hpre_split
    (sepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine hP2A mmpl gh X W B S Scope y StoresGhost.opened s0 s1 sp rngPtr v_a8 v_b8 v_d0 _ _
    hh hReadFile hDeser hfits_p2 hcoins hdecOk hsub hfPeer hloadS htrusted rfl hfiles1 hro1
    (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hsp_sub hpc1 hrun1 hsp_align1 hregs1 ?_ ?_
  · intro sf Pf _ _ _ hsf_sp hcs_f hvregs_f _ hErr
    rcases hErr with ⟨err, evs_p2, hevs_p2, hne_p, hne_s, htr_f, hmodel, hpost_f⟩
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hpost_f' :
        Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          stackAt sp (dpClosSubStack B) ∗
          anyHeap := by
      rw [M.stepEvents_append evs_p1 evs_p2 y.st]
      exact hpost_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left hpost_f') hm_f
    have hm2 : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          anyHeap ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [Fr_tail]; sep_frame) hm1
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject StoresGhost.opened hS hne_p hne_s hmodel
    have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
      (evs_p1 ++ evs_p2) StoresGhost.opened (.error err) anyHeap
      (hevs_p2_err evs_p2 hevs_p2) hh hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm2
  · intro evs_p2 s2 m i k kp reg dk recG whisperMsgPtr whisperG preKeyMsgRem
      hevs_p2 hwg_eq hpm_eq hi hk hkp hreg hacc hex hmsg_fold hsteps12 htr2 hpc2 hrun2
      hs2_sp hsp_align2 _ _ _ hvregs2 hro2
    subst hwg_eq
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
    obtain ⟨_hIn0, _hver4, hSeeds, hRC, hPqLt⟩ := pathAInitSession_scopeIn ⟨W.C, W.Q⟩ meE k m dk
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps02 htr20).trans hf0
    have hpan_model : st0.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).1 = .error .panic →
        (dpSlotPollKStatePlaced A lim DecPkEnv B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDef_pathA_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents evs_p2 (M.stepEvents evs_p1 y.st))
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
          F_p3 ⊢
        LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
          F_p3 := by
      rw [← M.stepEvents_append evs_p1 evs_p2 y.st]
      exact Entails.refl _
    refine sepWPp_conseq_pre hpre_p3
      (sepWPp_genP3_to_tailQpan_placed A lim DecPkEnv B S stk' y hpan_model ?_)
    refine hP3 (cliGhostExterns gh (cliExternsPlaced mmpl W)) W.C 0#64 W.Q.K
      hh.alloc (cliChainClone3_budget_placed_ok mmpl gh W hh)
      (cliSenderChainClone3_budget_placed_ok mmpl gh W hh)
      hTryDec
      s0 s2 y.fut y.cx y.out 8#64 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message F_p3 _
      (hfits_p3 evs_p2 m i k kp reg dk recG hevs_p2 hpm_eq hi hk hkp hreg hacc hex)
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdecOk)) hSeeds hRC hPqLt
      hro2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' evs_p3 pt ptCap ptPtr s' P_s' hver hcl hdec_rel hevs_p3 hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'
      have hent_s'' :
          P_s' ⊢
            stageP3DispatchOkMid_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 s' y.fut y.out 8#64 8#64
              ptCap ptPtr pt 0#8 G'
              (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2 ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_s'
      have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced A.repAlloc σ y.g.stores
        hsub hfPeer hdecOk (pid := pid) (sid := m.spkId) (kid := m.kpkId) (kbk := y.g.msg.baseKey)
      have hunpack_p3 : P_s' ∗ F_p3 ⊢
          P_s' ∗
          (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
              (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
              (coroOpkIdAtP4 y.fut m.opkId)
              (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
                ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
            stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
            ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
            ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRem ∗
            kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
            ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
            (cliPollPkKitPlaced A.repAlloc y.g.F pid σ).storeAt
              (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ).storeAt
              (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
              (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
            memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) := by
        dsimp only [F_p3]
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
        refine Entails.trans (sepConj_mono_left hstores_in) ?_
        dsimp only [cliPollStoresKitsAtPlaced]
        sep_frame
      exact sepWPp_conseq_pre hunpack_p3
        (closure_pathA_p4_cont_placed hP4 B S hh hReadFile hDeser hS stk' hneed hstk63 y
          hfPeer hdecOk hloadS hcur htrusted m i k kp reg dk
          kitEnv ikitEnv pkKitEnv (kpkKitEnv m.kpkId m.spkId)
          ((evs_p1 ++ evs_p2) ++ evs_p3) recG G₁ G'
          rngPtr whisperMsgPtr ptCap ptPtr y.g.msgG.msg preKeyMsgRem P_s' R pt s0 s2 s'
          hpm_eq hi hk hkp hreg hacc hex
          (hfits_p4 evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt
            hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 hok)
          (fun evs_p4 hevs_p4 =>
            hevs_ok evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4
              hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 hok hevs_p4)
          (fun evs_p4 hevs_p4 =>
            hevs_markErr evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4
              hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 hok hevs_p4)
          hmsg_fold hs2_files htr20 hs2_sp hsp_align2 hsp_sub
          hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
          hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'')
    · intro G₁ G' evs_p3 e sf P_f hver hcl hdec_rel hevs_p3 herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
            memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPost_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out 8#64 e ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_f
      exact stageP3_exit_pathA_to_pollPost_placed B S hh hS stk' hneed hstk63 y
        ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf
        rngPtr whisperMsgPtr y.g.msgG.msg preKeyMsgRem
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins))
        P_f R m.opkId m.kpkId m.spkId e
        (hevs_err evs_p2 m i k kp reg dk recG G₁ G' evs_p3 e
          hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 herr hne_p)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver herr hne_p)
        hent_f' hsf_sp htr_f hcs_f hvregs_f
    · intro evs_p3 sf P_f hver_ne hevs_p3 hent_f hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
            memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPost_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out 8#64
              (.invalidMessage .preKey .decryptionFailed) ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (coinsAtPlaced y.g.coinsP y.g.coins) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_f
      exact stageP3_exit_pathA_to_pollPost_placed B S hh hS stk' hneed hstk63 y
        ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf
        rngPtr whisperMsgPtr y.g.msgG.msg preKeyMsgRem (coinsAtPlaced y.g.coinsP y.g.coins)
        P_f R m.opkId m.kpkId m.spkId (.invalidMessage .preKey .decryptionFailed)
        (hevs_verNe evs_p2 m i k kp reg dk recG evs_p3
          hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver_ne hevs_p3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver_ne)
        hent_f' hsf_sp htr_f hcs_f hvregs_f

/-! ## `LibsignalFrozen` Variants -/

def StageP2PathAQpanCliFrozenPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {st_b : M.σ}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv) →
    FitsEnv M lim st_b (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → Slots.scopeIn r') →
    Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
    Slots.loadRec Scope y.g.F y.g.peer.val = .ok none →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 →
    CryptoVerification.LibsignalFrozen lsmpl s1.mem →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    dpClosSubStack B ≤ sp.toNat →
    s1.pc = dpPollEntryPlaced + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2PathAErrPlaced A lim st_b P2PathAErrEnv X W B S Scope y s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (evs : List AllocEvent) (s2 : State)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (recG : SessionGhost)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2PathAOkEnv y.g evs →
      whisperG = y.g.msgG.msg →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG
        (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = dpPollEntryPlaced + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      CryptoVerification.LibsignalFrozen lsmpl s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         genP3Pre_placed A lim (M.stepEvents evs st_b) s2.sp (s2.readReg64 .x29) y.fut y.cx
           y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A.repAlloc y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores g1 ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

set_option maxHeartbeats 1200000 in
theorem closure_pathA_frozen_placed_ok [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hP2A : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget.StageP2PathAQpanCliFrozenPlacedStmt)
    (hP3 : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.StageP3GenStepsVRegsFrozenPlacedStmt)
    (hP4 : StageP4PathAPlacedStmt)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kitEnv : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)))
    (pkKitEnv : PreKeyStoreBudgetEnv
      (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)))
    (kpkKitEnv : ∀ kpkId spkId, KyberPreKeyStoreBudgetEnv
      (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey (cliKitStk B)))
    (evs_p1 : List AllocEvent)
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok none))
    (hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g))
    (hevs_p2_err : ∀ evs_p2, P2PathAErrEnv y.g evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2))
    (hfits_p3 : ∀ evs_p2 m i k kp reg dk recG,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
        (StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
          y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins))
    (hfits_p4 : ∀ evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      FitsEnv M lim (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st)
        (StageP4PathAEnv
          (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
          (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)) pkKitEnv
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
            (kpkKitEnv m.kpkId m.spkId)
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          y.g.peer.val y.g.msg.identityKey m.opkId m.kpkId m.spkId y.g.msg.baseKey
          { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
            state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
              (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
            pendingPreKey := none
            pendingKyberPreKey := none }))
    (hevs_ok : ∀ evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      StageP4PathAStoreStepEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)) pkKitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (kpkKitEnv m.kpkId m.spkId)
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.opkId m.kpkId m.spkId y.g.msg.baseKey
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
          pendingPreKey := none
          pendingKyberPreKey := none } evs_p4 →
      DecPkEnv y.g (((evs_p1 ++ evs_p2) ++ evs_p3) ++ evs_p4))
    (hevs_markErr : ∀ evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      StageP4PathAMarkErrEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (kpkKitEnv m.kpkId m.spkId)
        StoresGhost.opened.identity StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey evs_p4 →
      DecPkEnv y.g (((evs_p1 ++ evs_p2) ++ evs_p3) ++ evs_p4))
    (hevs_err : ∀ evs_p2 m i k kp reg dk recG G₁ G' evs_p3 e,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
      G₁.AfterTryDecrypt false G' →
      StageP3ErrEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .error e →
      e ≠ .panic →
      DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3))
    (hevs_verNe : ∀ evs_p2 m i k kp reg dk recG evs_p3,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version ≠
        y.g.msg.message.messageVersion.zeroExtend 32 →
      StageP3VerNeEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) evs_p3 →
      DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3))
    (hsteps01 : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1)
    (htr1 : s1.trace = s0.trace)
    (hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  dsimp only [cliPollSessKitPlaced] at hload_rel
  have hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok none :=
    loadRec_of_cliPollSess_loadRel (A := A.repAlloc) (b := 0#64) (σ := σ)
      hinjK hsub hfPeer hload_rel
  have hcur : (none : Option (SessionRecord (List (BitVec 8)))).bind (·.currentSession) = none := rfl
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  have hs1_files : s1.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps01 htr1).trans hf0
  have hfiles1 : FsAt (fun f => f = y.g.F) True
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 :=
    .inr ⟨trivial, hh.fs (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) 518, hs1_files⟩
  let Fr_tail : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hpre_split :
      stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B)) ∗ Fr_tail := by
    dsimp only [Fr_tail]
    sep_frame
  refine sepWPp_conseq_pre hpre_split
    (sepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine hP2A mmpl gh X W B S Scope y StoresGhost.opened s0 s1 sp rngPtr v_a8 v_b8 v_d0 _ _
    hh hReadFile hDeser hfits_p2 hcoins hdecOk hsub hfPeer hloadS htrusted rfl hfiles1 hfr1
    (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hsp_sub hpc1 hrun1 hsp_align1 hregs1 ?_ ?_
  · intro sf Pf _ _ _ hsf_sp hcs_f hvregs_f _ hErr
    rcases hErr with ⟨err, evs_p2, hevs_p2, hne_p, hne_s, htr_f, hmodel, hpost_f⟩
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hpost_f' :
        Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          stackAt sp (dpClosSubStack B) ∗
          anyHeap := by
      rw [M.stepEvents_append evs_p1 evs_p2 y.st]
      exact hpost_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left hpost_f') hm_f
    have hm2 : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          anyHeap ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [Fr_tail]; sep_frame) hm1
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject StoresGhost.opened hS hne_p hne_s hmodel
    have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
      (evs_p1 ++ evs_p2) StoresGhost.opened (.error err) anyHeap
      (hevs_p2_err evs_p2 hevs_p2) hh hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm2
  · intro evs_p2 s2 m i k kp reg dk recG whisperMsgPtr whisperG preKeyMsgRem
      hevs_p2 hwg_eq hpm_eq hi hk hkp hreg hacc hex hmsg_fold hsteps12 htr2 hpc2 hrun2
      hs2_sp hsp_align2 _ _ _ hvregs2 hfr2
    subst hwg_eq
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
    obtain ⟨_hIn0, _hver4, hSeeds, hRC, hPqLt⟩ := pathAInitSession_scopeIn ⟨W.C, W.Q⟩ meE k m dk
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps02 htr20).trans hf0
    have hpan_model : st0.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).1 = .error .panic →
        (dpSlotPollKStatePlaced A lim DecPkEnv B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDef_pathA_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents evs_p2 (M.stepEvents evs_p1 y.st))
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
          F_p3 ⊢
        LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
          F_p3 := by
      rw [← M.stepEvents_append evs_p1 evs_p2 y.st]
      exact Entails.refl _
    refine sepWPp_conseq_pre hpre_p3
      (sepWPp_genP3_to_tailQpan_placed A lim DecPkEnv B S stk' y hpan_model ?_)
    refine hP3 (cliGhostExterns gh (cliExternsPlaced mmpl W)) W.C 0#64 W.Q.K
      hh.alloc (cliChainClone3_budget_placed_ok mmpl gh W hh)
      (cliSenderChainClone3_budget_placed_ok mmpl gh W hh)
      hTryDec
      s0 s2 y.fut y.cx y.out 8#64 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message F_p3 _
      (hfits_p3 evs_p2 m i k kp reg dk recG hevs_p2 hpm_eq hi hk hkp hreg hacc hex)
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdecOk)) hSeeds hRC hPqLt
      hfr2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' evs_p3 pt ptCap ptPtr s' P_s' hver hcl hdec_rel hevs_p3 hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'
      have hent_s'' :
          P_s' ⊢
            stageP3DispatchOkMid_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 s' y.fut y.out 8#64 8#64
              ptCap ptPtr pt 0#8 G'
              (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2 ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_s'
      have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced A.repAlloc σ y.g.stores
        hsub hfPeer hdecOk (pid := pid) (sid := m.spkId) (kid := m.kpkId) (kbk := y.g.msg.baseKey)
      have hunpack_p3 : P_s' ∗ F_p3 ⊢
          P_s' ∗
          (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
              (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
              (coroOpkIdAtP4 y.fut m.opkId)
              (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
                ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
            stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
            ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
            ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRem ∗
            kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
            ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
            (cliPollPkKitPlaced A.repAlloc y.g.F pid σ).storeAt
              (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ).storeAt
              (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
              (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
            memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) := by
        dsimp only [F_p3]
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
        refine Entails.trans (sepConj_mono_left hstores_in) ?_
        dsimp only [cliPollStoresKitsAtPlaced]
        sep_frame
      exact sepWPp_conseq_pre hunpack_p3
        (closure_pathA_p4_cont_placed hP4 B S hh hReadFile hDeser hS stk' hneed hstk63 y
          hfPeer hdecOk hloadS hcur htrusted m i k kp reg dk
          kitEnv ikitEnv pkKitEnv (kpkKitEnv m.kpkId m.spkId)
          ((evs_p1 ++ evs_p2) ++ evs_p3) recG G₁ G'
          rngPtr whisperMsgPtr ptCap ptPtr y.g.msgG.msg preKeyMsgRem P_s' R pt s0 s2 s'
          hpm_eq hi hk hkp hreg hacc hex
          (hfits_p4 evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt
            hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 hok)
          (fun evs_p4 hevs_p4 =>
            hevs_ok evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4
              hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 hok hevs_p4)
          (fun evs_p4 hevs_p4 =>
            hevs_markErr evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4
              hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 hok hevs_p4)
          hmsg_fold hs2_files htr20 hs2_sp hsp_align2 hsp_sub
          hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
          hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'')
    · intro G₁ G' evs_p3 e sf P_f hver hcl hdec_rel hevs_p3 herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
            memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPost_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out 8#64 e ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_f
      exact stageP3_exit_pathA_to_pollPost_placed B S hh hS stk' hneed hstk63 y
        ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf
        rngPtr whisperMsgPtr y.g.msgG.msg preKeyMsgRem
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins))
        P_f R m.opkId m.kpkId m.spkId e
        (hevs_err evs_p2 m i k kp reg dk recG G₁ G' evs_p3 e
          hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 herr hne_p)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver herr hne_p)
        hent_f' hsf_sp htr_f hcs_f hvregs_f
    · intro evs_p3 sf P_f hver_ne hevs_p3 hent_f hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
            memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPost_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out 8#64
              (.invalidMessage .preKey .decryptionFailed) ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (coinsAtPlaced y.g.coinsP y.g.coins) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_f
      exact stageP3_exit_pathA_to_pollPost_placed B S hh hS stk' hneed hstk63 y
        ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf
        rngPtr whisperMsgPtr y.g.msgG.msg preKeyMsgRem (coinsAtPlaced y.g.coinsP y.g.coins)
        P_f R m.opkId m.kpkId m.spkId (.invalidMessage .preKey .decryptionFailed)
        (hevs_verNe evs_p2 m i k kp reg dk recG evs_p3
          hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver_ne hevs_p3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver_ne)
        hent_f' hsf_sp htr_f hcs_f hvregs_f

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget
