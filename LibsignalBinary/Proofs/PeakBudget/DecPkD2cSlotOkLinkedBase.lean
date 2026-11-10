/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.WrapperOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.ProloguePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget

/-!
# `CodeOk`-Parameterized and `LibsignalFrozen` Slot/Wrapper/Path-A Infrastructure

Provides `CodeOk : Memory → Prop`-generalized and `[LibsignalFullPlacement]` (`withLsFrozen lsmpl`)
slot, outer-wrapper (Block `520`), Stage P2, and Path A composition infrastructure consumed by
`DecPkD2cSlotOkLinkedAux`, so a single poll composition yields both `DecPkD2cSlotOkPlaced`
(`[LibsignalPlacement]`) and `DecPkD2cSlotOkFrozenPlaced` (`[LibsignalFullPlacement]`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase

open scoped CryptoVerification.RustHeap
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm
  CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers
open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalFrozen LibsignalFullPlacement LibsignalHooks
   LibsignalPlacement libsignalFrozen_of_keepsFrozen lsRustNoAllocShimSym lsmpl lsρ)
open CryptoVerification.CliHandshake.Placed (blkPC_520_pairStep_0x40 blkPl_520 lsProg_520)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal preKeyMsgAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsAt FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (noAllocShimSpec rootStack withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SessionGhost SignalMessageGhost decryptDraws protocolAddressAt signalMessageAt uuidTryParse)
open CryptoVerification.E2E
  (LocalIdentity PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives
   acceptInput modelPrims)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (stageP3Sub5ExtraPre)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
  (Over.clearPending Over.stageP3Sub5ExtraPrePrev1)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
  (SessionExtraRel coroOpkIdAtP4 p1LoadedRecordAt stageP1ProgPlaced)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open CryptoVerification.SignalSession.Cli
  (CliGhostHooks StoresGhost cliGhostExterns cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym
   cliSessionVtSym cliSignedPreKeyVtSym dirAt)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunGlue (withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunSkeleton
  (CalleeSlot.OkPlaced RunBudgets RunSlots)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunNeeds RunSem decPkNeed decResAt dpPollNeed dpResHeap dpSlotArgsPlaced
   dpWords_resHeap_entails_decResAt mkSlot)
open CryptoVerification.SignalSession.Cli.RunProofs
  (DecPkOkD2c DecPkOk₀ DpPollK SessMatchesPm cliDecryptPrekeyNeed decPkDef decPkDefD2c dpCxAt
   dpFutDoneAt dpFutStartAt dpWordsAt dpWrapFrame pkStoreKeys pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers
  (DpPrologueMid1Placed DpPrologueMid2Placed DpProloguePostPlaced args13_unpack bv128_hi_append
   bv128_lo_append bv_add_16_8 bv_add_32_8 bv_off_01 bv_off_02 bv_off_03 bv_off_04 bv_off_05
   bv_off_06 bv_off_07 bv_off_08 bv_off_09 bv_off_10 bv_off_11 bv_off_12 bv_off_13 bv_off_14
   bv_off_15 bv_off_15b bv_off_16 bv_off_17 bv_off_17b bv_off_18 bv_off_19 bv_off_20 bv_off_21
   bv_off_22 bv_off_23 bv_off_24 bv_off_25 bv_off_26 bv_off_27 bv_off_28 bv_off_29 bv_off_30
   bv_off_31 bv_off_32 bv_off_33 cmn3_ne_zero dpCallerFrame dpCallerFrame_pack dpCxAt_pack
   dpFutDoneAt_eq dpFutStartAt_pack dpPrologueMid2Prop dpRetRes_pack dpWords5_eq dpWords6_eq
   readVReg128_setMem_setPC_pre readVReg128_setPC_pre sepWP_unpack_callerFrame
   sepWP_with_dp_locals sepWP_with_dp_saved sep_rearrange stackAt_dp_epilogue ws6_unpack)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (SepWPp.call_lscro_plain)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (LsTokenInit StageP1PostRegs cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced
   cliPollPkKitPlaced cliPollSessKitPlaced cliPollSpkKitPlaced cliPollStoresKitsAtPlaced
   closureCalleeSaved_toCalleeSavedPreserved decPkDef_pathA_err decPkDef_pathA_panic
   decPkDef_pathA_ver_ne distinctSid_of_decPkOk₀ dpClosSubStack dpPollEntryPlaced dpPollProgPlaced
   loadRec_of_cliPollSess_loadRel pathAInitSession pathAInitSession_scopeIn pathAInitState
   pmPreKeyId rootStack_le_subStack sepWPp_conseq_pre slotOutTr_of_reject sp_frame_sub_add
   stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt)
open CryptoVerification.SignalSession.Cli.Slots
  (EncodeInjOn FilesOkPeer cliGhostExterns_sat_of_cliExternsPlaced encodeInjOn_deserializeScopeP_Q
   filesOk₀ loadRec scopeIn scopeKit)
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
  (chainClone3_placed_ok_of_hooks senderChainClone3_placed_ok_of_hooks)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
  (KyberPreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (PreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees
  (ls_subroutine_ok_withLsFrozen_of_block_frc)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
  (DecPkD2cSlotOkPlacedAt slotOkPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (cliExternsPlaced_sessionMemcpyRegion_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget DpPollKStateBudget cliDecryptPrekeySpecStateBudget decPkSlotSpecPlaced
   dpPollSpecStateBudget dpSlotPollKStatePlaced slotFramePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
  (dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  (ChainClone3OkPlaced SenderChainClone3OkPlaced StageP3Env StageP3OkPrefixEnv genP3Pre_placed
   genP3S5PostFrame_placed pollTryDecryptPlacedSpecTPTight stageP3DispatchOkMid_placed
   stageP3ErrPost_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (RunHooksPlaced StageP2PathAEnv StageP2PathAErrPlaced StageP3GenStepsVRegsPlacedStmt
   StageP4PathAEnv StageP4PathAPlacedStmt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget
  (stageP3_exit_pathA_to_pollPost_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget
  (cliFiles_eq_of_trace_eq_placed exit_entails_dpPollPost_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
  (sepWPp_genP3_to_tailQpan_placed sepWPp_pollGoal_frame_placed
   storesAt_opened_entails_cliPollStoresKitsAtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4ContPlacedBudget
  (closure_pathA_p4_cont_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
  (CliStageP1OkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
  (StageP2OverEnv StageP2OverErrPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
  (overGenP3Pre_placed)

/-! ## 1. `withMemInv` and `LibsignalFrozen` Block `520` Wrapper Reduction -/

/-- Precondition wrapper adjoining `⌜CodeOk s0.mem⌝` on the right (`rfl`-compatible with both
`StoreKit.withLsCodeRoLoaded lsmpl` and `withLsFrozen lsmpl`). -/
def withMemInv (CodeOk : Memory → Prop) {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜CodeOk s0.mem⌝ }

theorem extract_withMemInv {CodeOk : Memory → Prop} {α : Type} {spec : Spec α}
    {x : α} {R : SepProp} {s0 : State}
    (h : s0.mem ⊨ (withMemInv CodeOk spec).pre x s0 ∗ R) :
    CodeOk s0.mem ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withMemInv] at h
  rwa [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at h

section FrozenWrapper520

noncomputable section

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
  bv128_lo_append bv128_hi_append bv_add_16_8 bv_add_32_8
  bv_off_01 bv_off_02 bv_off_03 bv_off_04 bv_off_05 bv_off_06 bv_off_07 bv_off_08
  bv_off_09 bv_off_10 bv_off_11 bv_off_12 bv_off_13 bv_off_14 bv_off_15 bv_off_15b
  bv_off_16 bv_off_17 bv_off_17b bv_off_18 bv_off_19 bv_off_20 bv_off_21 bv_off_22
  bv_off_23 bv_off_24 bv_off_25 bv_off_26 bv_off_27 bv_off_28 bv_off_29 bv_off_30
  bv_off_31 bv_off_32 bv_off_33
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre

private theorem sepWP_of_vm {prog : Program} {mid : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → post sm Pm))) :
    SepWP prog mid s P post :=
  SepWP.mono h (fun _ _ _ _ ⟨hvmp, hpost⟩ => hpost hvmp)

private theorem sepWP_done_tpidr {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0) (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨htp, hpost⟩

private def dps_fixedK_placed {M : AllocCostModel}
    (K : DpPollKStateBudget M) (st : M.σ) (s0 : State) : DpPollK where
  Ghost := K.Ghost
  args := K.args
  inv := fun g => K.inv g st s0
  res := fun _ _ => emp
  io := fun _ _ _ _ _ => True
  panics := K.panics
  need := K.need

private theorem dps_sepWPp_seq_keepsFrozen_placed {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P
      (fun sm Pm => s.mem.KeepsFrozen sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (Φ := fun m => s.mem.KeepsFrozen m)
    (fun _ _ h1 h2 => h1.trans h2) (Memory.KeepsFrozen.refl s.mem) h

set_option maxHeartbeats 400000 in
private theorem dpWrapper_prologue_a1_vm_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {K : DpPollK} {stk : Nat} (hge_wrap : dpWrapFrame ≤ stk) (hle_wrap : stk ≤ 2 ^ 64)
    {s0 : State} {ret : BitVec 64} {g : K.Ghost} {a8 a9 a10 a11 a12 : BitVec 64}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_520).base)
    (hrun : s0.status = .Running) (hsp_align : s0.spAligned = true)
    (hx8 : s0.readReg64 (Reg.gpr 8#5) = ret)
    (hdrop_eq : (K.args g).drop 8 = [a8, a9, a10, a11, a12])
    (hk : ∀ sa Pa, DpPrologueMid1Placed s0 ret a8 a9 a10 a11 a12 sa → VmPreserved s0 sa →
      Pa = memRegion (s0.sp - 2144#64) 2088 ∗
             (stackAt (s0.sp - 2144#64) (stk - dpWrapFrame) ∗ K.inv g ∗
               dpCallerFrame s0 ret ((K.args g).drop 8)) → Q sa Pa) :
    SepWP (lsProg_520 (Rust.withPanics ext)) ((blkPl_520).base + 36#64) s0
      (dpWordsAt s0.sp ((K.args g).drop 8) ∗ memRegion ret 48 ∗ K.inv g ∗ stackAt s0.sp stk) Q := by
  dsimp only [lsProg_520]
  rw [← BitVec.add_zero (blkPl_520).base] at hpc
  rw [← sepConj_assoc, ← sepConj_assoc]
  refine sepWP_with_dp_saved hge_wrap hle_wrap fun sfp slr sx28 sx21 sx20 sx19 => ?_
  rw [hdrop_eq, dpWords5_eq s0.sp a8 a9 a10 a11 a12]
  apply sepWP_of_vm
  by_vm_steps (
    wp_steps
    apply SepWP.fold (Entails.of_eq (dpWords5_eq s0.sp a8 a9 a10 a11 a12).symm) (by sep_focus)
    rw [← hdrop_eq]
    apply SepWP.fold (dpCallerFrame_pack s0 ret ((K.args g).drop 8)) (by sep_focus)
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    intro hvmp
    refine hk _ _ ?_ hvmp (sep_rearrange (by sep_focus))
    constructor <;>
      first
      | (simp only [State.spAligned, wp_norm, arm64_norm] at hsp_align ⊢; exact hsp_align)
      | (simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]; done)
      | (simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]; bv_omega)
  )

set_option maxHeartbeats 400000 in
private theorem dpWrapper_prologue_a2_vm_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {K : DpPollK} {stk : Nat} {s0 sa : State} {ret : BitVec 64} {g : K.Ghost}
    {a8 a9 a10 a11 a12 : BitVec 64} {Q : State → SepProp → Prop}
    (ha : DpPrologueMid1Placed s0 ret a8 a9 a10 a11 a12 sa)
    (hk : ∀ sb Pb (f4 f5 f6 f7 f8 f9 f10 f11 : BitVec 64) (fstate : BitVec 8) (cx0 cx1 cx2 : BitVec 64),
      DpPrologueMid2Placed s0 ret a8 a9 a10 a11 sb → VmPreserved sa sb →
      Pb = dpPrologueMid2Prop stk s0 ret g a12 f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2 →
      Q sb Pb) :
    SepWP (lsProg_520 (Rust.withPanics ext)) ((blkPl_520).base + 64#64) sa
      (memRegion (s0.sp - 2144#64) 2088 ∗
        (stackAt (s0.sp - 2144#64) (stk - dpWrapFrame) ∗ K.inv g ∗
          dpCallerFrame s0 ret ((K.args g).drop 8))) Q := by
  rcases ha with ⟨hpc_a, hrun_a, hsp_a, hsp_align_a, hfp_a, hx0_a, hx1_a,
    hx2_a, hx3_a, hx4_a, hx5_a, hx6_a, hx7_a, hx8_a, hx9_a, hq0_a, hq1_a, hx19_a,
    hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hvregs_a, hfs_a, htr_a⟩
  dsimp only [lsProg_520]
  refine sepWP_with_dp_locals s0.sp fun f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 fcoins fstate cx0 cx1 cx2 => ?_
  apply sepWP_of_vm
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    intro hvmp
    refine hk _ _ f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2 ?_ hvmp
      (sep_rearrange (by dsimp only [dpPrologueMid2Prop]; sep_focus))
    constructor <;>
      first
      | (simp only [State.spAligned, wp_norm, arm64_norm, *] at hsp_align_a ⊢; exact hsp_align_a)
      | simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]
  )

set_option maxHeartbeats 400000 in
private theorem dpWrapper_prologue_b_vm_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {K : DpPollK} {stk : Nat} {s0 sb : State} {ret : BitVec 64} {g : K.Ghost}
    {a8 a9 a10 a11 a12 f4 f5 f6 f7 f8 f9 f10 f11 : BitVec 64}
    {fstate : BitVec 8} {cx0 cx1 cx2 : BitVec 64} {Q : State → SepProp → Prop}
    (hb : DpPrologueMid2Placed s0 ret a8 a9 a10 a11 sb)
    (hargs_eq : K.args g =
      [s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5), s0.readReg64 (Reg.gpr 2#5),
       s0.readReg64 (Reg.gpr 3#5), s0.readReg64 (Reg.gpr 4#5), s0.readReg64 (Reg.gpr 5#5),
       s0.readReg64 (Reg.gpr 6#5), s0.readReg64 (Reg.gpr 7#5), a8, a9, a10, a11, a12])
    (hk : ∀ s1 P1, DpProloguePostPlaced s0 ret s1 → VmPreserved sb s1 →
      P1 = (memRegion (s0.sp - 104#64) 48 ∗ dpFutStartAt (s0.sp - 2144#64) (K.args g) ∗
              dpCxAt (s0.sp - 136#64) ∗ K.inv g ∗ stackAt (s0.sp - 2144#64) (stk - dpWrapFrame)) ∗
           dpCallerFrame s0 ret ((K.args g).drop 8) → Q s1 P1) :
    SepWP (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 518) sb
      (dpPrologueMid2Prop stk s0 ret g a12 f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2) Q := by
  rcases hb with ⟨hpc_b, hrun_b, hsp_b, hsp_align_b, hfp_b, hx0_b, hx1_b,
    hx2_b, hx4_b, hx5_b, hx6_b, hx7_b, hq0_b, hq1_b, hx19_b,
    hx22_b, hx23_b, hx24_b, hx25_b, hx26_b, hx27_b, hvregs_b, hfs_b, htr_b⟩
  dsimp only [lsProg_520, dpPrologueMid2Prop]
  have hvm_pair :
      VmPreserved sb
        ((sb.writeReg64 (Reg.gpr 8#5)
          (blkPl_520.ρ "libsignal_cli_handshake:.rodata..Lanon.1")).setPC
          (blkPl_520.base + 72#64)) := by
    simp only [wp_norm, arm64_norm]
  apply blkPC_520_pairStep_0x40 blkPl_520.base (Rust.withPanics ext) rfl hpc_b hrun_b
  apply sepWP_of_vm
  by_vm_steps (
    wp_steps
    apply SepWP.fold (dpFutStartAt_pack s0.sp _ _ _ _ _ _ _ _ a8 a9 a10 a11 a12 _) (by sep_focus)
    rw [← hargs_eq]
    apply SepWP.fold (dpCxAt_pack s0.sp _) (by sep_focus)
    apply sepWP_done_tpidr (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    intro hvmp
    refine hk _ _ ?_ (hvm_pair.trans hvmp) (sep_rearrange (by sep_focus))
    constructor <;>
      first
      | (simp only [State.spAligned, wp_norm, arm64_norm, *] at hsp_align_b ⊢; exact hsp_align_b)
      | simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]
  )

private structure dps_EpilogueMidPlaced [LibsignalPlacement] (s0 sm se : State) : Prop where
  pc : se.pc = (blkPl_520).base + 176#64
  run : se.status = .Running
  sp : se.sp = s0.sp - 2144#64
  sp_align : se.spAligned = true
  x22 : se.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)
  x23 : se.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5)
  x24 : se.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5)
  x25 : se.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5)
  x26 : se.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  x27 : se.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  vregs : calleeSavedVRegs se = calleeSavedVRegs s0
  fs : se.fs = sm.fs
  trace : se.trace = sm.trace
  vm : VmPreserved sm se

private abbrev dps_epilogueMidProp_placed {M : AllocCostModel}
    (stk : Nat) (s0 s1 sm : State) (ret : BitVec 64)
    {K : DpPollKStateBudget M} (g : K.Ghost) (st : M.σ)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  (∃∗ ws : List (BitVec 64),
      ⌜ws.length = 6 ∧ ws.head? ≠ some (BitVec.ofNat 64 (2 ^ 64 - 3))⌝ ∗
        dpWordsAt ret ws ∗ K.res g st s1 sm ws) ∗
    dpWordsAt s0.sp ((K.args g).drop 8) ∗
    stackAt (s0.sp - 2144#64) (stk - dpWrapFrame) ∗
    memRegion (s0.sp - 2144#64) 704 ∗ ((s0.sp - 1440#64) ↦₈ 1#8) ∗
    memRegion (s0.sp - 1439#64) 1303 ∗ memRegion (s0.sp - 136#64) 32 ∗
    ((s0.sp - 104#64) ↦₆₄ w0) ∗ ((s0.sp - 96#64) ↦₆₄ w1) ∗
    ((s0.sp - 88#64) ↦₆₄ w2) ∗ ((s0.sp - 80#64) ↦₆₄ w3) ∗
    ((s0.sp - 72#64) ↦₆₄ w4) ∗ ((s0.sp - 64#64) ↦₆₄ w5) ∗
    memRegion (s0.sp - 56#64) 8 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.fp) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

set_option maxHeartbeats 400000 in
private theorem dps_wrapper_epilogue_a_placed [LibsignalPlacement] {M : AllocCostModel}
    {ext : String → Option (State → State)}
    {K : DpPollKStateBudget M} {stk : Nat}
    {s0 s1 sm : State} {ret : BitVec 64} {g : K.Ghost} {st : M.σ}
    {Q : State → SepProp → Prop}
    (hp1 : DpProloguePostPlaced s0 ret s1)
    (hpcm : sm.pc = (blkPl_520).base + 100#64)
    (hrunm : sm.status = .Running) (hspm : sm.sp = s1.sp)
    (hcsm : CalleeSavedPreserved s1 sm)
    (hk : ∀ se Pe w0 w1 w2 w3 w4 w5,
      dps_EpilogueMidPlaced s0 sm se →
      Pe = dps_epilogueMidProp_placed stk s0 s1 sm ret g st w0 w1 w2 w3 w4 w5 →
      Q se Pe) :
    SepWP (lsProg_520 (Rust.withPanics ext)) ((blkPl_520).base + 176#64) sm
      ((dpPollSpecStateBudget K (stk - dpWrapFrame)).post
          ⟨s0.sp - 104#64, s0.sp - 2144#64, s0.sp - 136#64, g, st⟩ s1 sm ∗
        dpCallerFrame s0 ret ((K.args g).drop 8)) Q := by
  dsimp only [lsProg_520]
  have hsp_align_sm : sm.spAligned = true := by simp only [State.spAligned, hspm]; exact hp1.sp_align
  have hfp_sm : sm.readReg64 Reg.fp = s0.sp - 48#64 := hcsm.readReg64_fp.trans hp1.fp
  have hx19_sm : sm.readReg64 (.gpr 19#5) = ret := hcsm.readReg64_x19.trans hp1.x19
  have hx22_sm : sm.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) := hcsm.readReg64_x22.trans hp1.x22
  have hx23_sm : sm.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) := hcsm.readReg64_x23.trans hp1.x23
  have hx24_sm : sm.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) := hcsm.readReg64_x24.trans hp1.x24
  have hx25_sm : sm.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) := hcsm.readReg64_x25.trans hp1.x25
  have hx26_sm : sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) := hcsm.readReg64_x26.trans hp1.x26
  have hx27_sm : sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) := hcsm.readReg64_x27.trans hp1.x27
  have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs s0 := hcsm.vregs.trans hp1.vregs
  have hsp_s1 : s1.sp = s0.sp - 2144#64 := hp1.sp
  refine sepWP_unpack_callerFrame fun r0 r1 r2 r3 r4 r5 => ?_
  dsimp only [dpPollSpecStateBudget]
  rw [hsp_s1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i ws
  wp_focus_pure; rintro ⟨hws_len, hws_head⟩
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl, hw0_ne⟩ := ws6_unpack hws_len hws_head
  obtain ⟨hw0_add3, hcmn_ne⟩ := cmn3_ne_zero hw0_ne
  rw [dpFutDoneAt_eq s0.sp, dpWords6_eq (s0.sp - 104#64) w0 w1 w2 w3 w4 w5]
  simp only [bv_off_14, bv_off_15, bv_off_15b, bv_off_17, bv_off_17b, sepConj_assoc]
  apply sepWP_of_vm
  by_vm_steps (
    wp_steps
    apply SepWP.fold (Entails.of_eq (dpWords6_eq ret w0 w1 w2 w3 w4 w5).symm) (by sep_focus)
    apply SepWP.fold (dpRetRes_pack (res := K.res g st s1 sm) ret w0 w1 w2 w3 w4 w5 hw0_ne) (by sep_focus)
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    intro hvm_ea
    refine hk _ _ w0 w1 w2 w3 w4 w5 ?_ (sep_rearrange (by dsimp only [dps_epilogueMidProp_placed]; sep_focus))
    exact
      { pc := by simp only [wp_norm, arm64_norm]
        run := by simp only [wp_norm, arm64_norm, *]
        sp := by simp only [wp_norm, arm64_norm, *]
        sp_align := by simp only [State.spAligned, wp_norm, arm64_norm, *] at hsp_align_sm ⊢; exact hsp_align_sm
        x22 := by simp only [wp_norm, arm64_norm, *]
        x23 := by simp only [wp_norm, arm64_norm, *]
        x24 := by simp only [wp_norm, arm64_norm, *]
        x25 := by simp only [wp_norm, arm64_norm, *]
        x26 := by simp only [wp_norm, arm64_norm, *]
        x27 := by simp only [wp_norm, arm64_norm, *]
        vregs := by simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]
        fs := by simp only [wp_norm, arm64_norm, *]
        trace := by simp only [wp_norm, arm64_norm, *]
        vm := hvm_ea }
  )

private theorem dps_epilogue_post_mono [LibsignalPlacement] {M : AllocCostModel}
    {K : DpPollKStateBudget M} {stk : Nat}
    {s0 s1 sm sf : State} {ret : BitVec 64} {g : K.Ghost} {st : M.σ} {R : SepProp}
    (hres : ∀ g st s0 s1 sm sf ws,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      sf.fs = sm.fs → sf.trace = sm.trace → VmPreserved sm sf →
      K.res g st s1 sm ws ⊢ K.res g st s0 sf ws)
    (hfs01 : s1.fs = s0.fs) (htr01 : s1.trace = s0.trace) (hvm01 : VmPreserved s0 s1)
    (hfs_mf : sf.fs = sm.fs) (htr_mf : sf.trace = sm.trace) (hvm_mf : VmPreserved sm sf)
    (hm : sf.mem ⊨
      (((∃∗ ws : List (BitVec 64),
          ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
            dpWordsAt ret ws ∗ K.res g st s1 sm ws) ∗
        dpWordsAt s0.sp ((K.args g).drop 8) ∗ stackAt s0.sp stk) ∗ emp) ∗ R) :
    sf.mem ⊨ (cliDecryptPrekeySpecStateBudget K stk).post ⟨ret, g, st⟩ s0 sf ∗ R := by
  rw [sepConj_emp] at hm
  dsimp only [cliDecryptPrekeySpecStateBudget]
  have hent_res :
      (∃∗ ws : List (BitVec 64),
          ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
            dpWordsAt ret ws ∗ K.res g st s1 sm ws) ⊢
        (∃∗ ws : List (BitVec 64),
          ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
            dpWordsAt ret ws ∗ K.res g st s0 sf ws) :=
    Entails.sepExists_elim fun ws =>
      Entails.sepExists_right ws
        (sepConj_mono_right
          (sepConj_mono_right
            (hres g st s0 s1 sm sf ws hfs01 htr01 hvm01 hfs_mf htr_mf hvm_mf)))
  exact Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_res)) hm

set_option maxHeartbeats 400000 in
private theorem dps_wrapper_epilogue_b_placed [LibsignalPlacement] {M : AllocCostModel}
    {ext : String → Option (State → State)}
    {K : DpPollKStateBudget M} {stk : Nat} (hge_wrap : dpWrapFrame ≤ stk) (hle_wrap : stk ≤ 2 ^ 64)
    {s0 s1 sm se : State} {ret : BitVec 64} {g : K.Ghost} {st : M.σ}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {R : SepProp}
    (hp1 : DpProloguePostPlaced s0 ret s1) (hvm01 : VmPreserved s0 s1)
    (hres : ∀ g st s0 s1 sm sf ws,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      sf.fs = sm.fs → sf.trace = sm.trace → VmPreserved sm sf →
      K.res g st s1 sm ws ⊢ K.res g st s0 sf ws)
    (hsp_align : s0.spAligned = true) (he : dps_EpilogueMidPlaced s0 sm se) :
    SepWP (lsProg_520 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) se
      (dps_epilogueMidProp_placed stk s0 s1 sm ret g st w0 w1 w2 w3 w4 w5)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (withLsFrozen lsmpl (cliDecryptPrekeySpecStateBudget K stk)).post ⟨ret, g, st⟩ s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rcases he with ⟨hpc_e, hrun_e, hsp_e, hsp_align_e, hx22_e, hx23_e, hx24_e,
    hx25_e, hx26_e, hx27_e, hvregs_e, hfs_e, htr_e, hvm_ea⟩
  dsimp only [lsProg_520, dps_epilogueMidProp_placed]
  apply sepWP_of_vm
  by_vm_steps (
    wp_steps
    apply SepWP.fold (stackAt_dp_epilogue s0.sp hge_wrap hle_wrap w0 w1 w2 w3 w4 w5
      (s0.readReg64 Reg.fp) (s0.readReg64 Reg.lr)
      (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))) (by sep_focus)
    apply SepWP.fold
      (Entails.refl ((∃∗ ws : List (BitVec 64),
          ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
            dpWordsAt ret ws ∗ K.res g st s1 sm ws) ∗
        dpWordsAt s0.sp ((K.args g).drop 8) ∗ stackAt s0.sp stk))
      (by sep_focus)
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    intro hvm_eb
    refine ⟨fun hm =>
        dps_epilogue_post_mono hres hp1.fs hp1.trace hvm01
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (hvm_ea.trans hvm_eb) hm,
      by simp only [wp_norm, arm64_norm, *], ?_⟩
    constructor <;> simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]
  )

/-- `[LibsignalFullPlacement]` (`withLsFrozen lsmpl`) state-coupled wrapper reduction on Block `520`
(`lsProg_520`) from `lsProg_518`. -/
theorem cliDecryptPrekey_ok_state_frozen_placed [LibsignalFullPlacement] {M : AllocCostModel}
    {ext : String → Option (State → State)}
    (K : DpPollKStateBudget M)
    (hinv : ∀ g st s0 s1,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      K.inv g st s0 ⊢ K.inv g st s1)
    (hres : ∀ g st s0 s1 sm sf ws,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      sf.fs = sm.fs → sf.trace = sm.trace → VmPreserved sm sf →
      K.res g st s1 sm ws ⊢ K.res g st s0 sf ws)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (withLsFrozen lsmpl (dpPollSpecStateBudget K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 520)
      (withLsFrozen lsmpl (cliDecryptPrekeySpecStateBudget K stk)) := by
  have hge_wrap : dpWrapFrame ≤ stk := by omega
  have hle_wrap : stk ≤ 2 ^ 64 := by omega
  have hpoll_fr : subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 518)
      (withLsFrozen lsmpl (dpPollSpecStateBudget K (stk - dpWrapFrame))) :=
    ls_subroutine_ok_withLsFrozen_of_block_frc (callerProg := lsProg_520 (Rust.withPanics ext))
      (hK (stk - dpWrapFrame) (by omega) (by omega))
  clear hK
  wpp_init x s0
  obtain ⟨ret, g, st⟩ := x
  dsimp only [withLsFrozen, cliDecryptPrekeySpecStateBudget] at *
  have hx8 : s0.readReg64 Reg.x8 = ret := by assumption
  have hlen13 : (K.args g).length = 13 := by assumption
  have htake8 : (K.args g).take 8 =
      [s0.readReg64 Reg.x0, s0.readReg64 Reg.x1, s0.readReg64 Reg.x2, s0.readReg64 Reg.x3,
       s0.readReg64 Reg.x4, s0.readReg64 Reg.x5, s0.readReg64 Reg.x6, s0.readReg64 Reg.x7] := by
    assumption
  have hsp_le : stk ≤ s0.sp.toNat := by assumption
  have hfr0 : LibsignalFrozen lsmpl s0.mem := by assumption
  obtain ⟨a8, a9, a10, a11, a12, hdrop_eq, hargs_eq⟩ := args13_unpack hlen13 htake8
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_a1_vm_placed (K := dps_fixedK_placed K st s0) (g := g)
    hge_wrap hle_wrap hpc hrun hsp_align hx8 hdrop_eq ?_
  rintro sa _ ha hvm_a1 rfl hkf1
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_a2_vm_placed (K := dps_fixedK_placed K st s0) (g := g) ha ?_
  rintro sb _ f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2 hb hvm_a2 rfl hkf2
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_b_vm_placed (K := dps_fixedK_placed K st s0) (g := g) hb hargs_eq ?_
  rintro s1 _ hp1 hvm_b rfl hkf3
  have hvm01 : VmPreserved s0 s1 := (hvm_a1.trans hvm_a2).trans hvm_b
  have hsp_le1 : stk - dpWrapFrame ≤ (s0.sp - 2144#64).toNat := by
    have hw : dpWrapFrame = 2144 := rfl
    rw [hw] at hge_wrap ⊢
    bv_omega
  have hfr1 : LibsignalFrozen lsmpl s1.mem :=
    libsignalFrozen_of_keepsFrozen hfr0 ((hkf1.trans hkf2).trans hkf3)
  have hcrl1 : LibsignalCodeRoLoaded lsmpl s1.mem :=
    ⟨LibsignalCodeLoaded.of_codeLoaded hfr1.2, hfr1.1⟩
  exact SepWPp.call_lscro_plain
    (spec := withLsFrozen lsmpl (dpPollSpecStateBudget K (stk - dpWrapFrame)))
    (x := DpPollGhostStateBudget.mk (s0.sp - 104#64) (s0.sp - 2144#64) (s0.sp - 136#64) g st)
    (F := dpCallerFrame s0 ret ((K.args g).drop 8))
    hpoll_fr hcrl1 hp1.pc hp1.run hp1.sp_align hp1.lr
    (fun R' hm => by
      dsimp only [withLsFrozen, dpPollSpecStateBudget]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hfr1, ?_⟩
      rw [hp1.sp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hp1.x0, hp1.x1, hp1.x2, hlen13, hsp_le1⟩, ?_⟩
      dsimp only [dps_fixedK_placed] at hm
      have hm' :=
        Satisfies.mono
          (sepConj_mono_left
            (sepConj_mono_left
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono_right
                    (sepConj_mono_left (hinv g st s0 s1 hp1.fs hp1.trace hvm01)))))))
          hm
      simpa only [sepConj_assoc] using hm')
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf_pan _ hmpan => by
      dsimp only [withLsFrozen, dpPollSpecStateBudget, cliDecryptPrekeySpecStateBudget] at hmpan ⊢
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hmpan
      obtain ⟨⟨htr_pan, hpan_k⟩, hmpan_rest⟩ := hmpan
      rw [hp1.trace] at htr_pan
      rw [← sepConj_assoc] at hmpan_rest
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨htr_pan, hpan_k⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmpan_rest⟩)
    (fun sm hpcm hrunm hspm hcsm _ => by
      apply dps_sepWPp_seq_keepsFrozen_placed
      refine dps_wrapper_epilogue_a_placed hp1 hpcm hrunm hspm hcsm ?_
      rintro se _ w0 w1 w2 w3 w4 w5 he rfl _
      exact SepWPp.of_sepWP_ret
        (dps_wrapper_epilogue_b_placed hge_wrap hle_wrap hp1 hvm01 hres hsp_align he))
    (fun _ _ _ hmo => (not_satisfies_false_sepConj hmo).elim)

/-- Cross-block transfer of `cliDecryptPrekey_ok_state_frozen_placed` onto any caller block
(e.g. `lsProg_579 (Rust.withPanics ext)`) under `[LibsignalFullPlacement]`. -/
theorem cliDecryptPrekey_ok_state_frozen_placed_at_block [LibsignalFullPlacement]
    {M : AllocCostModel} {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (K : DpPollKStateBudget M)
    (hinv : ∀ g st s0 s1,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      K.inv g st s0 ⊢ K.inv g st s1)
    (hres : ∀ g st s0 s1 sm sf ws,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      sf.fs = sm.fs → sf.trace = sm.trace → VmPreserved sm sf →
      K.res g st s1 sm ws ⊢ K.res g st s0 sf ws)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (withLsFrozen lsmpl (dpPollSpecStateBudget K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok callerProg (lsmpl.base 520)
      (withLsFrozen lsmpl (cliDecryptPrekeySpecStateBudget K stk)) :=
  ls_subroutine_ok_withLsFrozen_of_block_frc (callerProg := callerProg)
    (cliDecryptPrekey_ok_state_frozen_placed K hinv hres hK stk hstk hstk64)

end

end FrozenWrapper520

/-! ## 2. `CodeOk`-Parameterized W4 Slot Contracts, Adapters, and Frozen Outer Wrapper -/

/-- Unwrapped budget-threaded `[LibsignalPlacement]` W4 slot contract. -/
def decPkSlotSpecBasePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecPkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.peerA ∧ s.readReg64 .x2 = x.meA ∧
      s.readReg64 .x3 = x.stores + 0xf0#64 ∧ s.readReg64 .x4 = lsρ cliSessionVtSym ∧
      s.readReg64 .x5 = x.stores ∧ s.readReg64 .x6 = lsρ cliIdentityVtSym ∧
      s.readReg64 .x7 = x.stores + 0xc8#64 ∧
      s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
      S.decPkOk x.F x.peer.val x.me.val x.msg ∧ stk ≤ s.sp.toNat ∧
      FitsEnv M lim st (DecPkEnv x)⌝ ∗
    slotFramePlaced A lim st x.toSlotCtx s ∗ preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
    (s.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s.sp + 8#64) ↦₆₄ (x.stores + 0x50#64)) ∗
    ((s.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
    ((s.sp + 24#64) ↦₆₄ (x.stores + 0x78#64)) ∗
    ((s.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
    memRegion x.ret 48 ∗ stackAt s.sp stk
  post := (decPkSlotSpecPlaced A lim DecPkEnv S stk).post
  onPanic := (decPkSlotSpecPlaced A lim DecPkEnv S stk).onPanic

/-- `CodeOk`-parameterized budget-threaded W4 slot contract (`rfl`-equal to `decPkSlotSpecPlaced`
at `CodeOk := LibsignalCodeRoLoaded lsmpl` and to `withLsFrozen lsmpl ∘ decPkSlotSpecBasePlaced`
at `CodeOk := LibsignalFrozen lsmpl`). -/
def decPkSlotSpecPlacedOf [LibsignalPlacement] (CodeOk : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecPkGhost × M.σ) :=
  withMemInv CodeOk (decPkSlotSpecBasePlaced A lim DecPkEnv S stk)

/-- `LibsignalFrozen`-guarded budget-threaded W4 slot contract (`withLsFrozen lsmpl`). -/
abbrev decPkSlotSpecFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecPkGhost × M.σ) :=
  decPkSlotSpecPlacedOf (LibsignalFrozen lsmpl) A lim DecPkEnv S stk

theorem decPkSlotSpecPlacedOf_roLoaded [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    decPkSlotSpecPlacedOf (LibsignalCodeRoLoaded lsmpl) A lim DecPkEnv S stk =
      decPkSlotSpecPlaced A lim DecPkEnv S stk :=
  rfl

theorem decPkSlotSpecFrozenPlaced_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk =
      withLsFrozen lsmpl (decPkSlotSpecBasePlaced A lim DecPkEnv S stk) :=
  rfl

/-- `CodeOk`-parameterized `slotsOfPlaced` updating `decryptPrekey` (`rfl` at `LibsignalCodeRoLoaded`). -/
def slotsOfDecPkPlacedOf [LibsignalPlacement] (CodeOk : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : RunSlotEnvs)
    (S : RunSem) (needs : RunNeeds) : RunSlots :=
  { slotsOfPlaced A lim envs S needs with
    decryptPrekey := mkSlot (decPkSlotSpecPlacedOf CodeOk A lim envs.decryptPrekey S) needs.decryptPrekey }

/-- Extern-parametric `CodeOk`-guarded D2(c) `decryptPrekey` slot contract on `lsProg_579 H`. -/
def DecPkD2cSlotOkPlacedAtOf [LibsignalPlacement] (CodeOk : Memory → Prop) {M : AllocCostModel}
    (H : LibsignalHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem) (needs : RunNeeds) (sEnvs : RunSlotEnvs),
    sEnvs.decryptPrekey = DecPkEnv →
    S.filesOk = filesOk₀ scopeIn (fun _ => True) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn →
    S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn →
    needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets →
    slotOkPlaced (lsProg_579 H) (lsmpl.base 520)
      (slotsOfDecPkPlacedOf CodeOk A lim sEnvs S needs).decryptPrekey

theorem decPkD2cSlotOkPlacedAtOf_roLoaded [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) :
    DecPkD2cSlotOkPlacedAtOf (LibsignalCodeRoLoaded lsmpl) H X W A lim DecPkEnv =
      DecPkD2cSlotOkPlacedAt H X W A lim DecPkEnv :=
  rfl

/-- `CodeOk`-parameterized D2(c) `decryptPrekey` slot contract at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
def DecPkD2cSlotOkPlacedOf [LibsignalPlacement] (CodeOk : Memory → Prop) (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives),
    DecPkD2cSlotOkPlacedAtOf CodeOk (cliGhostExterns g (cliExternsPlaced mmpl W)) X W A lim DecPkEnv

/-- `LibsignalFrozen`-guarded D2(c) `decryptPrekey` slot contract at fixed `(H, X, W)`. -/
abbrev DecPkD2cSlotOkFrozenPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  DecPkD2cSlotOkPlacedAtOf (LibsignalFrozen lsmpl) H X W A lim DecPkEnv

/-- `LibsignalFrozen`-guarded D2(c) `decryptPrekey` slot contract (`[LibsignalFullPlacement]` twin
of `RunOkNoMatchDefsPlacedBudget.DecPkD2cSlotOkPlaced`). -/
abbrev DecPkD2cSlotOkFrozenPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  DecPkD2cSlotOkPlacedOf (LibsignalFrozen lsmpl) mmpl g W A lim DecPkEnv

private theorem ent_bind_aux {α : Type} {X R Q : SepProp} {P : α → SepProp}
    (hX : X ⊢ ∃∗ x, P x) (hk : ∀ x, P x ∗ R ⊢ Q) : X ∗ R ⊢ Q := by
  refine Entails.trans (sepConj_mono_left hX) ?_
  rw [sepExists_sepConj_left]; exact Entails.sepExists_elim hk

private theorem ent_pure_right_aux {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [hEq, pure_true, sepConj_comm, sepConj_emp]; exact h

private theorem dpSlotStack5_aux_eq [LibsignalPlacement] (sp : BitVec 64) (x : DecPkGhost) :
    dpWordsAt sp ((dpSlotArgsPlaced x).drop 8) =
      (sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
        ((sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗ ((sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
        ((sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) := by
  simp only [dpSlotArgsPlaced, List.drop, dpWordsAt, sepConj_emp, BitVec.add_assoc]; rfl

private theorem dpSlotState_post_entails_aux [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (B : RunBudgets) (S : RunSem)
    (stk : Nat) (x : DecPkGhost) (st : M.σ) (s0 sf : State) :
    (cliDecryptPrekeySpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk).post
        ⟨x.ret, x, st⟩ s0 sf ⊢
      (decPkSlotSpecPlaced A lim DecPkEnv S stk).post (x, st) s0 sf := by
  unfold cliDecryptPrekeySpecStateBudget
  refine ent_bind_aux (Entails.refl _) fun ws => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun _ => ?_
  have r1 : (dpWordsAt x.ret ws ∗
          (dpSlotPollKStatePlaced A lim DecPkEnv B S).res x st s0 sf ws) ∗
        (dpWordsAt s0.sp (((dpSlotPollKStatePlaced A lim DecPkEnv B S).args x).drop 8) ∗
          stackAt s0.sp stk) =
      (dpSlotPollKStatePlaced A lim DecPkEnv B S).res x st s0 sf ws ∗ (dpWordsAt x.ret ws ∗
          dpWordsAt s0.sp (((dpSlotPollKStatePlaced A lim DecPkEnv B S).args x).drop 8) ∗
          stackAt s0.sp stk) := by sep_ac_rfl
  rw [r1]; unfold dpSlotPollKStatePlaced
  refine ent_bind_aux (Entails.refl _) fun evs => ?_
  refine ent_bind_aux (Entails.refl _) fun g' => ?_
  refine ent_bind_aux (Entails.refl _) fun e => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun ⟨hevs, htrace, hout⟩ => ?_
  rw [dpSlotStack5_aux_eq]
  have r2 : (storesAt A.repAlloc x.stores g' ∗ dpResHeap A.repAlloc ws e ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ anyHeap) ∗
          (dpWordsAt x.ret ws ∗
          ((s0.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
            ((s0.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
            ((s0.sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
            ((s0.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym)) ∗ stackAt s0.sp stk) =
      (dpWordsAt x.ret ws ∗ dpResHeap A.repAlloc ws e) ∗ (storesAt A.repAlloc x.stores g' ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
          (s0.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
          ((s0.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
          ((s0.sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
          ((s0.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp stk ∗ anyHeap) := by sep_ac_rfl
  rw [r2]
  refine Entails.trans
    (sepConj_mono_left (dpWords_resHeap_entails_decResAt A.repAlloc x.ret ws e)) ?_
  unfold decPkSlotSpecPlaced withLsCodeRoLoaded
  refine Entails.sepExists_right evs (Entails.sepExists_right g' (Entails.sepExists_right e ?_))
  exact ent_pure_right_aux ⟨hevs, htrace, hout⟩ (Entails.of_eq (by sep_ac_rfl))

/-- `CodeOk`-parameterized state-coupled wrapper-to-slot adapter. -/
theorem dpSlot_ok_state_of_codeOk_placed [LibsignalPlacement] (CodeOk : Memory → Prop)
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (B : RunBudgets) (S : RunSem) (stk : Nat)
    (_hstk : decPkNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63)
    (hw : subroutine_ok prog entry
      (withMemInv CodeOk
        (cliDecryptPrekeySpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk))) :
    subroutine_ok prog entry (decPkSlotSpecPlacedOf CodeOk A lim DecPkEnv S stk) := by
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcode, hpre0⟩ := extract_withMemInv hpre
  dsimp only [decPkSlotSpecBasePlaced] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit⟩,
    hspatial⟩ := hpre0
  have htake : ((dpSlotPollKStatePlaced A lim DecPkEnv B S).args x).take 8 =
      [s0.readReg64 .x0, s0.readReg64 .x1, s0.readReg64 .x2, s0.readReg64 .x3,
       s0.readReg64 .x4, s0.readReg64 .x5, s0.readReg64 .x6, s0.readReg64 .x7] := by
    simp only [dpSlotPollKStatePlaced, dpSlotArgsPlaced, List.take,
      hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7]
  have hinv_sp : s0.mem ⊨ (dpSlotPollKStatePlaced A lim DecPkEnv B S).inv x st s0 ∗
        dpWordsAt s0.sp (((dpSlotPollKStatePlaced A lim DecPkEnv B S).args x).drop 8) ∗
        memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ R := by
    unfold dpSlotPollKStatePlaced
    rw [dpSlotStack5_aux_eq, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF0, hfOk, hdOk, hfit⟩,
      by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hspatial⟩
  have hpre1 : s0.mem ⊨
      (withMemInv CodeOk
        (cliDecryptPrekeySpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk)).pre
        ⟨x.ret, x, st⟩ s0 ∗ R := by
    dsimp only [withMemInv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcode, ?_⟩
    unfold cliDecryptPrekeySpecStateBudget; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, rfl, htake, hsp_le⟩,
      by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hinv_sp⟩
  refine hw.mono_outcome ⟨x.ret, x, st⟩ R s0 hpc hrun hpre1 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hex⟩ | ⟨ho_st, ho⟩
  · exact Or.inl ⟨hret, hcc,
      Satisfies.mono (sepConj_mono_left
        (dpSlotState_post_entails_aux A lim DecPkEnv B S stk x st s0 sf)) hpost⟩
  · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
    have hp' : sf.mem ⊨ ⌜s0.trace <+: sf.trace ∧
            S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none⌝ ∗
        (anyHeap ∗ R) := by
      simpa only [withMemInv, cliDecryptPrekeySpecStateBudget, dpSlotPollKStatePlaced,
        sepConj_assoc] using hp
    rw [satisfies_pure_sepConj] at hp'; obtain ⟨⟨_, hp_none⟩, hany⟩ := hp'
    have hp_goal : sf.mem ⊨
          ⌜S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none⌝ ∗ (anyHeap ∗ R) := by
      rw [satisfies_pure_sepConj]; exact ⟨hp_none, hany⟩
    simpa only [decPkSlotSpecPlacedOf, withMemInv, decPkSlotSpecBasePlaced, decPkSlotSpecPlaced,
      withLsCodeRoLoaded, sepConj_assoc] using hp_goal
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

/-- `CodeOk`-parameterized D2(c) poll contract on Block `518` (`dpPollEntryPlaced`). -/
def CliDpPollOkD2cStateMemInvAt [LibsignalPlacement] (CodeOk : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
  subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
  subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
  EncodeInjOn scopeKit →
  (∀ r, Scope r → scopeIn r) →
  S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope →
  (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
    FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm) →
  ∀ stk', dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      dpPollEntryPlaced
      (withMemInv CodeOk (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk'))

/-- `LibsignalFrozen`-guarded D2(c) poll contract on Block `518`. -/
abbrev CliDpPollOkD2cStateFrozenPlacedAt [LibsignalPlacement] :=
  @CliDpPollOkD2cStateMemInvAt _ (LibsignalFrozen lsmpl)

theorem cliDecryptPrekey_slotOk_d2c_of_pollAt_frozen_placed [LibsignalFullPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl g W X B S Scope)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecFrozenPlaced A lim DecPkEnv S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl g W
  have hEq : CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced H =
      dpPollProgPlaced H := by
    dsimp only [CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced,
      dpPollProgPlaced, stageP1ProgPlaced]
    rw [hpan]
  have : IsLsBlockProg prog i (Rust.withPanics H) := by rw [hpan]; exact hcaller
  intro stk h1 h2
  have hstk : cliDecryptPrekeyNeed B ≤ stk := hneed ▸ h1
  exact dpSlot_ok_state_of_codeOk_placed (LibsignalFrozen lsmpl) B S stk hstk h2
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := H)
      (dpSlotPollKStatePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' hs1 hs2 => by
        rw [hpan]
        exact hpoll hh (hEq ▸ hRead) (hEq ▸ hDeser) hinjK hsub hS hok stk' hs1 hs2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢; omega)
      h2)

/-- Lift a `[LibsignalFullPlacement]` poll proof on Block `518` to `DecPkD2cSlotOkFrozenPlaced`
on `lsProg_579`. -/
theorem decPkD2cSlotOk_of_poll_frozen_placed [LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hpoll : ∀ X S,
      CliDpPollOkD2cStateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl g W X cliRunBudgets S scopeIn) :
    DecPkD2cSlotOkFrozenPlaced mmpl g W A lim DecPkEnv := by
  intro X S needs sEnvs hsDec hfiles hdec hdecOk hneed
  dsimp only [slotsOfDecPkPlacedOf]
  rw [hsDec]
  exact cliDecryptPrekey_slotOk_d2c_of_pollAt_frozen_placed
    (prog := lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 579)
    A lim ReadEnv DeserEnv DecPkEnv mmpl g W X cliRunBudgets S scopeIn needs
    hh hRead hDeser encodeInjOn_deserializeScopeP_Q (fun _ h => h) hdec
    (fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩) (hpoll X S) hneed

/-! ## 3. `CodeOk`-Parameterized Stage P2 Statements and Path A Composition -/

/-- `CodeOk`-parameterized Stage P2 Path A statement (`rfl` at `CodeOk := LibsignalCodeRoLoaded lsmpl`,
and accepts `LibsignalFrozen lsmpl s1.mem` at `CodeOk := LibsignalFrozen lsmpl`). -/
def StageP2PathAQpanCliMemInvAtStmt [LibsignalPlacement] (CodeOk : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {st_b : M.σ} (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (g1 : StoresGhost) (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
    FitsEnv M lim st_b (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    loadRec Scope y.g.F y.g.peer.val = .ok none →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 →
    CodeOk s1.mem →
    s0.trace <+: s1.trace → s1.sp = sp → sp + 0xcd0#64 = s0.sp → dpClosSubStack B ≤ sp.toNat →
    s1.pc = dpPollEntryPlaced + 0x0868#64 → s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2PathAErrPlaced A lim st_b P2PathAErrEnv X W B S Scope y s0 s1 sf sp Pf → Q sf Pf) →
    (hok : ∀ (evs : List AllocEvent) (s2 : State)
      (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
      (recG : SessionGhost) (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2PathAOkEnv y.g evs → whisperG = y.g.msgG.msg → y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 s2 →
      s2.trace = s1.trace → s2.pc = dpPollEntryPlaced + 0x1778#64 → s2.status = .Running →
      s2.sp = sp → (s2.sp &&& 15#64 == 0#64) = true → s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 → s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl s2.mem →
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
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗ storesAt A.repAlloc y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores g1 ∗ LsTokenInit ∗ lsLogOff ∗
       stackAt sp (dpClosSubStack B)) Q Qpan

/-- `CodeOk`-parameterized Stage P2 Over (`Path C`) statement (`rfl` at `CodeOk := LibsignalCodeRoLoaded lsmpl`,
and accepts `LibsignalFrozen lsmpl s1.mem` at `CodeOk := LibsignalFrozen lsmpl`). -/
def StageP2OverQpanCliMemInvPlacedStmt [LibsignalPlacement] (CodeOk : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem) {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S)) (st_b : M.σ)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (g1 : StoresGhost) (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    loadRec Scope y.g.F y.g.peer.val = .ok (some r) →
    r.currentSession = some s_old →
    ¬ SessMatchesPm s_old y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 →
    CodeOk s1.mem →
    s0.trace <+: s1.trace → s1.sp = sp → sp + 0xcd0#64 = s0.sp → dpClosSubStack B ≤ sp.toNat →
    s1.pc = dpPollEntryPlaced + 0x0868#64 → s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2OverErrPlaced A lim st_b P2OverErrEnv X W B S Scope y r s0 s1 sf sp Pf → Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey) (recG : SessionGhost)
      (prevCap prevPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 → prevCap ≠ 0#64 → y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 s2 →
      s2.trace = s1.trace → s2.pc = dpPollEntryPlaced + 0x1778#64 → s2.status = .Running →
      s2.sp = sp → (s2.sp &&& 15#64 == 0#64) = true → s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 → s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         Over.stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (encSession (Over.clearPending s_old)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗ storesAt A.repAlloc y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores g1 ∗ LsTokenInit ∗ lsLogOff ∗
       stackAt sp (dpClosSubStack B)) Q Qpan

/-- Path A post-Stage-P1 allocation-event envelope (`opt = none` branch of `CliDpPollTrustedEnv`). -/
def PathAPostP1Env [LibsignalPlacement] {A : CryptoVerification.RustHeap.RustAlloc}
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost)
    (kitEnv : SessionStoreBudgetEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B)))
    (ikitEnv : IdentityStoreBudgetEnv (cliPollIdKitPlaced A g.F g.peer (cliKitStk B)))
    (pkKitEnv : PreKeyStoreBudgetEnv (cliPollPkKitPlaced A g.F (pmPreKeyId g.msg) (cliKitStk B)))
    (kpkKitEnv : ∀ kpkId spkId, KyberPreKeyStoreBudgetEnv
      (cliPollKpkKitPlaced A g.F kpkId spkId g.msg.baseKey (cliKitStk B)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (CliStageP1OkEnv (A := A) B ReadEnv DeserEnv g)
      (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv g) evs ∨
    ∃ m i k kp reg dk recG,
      g.msg = pmOfE m i ∧
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
      pkStoreKeys g.F m = some k ∧
      StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
      StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
      (SeqEnv (SeqEnv (CliStageP1OkEnv (A := A) B ReadEnv DeserEnv g) (P2PathAOkEnv g))
          (StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            g.peer g.me g.msgG.msg g.msg.message
            (g.msg.message.messageVersion.zeroExtend 32) g.coins) evs ∨
       ∃ G₁ G' pt,
         (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
           g.msg.message.messageVersion.zeroExtend 32 ∧
         CloneRel recG G₁ ∧ G₁.AfterTryDecrypt true G' ∧
         (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt ∧
         SeqEnv
           (SeqEnv
             (SeqEnv (CliStageP1OkEnv (A := A) B ReadEnv DeserEnv g) (P2PathAOkEnv g))
             (StageP3OkPrefixEnv tdEnv recG G₁
               (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
               g.peer g.me g.msgG.msg g.msg.message g.coins))
           (StageP4PathAEnv
             (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B)) kitEnv
             (cliPollIdKitPlaced A g.F g.peer (cliKitStk B)) ikitEnv
             (cliPollPkKitPlaced A g.F (pmPreKeyId g.msg) (cliKitStk B)) pkKitEnv
             (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey (cliKitStk B))
               (kpkKitEnv m.kpkId m.spkId)
             StoresGhost.opened.sessions StoresGhost.opened.identity
             StoresGhost.opened.oneTime StoresGhost.opened.kyber
             g.peer.val g.msg.identityKey m.opkId m.kpkId m.spkId g.msg.baseKey
             { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
               state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins
                 (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
               pendingPreKey := none
               pendingKyberPreKey := none }) evs)

private theorem hookSat_sessionShimBudget_of_codec {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · exact ⟨hkeep, hsym, Or.inl ⟨hret, hcc, hpost⟩⟩
  · exact ⟨hkeep, hsym, Or.inr hrest⟩

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
    (hookSat_sessionShimBudget_of_codec hh.codecHooks.shim)
    hh.codecHooks.alloc
    (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)

private theorem cliSenderChainClone3_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    SenderChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  senderChainClone3_placed_ok_of_hooks
    (hookSat_sessionShimBudget_of_codec hh.codecHooks.shim)
    hh.codecHooks.alloc
    (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)

set_option maxHeartbeats 1000000 in
/-- `CodeOk`-parameterized pointwise Path A branch consuming `StageP2PathAQpanCliMemInvAtStmt CodeOk`
and `PathAPostP1Env`. -/
theorem closure_pathA_memInv_ok_at [LibsignalPlacement] (CodeOk : Memory → Prop)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2A : StageP2PathAQpanCliMemInvAtStmt CodeOk A lim ReadEnv X mmpl gh W B P2PathAErrEnv P2PathAOkEnv)
    (hP3 : StageP3GenStepsVRegsPlacedStmt)
    (hP4 : StageP4PathAPlacedStmt)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r', Scope r' → scopeIn r')
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kitEnv : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)))
    (ikitEnv : IdentityStoreBudgetEnv (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)))
    (pkKitEnv : PreKeyStoreBudgetEnv
      (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)))
    (kpkKitEnv : ∀ kpkId spkId, KyberPreKeyStoreBudgetEnv
      (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey (cliKitStk B)))
    (evs_p1 : List AllocEvent) (hevs_p1 : CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs_p1)
    (hfits_A : FitsEnv M lim y.st
      (PathAPostP1Env (A := A.repAlloc) W X B ReadEnv DeserEnv P2PathAErrEnv P2PathAOkEnv tdEnv
        y.g kitEnv ikitEnv pkKitEnv kpkKitEnv))
    (hEnv_A : ∀ evs,
      PathAPostP1Env (A := A.repAlloc) W X B ReadEnv DeserEnv P2PathAErrEnv P2PathAOkEnv tdEnv
        y.g kitEnv ikitEnv pkKitEnv kpkKitEnv evs → DecPkEnv y.g evs)
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok none))
    (hsteps01 : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1)
    (htr1 : s1.trace = s0.trace) (hcode1 : CodeOk s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64) (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64)
      (lsρ cliKyberPreKeyVtSym)) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  dsimp only [cliPollSessKitPlaced] at hload_rel
  have hloadS : loadRec Scope y.g.F y.g.peer.val = .ok none :=
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
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32
  have hpre_split :
      stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ⊢
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B)) ∗ Fr_tail := by
    dsimp only [Fr_tail]; sep_frame
  have hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g) :=
    (hfits_A.mono fun _ h => Or.inl h).seq_right hevs_p1
  refine sepWPp_conseq_pre hpre_split
    (sepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine hP2A S Scope y StoresGhost.opened s0 s1 sp rngPtr v_a8 v_b8 v_d0 _ _
    hh hReadFile hDeser hfits_p2 hcoins hdecOk hsub hfPeer hloadS htrusted rfl hfiles1 hcode1
    (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hsp_sub hpc1 hrun1 hsp_align1 hregs1 ?_ ?_
  · intro sf Pf _ _ _ hsf_sp hcs_f hvregs_f _ hErr
    rcases hErr with ⟨err, evs_p2, hevs_p2, hne_p, hne_s, htr_f, hmodel, hpost_f⟩
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hpost_f' :
        Pf ⊢ dpFutDoneAt y.fut ∗ memRegion sp 3280 ∗ decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          lsLogOff ∗ A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          stackAt sp (dpClosSubStack B) ∗ anyHeap := by
      rw [M.stepEvents_append evs_p1 evs_p2 y.st]; exact hpost_f
    have hm1 := Satisfies.mono (sepConj_mono_left hpost_f') hm_f
    have hm2 : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          lsLogOff ∗ A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          anyHeap ∗ dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Satisfies.mono (by dsimp only [Fr_tail]; sep_frame) hm1
    have hout := slotOutTr_of_reject (tr0 := s0.trace) (trf := sf.trace)
      StoresGhost.opened hS hne_p hne_s hmodel
    have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
      (evs_p1 ++ evs_p2) StoresGhost.opened (.error err) anyHeap
      (hEnv_A _ (Or.inl (SeqEnv.append hevs_p1 (Or.inl hevs_p2)))) hh hsteps0f htr_sf hout
    exact Satisfies.mono (sepConj_mono_left hpost_goal) hm2
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
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗ storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents evs_p2 (M.stepEvents evs_p1 y.st))
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗ F_p3 ⊢
        LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗ F_p3 := by
      rw [← M.stepEvents_append evs_p1 evs_p2 y.st]; exact Entails.refl _
    have hfits_p3 : FitsEnv M lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
        (StageP3Env tdEnv recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins) :=
      (hfits_A.mono fun _ h =>
        Or.inr ⟨m, i, k, kp, reg, dk, recG, hpm_eq, hi, hk, hkp, hreg, hacc, hex, Or.inl h⟩).seq_right
        (SeqEnv.append hevs_p1 hevs_p2)
    refine sepWPp_conseq_pre hpre_p3
      (sepWPp_genP3_to_tailQpan_placed A lim DecPkEnv B S stk' y hpan_model ?_)
    refine hP3 (cliGhostExterns gh (cliExternsPlaced mmpl W)) W.C 0#64 W.Q.K
      hh.alloc (cliChainClone3_budget_placed_ok mmpl gh W hh)
      (cliSenderChainClone3_budget_placed_ok mmpl gh W hh)
      hTryDec s0 s2 y.fut y.cx y.out 8#64 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message F_p3 _
      hfits_p3 (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdecOk)) hSeeds hRC hPqLt
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
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]; exact hent_s'
      have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced A.repAlloc σ y.g.stores
        hsub hfPeer hdecOk (pid := pid) (sid := m.spkId) (kid := m.kpkId) (kbk := y.g.msg.baseKey)
      have hunpack_p3 : P_s' ∗ F_p3 ⊢
          P_s' ∗
          (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
              (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (coroOpkIdAtP4 y.fut m.opkId)
              (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
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
        dsimp only [cliPollStoresKitsAtPlaced]; sep_frame
      have hfits_p4 :=
        (hfits_A.mono fun _ h =>
          Or.inr ⟨m, i, k, kp, reg, dk, recG, hpm_eq, hi, hk, hkp, hreg, hacc, hex,
            Or.inr ⟨G₁, G', pt, hver, hcl, hdec_rel, hok, h⟩⟩).seq_right
          (SeqEnv.append (SeqEnv.append hevs_p1 hevs_p2) hevs_p3)
      exact sepWPp_conseq_pre hunpack_p3
        (closure_pathA_p4_cont_placed hP4 B S hh hReadFile hDeser hS stk' hneed hstk63 y
          hfPeer hdecOk hloadS hcur htrusted m i k kp reg dk
          kitEnv ikitEnv pkKitEnv (kpkKitEnv m.kpkId m.spkId)
          ((evs_p1 ++ evs_p2) ++ evs_p3) recG G₁ G'
          rngPtr whisperMsgPtr ptCap ptPtr y.g.msgG.msg preKeyMsgRem P_s' R pt s0 s2 s'
          hpm_eq hi hk hkp hreg hacc hex hfits_p4
          (fun evs_p4 he4 => hEnv_A _ (Or.inr ⟨m, i, k, kp, reg, dk, recG, hpm_eq, hi, hk, hkp,
            hreg, hacc, hex, Or.inr ⟨G₁, G', pt, hver, hcl, hdec_rel, hok,
              SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 hevs_p2) hevs_p3)
                (Or.inr (Or.inr (Or.inr he4)))⟩⟩))
          (fun evs_p4 he4 => hEnv_A _ (Or.inr ⟨m, i, k, kp, reg, dk, recG, hpm_eq, hi, hk, hkp,
            hreg, hacc, hex, Or.inr ⟨G₁, G', pt, hver, hcl, hdec_rel, hok,
              SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 hevs_p2) hevs_p3)
                (Or.inr (Or.inl he4))⟩⟩))
          hmsg_fold hs2_files htr20 hs2_sp hsp_align2 hsp_sub
          hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
          hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'')
    · intro G₁ G' evs_p3 e sf P_f hver hcl hdec_rel hevs_p3 herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗ memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPost_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out 8#64 e ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]; exact hent_f
      have he3_env : StageP3Env tdEnv recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
        unfold StageP3Env; simp only [hver, ↓reduceIte]; exact ⟨G₁, hcl, hevs_p3⟩
      exact stageP3_exit_pathA_to_pollPost_placed B S hh hS stk' hneed hstk63 y
        ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf rngPtr whisperMsgPtr y.g.msgG.msg preKeyMsgRem
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins))
        P_f R m.opkId m.kpkId m.spkId e
        (hEnv_A _ (Or.inr ⟨m, i, k, kp, reg, dk, recG, hpm_eq, hi, hk, hkp, hreg, hacc, hex,
          Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 hevs_p2) he3_env)⟩))
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver herr hne_p)
        hent_f' hsf_sp htr_f hcs_f hvregs_f
    · intro evs_p3 sf P_f hver_ne hevs_p3 hent_f hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗ memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPost_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out 8#64
              (.invalidMessage .preKey .decryptionFailed) ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (coinsAtPlaced y.g.coinsP y.g.coins) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]; exact hent_f
      have he3_env : StageP3Env tdEnv recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
        unfold StageP3Env; simp only [hver_ne, ↓reduceIte]; exact hevs_p3
      exact stageP3_exit_pathA_to_pollPost_placed B S hh hS stk' hneed hstk63 y
        ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf rngPtr whisperMsgPtr y.g.msgG.msg preKeyMsgRem
        (coinsAtPlaced y.g.coinsP y.g.coins) P_f R m.opkId m.kpkId m.spkId
        (.invalidMessage .preKey .decryptionFailed)
        (hEnv_A _ (Or.inr ⟨m, i, k, kp, reg, dk, recG, hpm_eq, hi, hk, hkp, hreg, hacc, hex,
          Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 hevs_p2) he3_env)⟩))
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver_ne)
        hent_f' hsf_sp htr_f hcs_f hvregs_f

end LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
