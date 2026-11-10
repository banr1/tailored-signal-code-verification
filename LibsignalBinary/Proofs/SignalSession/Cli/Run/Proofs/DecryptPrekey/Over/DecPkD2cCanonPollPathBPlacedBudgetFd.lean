/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonKitsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathBP4PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFoldPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
import ProofLib

/-!
# Kit-Parametric D2(c) Path B (`Matched`) Full Poll Branch

Proves `closure_pathB_frozen_placed_ok_at_gv_of_kits`, composing
`stageP2Matched_noRead_framed_cli_placed_ok`, `stageP3PrevEmptyVRegs_of_base_full_placed_ok`, and
`closure_pathB_p4_cont_placed_at_gv_of_kits` from `CanonPollKitsPlacedOk`.
-/

@[expose] public section

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification (lsBlackBoxU8Sym ls_hook_ok_ultra_of_mem)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (SessionExtraRel p1LoadedRecordAt stageP1ProgPlaced)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost apiDecResultAt preKeyMsgAt)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (noAllocShimSpec rootStack)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost SignalMessageGhost decryptDraws protocolAddressAt signalMessageAt uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym cliSignedPreKeyVtSym dirAt)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem decResAt dpPollNeed slotOutTr)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOk₀ SessMatchesPm decPkDef dpFutDoneAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (LsTokenInit StageP1PostRegs apiDecResultAt_proto_entails_decResAt cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKitPlaced cliPollSpkKitPlaced cliPollStoresKitsAtPlaced cliPollStoresKitsAtPlaced_entails_storesAt closureCalleeSaved_toCalleeSavedPreserved decPkDef_pathB_err decPkDef_pathB_panic decPkDef_pathB_remId_ne decPkDef_pathB_ver_ne distinctSid_of_decPkOk₀ dpClosSubStack dpPollEntryPlaced dpPollProgPlaced pathB_scopeIn_and_match pmKyberId pmPreKeyId preKeyMsgAt_eq_base_idKey_sep preKeyMsgRemBaseIdKeyAt rootStack_le_subStack sepWPp_conseq_pre sepWPp_entails_post sepWPp_lift_entails_post slotOutTr_of_reject sp_frame_sub_add stackAt_subStack_sub_eq stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt stageP3Sub5ExtraPrePrevEmpty x29_eq_sp0_sub_60 x29_eq_sp_add_c70)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetAux (StageP2MatchedBridgeEnv)
open LibsignalBinary.Proofs.Placed.Bridge (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open LibsignalBinary.Proofs.Placed.PlacedCallSym (ls_subroutine_ok_of_block subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget (sepWPp_genP3_to_tailQpan_placed sepWPp_pollGoal_frame_placed stageP3_exit_prevEmpty_to_pollPost_placed storesAt_opened_entails_cliPollStoresKitsAtPlaced)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathBPlacedBudgetFd

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000


open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification.CliHandshake.Placed (lsProg_530)
open scoped CryptoVerification.CliHandshake.Placed
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open scoped CryptoVerification.CliHandshake.RespClosurePlaced

open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other withPanics_cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.Slots (
  blackBox_row_placed cliGhostExterns_sat_of_cliExternsPlaced
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  noAllocShimBudgetSpec publicKeySerializeSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget (
  public_key_serialize_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget (
  StageP2MatchedBridgeEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget (
  strToOwnedLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlacedBudget (
  str_to_owned_local2_placed_ok_at
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget (
  StageP2MatchedEnv StageP2MatchedMismatchEnv stageP2_matched_ok_framed_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  chainClone3_placed_ok_of_hooks senderChainClone3_placed_ok_of_hooks
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget (
  drop_session_structure4_placed_ok_at
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_sessionMemcpyRegion_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  genP3Pre_placed genP3S5PostFrame_placed
  stageP3DispatchOkMidPrevEmpty_placed stageP3ErrPostPrevEmpty_placed
  StageP3Env StageP3OkPrefixEnv StageP3ErrEnv StageP3VerNeEnv
  pollTryDecryptPlacedSpecTPTight CliTryDecryptPqV1PlacedStmt StageP3PrevEmptyVRegsPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced StageP4MatchedEnv StageP4MatchedPlacedStmt StageP4MatchedStoreStepEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBPlacedBudget (
  stageP3ErrPrevEmpty_entails_exit_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget (
  cliFiles_eq_of_trace_eq_placed exit_entails_dpPollPost_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFoldPlacedBudget (
  matched_mismatch_fold_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFoldPlacedBudget (
  matched_match_fold_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPrePlacedBudget (
  matchedInnerFramePlaced matched_entry_unpack_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollSessSeqFreeBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonKitsPlacedBudgetFd (
  CanonPollKitsPlacedOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd (
  CanonSessionGhostValid ex_frame_genP3
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathBP4PlacedBudgetFd (
  closure_pathB_p4_cont_placed_at_gv_of_kits
)

local elab "erase_hkdf_arm64_norm" : command => Lean.Elab.Command.liftCoreM do
  for n in [``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase n `arm64_norm
erase_hkdf_arm64_norm

/-! ## 1. `0`-`hRead` Path B Stage P2 Instantiation (`stageP2Matched_noRead_framed_cli_placed_ok`) -/

private theorem dpPollProgPlaced_eq_withPanics_p4 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) := by
  dsimp only [dpPollProgPlaced, stageP1ProgPlaced]
  rw [withPanics_cliGhostExterns mmpl gh W]

private theorem hookSat_withPanics_placed_p4 (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) {sym : String} {α : Type} {spec : Spec α}
    (hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym spec) :
    HookSat (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) sym spec := by
  rw [withPanics_cliGhostExterns mmpl gh W]
  exact hsat

private theorem hookSat_noAllocShimBudget_of_withVmPreserved_p4 {H : String → Option (State → State)}
    (hsat : HookSat H CryptoVerification.lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H CryptoVerification.lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases hsat with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

private theorem cliExternsPlaced_blackBox_withPanics_p4 (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsBlackBoxU8Sym =
      some blackBoxHook := by
  rw [withPanics_cliGhostExterns mmpl gh W,
    cliGhostExterns_other gh _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  exact cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)

private theorem cliPublicKeySerialize_placed_ok_p4 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)) :=
  ls_subroutine_ok_of_block (i := 518) (j := 205)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (public_key_serialize_placed_ok
        (hookSat_withPanics_placed_p4 mmpl gh W
          (hookSat_noAllocShimBudget_of_withVmPreserved_p4 hh.codecHooks.shim))
        (hookSat_withPanics_placed_p4 mmpl gh W hh.codecHooks.alloc)))

private theorem cliStrToOwnedLocal2_placed_ok_p4 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A lim)) :=
  str_to_owned_local2_placed_ok_at (i := 518)
    (ls_hook_ok_ultra_of_mem (i := 530)
      (hookSat_withPanics_placed_p4 mmpl gh W
        ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸
          hh.codecHooks.shim))
      (by decide))
    (ls_hook_ok_ultra_of_mem (i := 530)
      (hookSat_withPanics_placed_p4 mmpl gh W hh.codecHooks.alloc) (by decide))
    (ls_hook_ok_ultra_of_mem (i := 530)
      (hookSat_withPanics_placed_p4 mmpl gh W hh.memcpyRO) (by decide))

private theorem cliDealloc_placed_ok_p4 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim) :=
  ls_hook_ok_ultra_of_mem (i := 518)
    (hookSat_withPanics_placed_p4 mmpl gh W hh.codecHooks.dealloc)
    (by decide)

private theorem cliDropSessionStructureLocal2_placed_ok_p4 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_ok_at (i := 518)
    (hookSat_withPanics_placed_p4 mmpl gh W hh.codecHooks.dealloc)
    (by decide)

set_option maxHeartbeats 800000 in
private theorem stageP2Matched_noRead_framed_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {st_b : M.σ}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (F_frame : SepProp) (Q Qpan : State → SepProp → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hfits : FitsEnv M lim st_b (StageP2MatchedEnv sess y.g.msg.identityKey))
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hMatch : SessMatchesPm sess y.g.msg)
    (hcro : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (_htr : s0.trace <+: s1.trace)
    (hsp1 : s1.sp = sp)
    (hsp0 : sp + 0xcd0#64 = s0.sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (halign1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym))
    (hmismatch : sess.state.remoteIdentity ≠ some y.g.msg.identityKey →
      ∀ (evs : List AllocEvent) (sf : State) (Pf : SepProp),
        StageP2MatchedMismatchEnv evs →
        sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf →
        sf.sp = s0.sp →
        sf.trace = s1.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        (Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          apiDecResultAt A.repAlloc y.out
            (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          coinsInstalledPlaced y.g.coinsP y.g.coins ∗
          LsTokenInit ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp rootStack) →
        Q sf (Pf ∗ F_frame))
    (hmatch : sess.state.remoteIdentity = some y.g.msg.identityKey →
      ∀ (evs : List AllocEvent) (s2 : State) (g : RecordGhost) (recG : SessionGhost)
        (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
        (preKeyMsgRem : SepProp)
        (opkHi kyberPreKeyId signedPreKeyId : BitVec 32),
        StageP2MatchedBridgeEnv evs →
        whisperG = y.g.msgG.msg →
        SessionExtraRel recG sess →
        (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem ⊢
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 s2 →
        s2.pc = dpPollEntryPlaced + 0x1778#64 →
        s2.status = .Running →
        s2.sp = sp →
        (s2.sp &&& 15#64 == 0#64) = true →
        s2.trace = s1.trace →
        s2.readReg64 .x19 = y.fut →
        s2.readReg64 .x27 = sp + 0x370#64 →
        s2.readReg64 .x29 = s0.sp - 0x60#64 →
        calleeSavedVRegs s2 = calleeSavedVRegs s0 →
        CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
          ((LsTokenInit ∗
            genP3Pre_placed A lim (M.stepEvents evs st_b) s2.sp (s2.readReg64 .x29)
              y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
              recG sess.state y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
            stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s2 y.fut y.out 8#64 g 0#8 ∗
            stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
              (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
              (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
              (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
               ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
               memRegion (y.fut + 0x2a8#64) 4) ∗
            stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
            ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRem) ∗ F_frame)
          Q Qpan) :
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      ((stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
        p1LoadedRecordAt Scope A.repAlloc y.fut (some ⟨some sess⟩) ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack) ∗ F_frame)
      Q Qpan := by
  rw [dpPollProgPlaced_eq_withPanics_p4 mmpl gh W] at hmismatch hmatch ⊢
  rcases hregs with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, hx28, hx29, hvregs1⟩
  have hunpack :=
    matched_entry_unpack_placed (Scope := Scope) y st_b sess s0 s1 sp rngPtr v_a8 v_b8 v_d0
  refine sepWPp_conseq_pre (sepConj_mono_left hunpack) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun g => ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun w => ?_
  let F_in := matchedInnerFramePlaced A.repAlloc y rngPtr sp
  have hpre_assoc :
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2MatchedPrePlaced
        (A.atState lim st_b s1) s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
        y.g.peerA (y.g.msgA + 0xc8#64)
        w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
        w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
        w.u_2a8 (v_b8.extractLsb' 0 32)
        y.g.msg.messageVersion y.g.msg.message.messageVersion
        w.b_4f1 0#8 0#8 0#8 w.b_3ac
        y.g.msg.baseKey y.g.msg.identityKey g ⟨some sess⟩ F_in) ∗ F_frame =
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget.stageP2MatchedPrePlaced
        A lim st_b s0 s1 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
        y.g.peerA (y.g.msgA + 0xc8#64)
        w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
        w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
        w.u_2a8 (v_b8.extractLsb' 0 32)
        y.g.msg.messageVersion y.g.msg.message.messageVersion
        w.b_4f1 0#8 0#8 0#8 w.b_3ac
        y.g.msg.baseKey y.g.msg.identityKey g ⟨some sess⟩ (F_in ∗ F_frame) := by
    dsimp only [
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2MatchedPrePlaced,
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget.stageP2MatchedPrePlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedPrePlaced,
      CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff]
    sep_ac_rfl
  rw [hpre_assoc]
  refine sepWPp_entails_post ?_
  exact stageP2_matched_ok_framed_placed
    (cliPublicKeySerialize_placed_ok_p4 mmpl gh W hh)
    (cliStrToOwnedLocal2_placed_ok_p4 mmpl gh W hh)
    (cliDealloc_placed_ok_p4 mmpl gh W hh)
    (cliExternsPlaced_blackBox_withPanics_p4 mmpl gh W)
    (cliDropSessionStructureLocal2_placed_ok_p4 mmpl gh W hh)
    st_b s0 s1
    sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
    y.g.peerA (y.g.msgA + 0xc8#64)
    w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
    w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
    w.u_2a8 (v_b8.extractLsb' 0 32)
    y.g.msg.messageVersion y.g.msg.message.messageVersion
    w.b_4f1 0#8 0#8 0#8 w.b_3ac
    y.g.msg.baseKey y.g.msg.identityKey
    g ⟨some sess⟩ sess (F_in ∗ F_frame)
    rfl hMatch.1 hMatch.2 hfits
    hcro hsp1 hsp_root hpc1 hrun1 halign1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28
    (x29_eq_sp_add_c70 hsp0 hx29)
    (fun hne evs hevs sf Pf hpcf hrunf hsteps hspf htrf hcsf hvregsf hcrof hent => by
      have hfold :=
        matched_mismatch_fold_placed y (M.stepEvents evs st_b) s0 sf sp rngPtr
          (v_b8.extractLsb' 0 32) w
      have hpost_assoc :
          LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget.stageP2MatchedMismatchPostPlaced
            A lim (M.stepEvents evs st_b) s0 sf sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
            y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
            y.g.peerA (y.g.msgA + 0xc8#64)
            w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
            w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
            w.u_2a8 (v_b8.extractLsb' 0 32)
            y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
            y.g.msg.baseKey y.g.msg.identityKey (F_in ∗ F_frame) =
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2MatchedMismatchPostPlaced
            (A.atState lim (M.stepEvents evs st_b) sf) s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
            y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
            y.g.peerA (y.g.msgA + 0xc8#64)
            w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
            w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
            w.u_2a8 (v_b8.extractLsb' 0 32)
            y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
            y.g.msg.baseKey y.g.msg.identityKey F_in ∗ F_frame := by
        dsimp only [
          LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget.stageP2MatchedMismatchPostPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2MatchedMismatchPostPlaced,
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedMismatchPostPlaced,
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff]
        sep_ac_rfl
      rw [hpost_assoc] at hent
      exact ⟨_, Entails.trans hent (sepConj_mono_left hfold),
        hmismatch hne evs sf _ hevs hpcf hrunf hsteps (hspf.trans hsp0)
          htrf hcsf (hvregsf.trans hvregs1) hcrof (Entails.refl _)⟩)
    (fun heq evs hevs s2 recG opkHi kyberPreKeyId signedPreKeyId _hgcur hextra hsteps
        hpc2 hrun2 hsp2 halign2 htr2 hx19_2 hx27_2 hx29_2 hvregs2 hcro2 => by
      have hx29_2' := x29_eq_sp0_sub_60 hsp0 hx29_2
      refine sepWPp_lift_entails_post ?_
      refine sepWPp_conseq_pre
        (matched_match_fold_placed y (M.stepEvents evs st_b) sess s0 s2 sp rngPtr v_d0 g recG
          opkHi kyberPreKeyId signedPreKeyId F_frame hcoins
          hsp2 hx19_2 hx27_2) ?_
      exact hmatch heq evs s2 g recG y.g.msgA y.g.msgG.msg
        (((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
        opkHi kyberPreKeyId signedPreKeyId
        hevs rfl hextra
        (Entails.of_eq (by rw [preKeyMsgAt_eq_base_idKey_sep]; sep_ac_rfl))
        hsteps hpc2 hrun2 hsp2 halign2 htr2 hx19_2 hx27_2 hx29_2'
        (hvregs2.trans hvregs1) hcro2)

/-! ## 2. Stage P3 Callee Helpers & Full Path B Branch (`closure_pathB_frozen_placed_ok_at_gv_of_kits`) -/

private theorem hookSat_sessionShimBudget_of_codec_p4 {H : LibsignalHooks}
    (h : HookSat H CryptoVerification.lsRustNoAllocShimSym
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec)) :
    HookSat H CryptoVerification.lsRustNoAllocShimSym sessionShimBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · exact ⟨hkeep, hsym, Or.inl ⟨hret, hcc, hpost⟩⟩
  · exact ⟨hkeep, hsym, Or.inr hrest⟩

private theorem cliChainClone3_budget_placed_ok_p4 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.ChainClone3OkPlaced A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  chainClone3_placed_ok_of_hooks
    (hookSat_sessionShimBudget_of_codec_p4 hh.codecHooks.shim)
    hh.codecHooks.alloc
    ((show withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
        LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec from rfl) ▸
      hh.codecHooks.memcpy)

private theorem cliSenderChainClone3_budget_placed_ok_p4 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.SenderChainClone3OkPlaced A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  senderChainClone3_placed_ok_of_hooks
    (hookSat_sessionShimBudget_of_codec_p4 hh.codecHooks.shim)
    hh.codecHooks.alloc
    ((show withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
        LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec from rfl) ▸
      hh.codecHooks.memcpy)

private theorem cliDropSessionStructure4_budget_placed_ok_at_p4 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_ok_at (i := 518) hh.codecHooks.dealloc (by decide)

set_option maxHeartbeats 800000 in
theorem closure_pathB_frozen_placed_ok_at_gv_of_kits [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CanonPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : CryptoVerification.SignalSession.Cli.Slots.EncodeInjOn CryptoVerification.SignalSession.Cli.Slots.scopeKit)
    (hsub : ∀ r', Scope r' → CryptoVerification.SignalSession.Cli.Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kitEnv : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer (cliKitStk B)))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)))
    (hkitEnv : kitEnv =
      cliPollSessSeqFreeBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
    (hikitEnv : ikitEnv =
      cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
    (evs_p1 : List AllocEvent)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2MatchedEnv sess y.g.msg.identityKey))
    (hevs_mismatch : sess.state.remoteIdentity ≠ some y.g.msg.identityKey →
      ∀ evs_p2, StageP2MatchedMismatchEnv evs_p2 →
        DecPkEnv y.g (evs_p1 ++ evs_p2))
    (hfits_p3 : sess.state.remoteIdentity = some y.g.msg.identityKey →
      ∀ evs_p2 recG,
        StageP2MatchedBridgeEnv evs_p2 →
        CanonSessionGhostValid recG sess →
        FitsEnv M lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
          (StageP3Env tdEnv recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins))
    (hfits_p4 : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG G₁ G' evs_p3 pt,
        StageP2MatchedBridgeEnv evs_p2 →
        CanonSessionGhostValid recG sess →
        CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt →
        FitsEnv M lim (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st)
          (StageP4MatchedEnv
            (cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
            (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
            CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
            y.g.peer.val y.g.msg.identityKey
            { sess with
              state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
              pendingPreKey := none
              pendingKyberPreKey := none }))
    (hevs_ok : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG G₁ G' evs_p3 pt evs_p4,
        StageP2MatchedBridgeEnv evs_p2 →
        CanonSessionGhostValid recG sess →
        CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt →
        StageP4MatchedStoreStepEnv
          (cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
          y.g.peer.val y.g.msg.identityKey
          { sess with
            state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
            pendingPreKey := none
            pendingKyberPreKey := none } evs_p4 →
        DecPkEnv y.g (((evs_p1 ++ evs_p2) ++ evs_p3) ++ evs_p4))
    (hevs_err : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG G₁ G' evs_p3 e,
        StageP2MatchedBridgeEnv evs_p2 →
        CanonSessionGhostValid recG sess →
        CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .error e →
        e ≠ .panic →
        DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3))
    (hevs_verNe : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version ≠ y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG evs_p3,
        StageP2MatchedBridgeEnv evs_p2 →
        CanonSessionGhostValid recG sess →
        StageP3VerNeEnv recG sess.state evs_p3 →
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
       p1LoadedRecordAt CryptoVerification.SignalSession.Cli.Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
       LsTokenInit ∗
       CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
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
  have hro1 : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
    ⟨CryptoVerification.LibsignalCodeLoaded.of_codeLoaded hfr1.2, hfr1.1⟩
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  dsimp only [cliPollSessKitPlaced] at hload_rel
  obtain ⟨hloadS, hr_eq, hIn, hMatch, _, _, hSeeds, hRC, hPqLt⟩ :=
    pathB_scopeIn_and_match hinjK hsub hfPeer hdecOk hload_rel hcur
  subst hr_eq
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  let F_p2 : SepProp :=
    ikit.identityAt y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
    kit.storeAt (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
  let Fr_tail : SepProp :=
    pkKit.storeAt (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced A.repAlloc σ y.g.stores
    hsub hfPeer hdecOk (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hstk_split := stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub
  have hpre_split :
      stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt CryptoVerification.SignalSession.Cli.Slots.scopeKit A.repAlloc y.fut (some ⟨some sess⟩) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
       LsTokenInit ∗
       CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      ((stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
          y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
        p1LoadedRecordAt CryptoVerification.SignalSession.Cli.Slots.scopeKit A.repAlloc y.fut (some ⟨some sess⟩) ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack) ∗ F_p2) ∗ Fr_tail := by
    rw [hstk_split]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores_in))))))) ?_
    unfold cliPollStoresKitsAtPlaced F_p2 Fr_tail
    sep_frame
  refine sepWPp_conseq_pre hpre_split (sepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine stageP2Matched_noRead_framed_cli_placed_ok mmpl gh W B S CryptoVerification.SignalSession.Cli.Slots.scopeKit y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_p2 _ _
    hh hfits_p2 hcoins hMatch hro1 (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hroot hpc1 hrun1 hsp_align1 hregs1 ?_ ?_
  · intro hrem_ne evs_p2 sf Pf hevs_p2 _ _ _ hsf_sp htr_f hcs_f hvregs_f _ hent_f
    let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hent_f' :
        Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          apiDecResultAt A.repAlloc y.out
            (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          coinsInstalledPlaced y.g.coinsP y.g.coins ∗
          LsTokenInit ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          stackAt sp rootStack := by
      rw [M.stepEvents_append evs_p1 evs_p2 y.st]
      exact hent_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_f')) hm_f
    have hdec_at := apiDecResultAt_proto_entails_decResAt A.repAlloc y.out
      (.invalidMessage .preKey .badCiphertext) err
    have hstores_out := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
      (F0 := y.g.F) (Scope := CryptoVerification.SignalSession.Cli.Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened
    have hm2 : sf.mem ⊨
        apiDecResultAt A.repAlloc y.out (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer pid sid kid kbk σ
          y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
        (protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins) ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
            stackAt sp rootStack) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [cliPollStoresKitsAtPlaced, F_p2, Fr_tail]; sep_frame) hm1
    have hm3 := Arm64.Satisfies.mono (sepConj_mono hdec_at (sepConj_mono_left hstores_out)) hm2
    rw [← hstk_split] at hm3
    have hm4 : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins) ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by sep_frame) hm3
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject CryptoVerification.SignalSession.Cli.StoresGhost.opened hS (err := err) nofun nofun
        (decPkDef_pathB_remId_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_ne)
    have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
      (evs_p1 ++ evs_p2) CryptoVerification.SignalSession.Cli.StoresGhost.opened (.error err)
      (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins)
      (hevs_mismatch hrem_ne evs_p2 hevs_p2) hh hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm4
  · intro hrem_eq evs_p2 s2 g recG whisperMsgPtr whisperG preKeyMsgRem
      opkHi kyberPreKeyId signedPreKeyId hevs_p2 hwg_eq hex hmsg_fold hsteps12 hpc2 hrun2
      hs2_sp hsp_align2 htr2 _ _ _ hvregs2 _hro2
    have hfr2 : CryptoVerification.LibsignalFrozen lsmpl s2.mem :=
      CryptoVerification.libsignalFrozen_of_keepsFrozen hfr1 hsteps12.keepsFrozen
    subst hwg_eq
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps02 htr20).trans hf0
    have hpan_model : sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .error .panic →
        (dpSlotPollKStatePlaced A lim DecPkEnv B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDef_pathB_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS htrusted hMatch hrem_eq hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
        (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
         ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
         memRegion (y.fut + 0x2a8#64) 4) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      ikit.identityAt y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
      kit.storeAt (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        (LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents evs_p2 (M.stepEvents evs_p1 y.st))
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s2 y.fut y.out 8#64 g 0#8 ∗
          stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
            (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
            (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
            (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
            (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
             ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
             memRegion (y.fut + 0x2a8#64) 4) ∗
          stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem) ∗ F_p2 ⊢
        LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s2 y.fut y.out 8#64 g 0#8 ∗
          F_p3 := by
      rw [← M.stepEvents_append evs_p1 evs_p2 y.st]
      dsimp only [F_p2, F_p3]
      sep_frame
    refine sepWPp_conseq_pre hpre_p3 (fun R_p3 hm_p3 hL_p3 => ?_)
    have hgv_rec : CanonSessionGhostValid recG sess := by
      refine ⟨hex, A.atState lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) s2, y.fut + 0xf8#64, s2.mem, ?_⟩
      dsimp only [genP3Pre_placed, CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3Pre_placed] at hm_p3
      exact ex_frame_genP3 hm_p3
    refine (sepWPp_genP3_to_tailQpan_placed A lim DecPkEnv B S stk' y hpan_model ?_) R_p3 hm_p3 hL_p3
    refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudget.stageP3PrevEmptyVRegs_of_base_full_placed_ok
      (M.stepEvents (evs_p1 ++ evs_p2) y.st) (cliGhostExterns gh (cliExternsPlaced mmpl W)) W.C 0#64 W.Q.K
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux.StageP3CalleesM3BasePlaced.of_cliExternsPlaced mmpl gh W hG)
      (cliChainClone3_budget_placed_ok_p4 mmpl gh W hh)
      (cliSenderChainClone3_budget_placed_ok_p4 mmpl gh W hh)
      hTryDec (cliDropSessionStructure4_budget_placed_ok_at_p4 mmpl gh W hh)
      s0 s2 y.fut y.cx y.out 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      g recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message F_p3 _
      (hfits_p3 hrem_eq evs_p2 recG hevs_p2 hgv_rec)
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdecOk)) hSeeds hRC hPqLt
      hfr2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' evs_p3 pt ptCap ptPtr s' P_s' hver hcl hdec_rel hevs_p3 hok hpt_le hpt_lt hpt_ne
        hsteps2' hpc' hrun' hs'_sp htr' hvregs' hx19' hx24' hx25' hx26' hx27' hx28'
        hro' hent_s'
      have hent_s'' :
          P_s' ⊢
            stageP3DispatchOkMidPrevEmpty_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 s' y.fut y.out 8#64
              ptCap ptPtr g pt 0#8 G'
              (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2 ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_s'
      exact closure_pathB_p4_cont_placed_at_gv_of_kits hDropNz mmpl gh W X B S Scope hh hKits hS stk' hneed hstk63
        y kitEnv ikitEnv hkitEnv hikitEnv sess ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 s'
        rngPtr whisperMsgPtr ptCap ptPtr y.g.msgG.msg preKeyMsgRem P_s' R
        opkHi kyberPreKeyId signedPreKeyId g recG G₁ G' pt
        hfPeer hdecOk hIn hloadS htrusted hMatch hrem_eq hex
        (hfits_p4 hrem_eq hver evs_p2 recG G₁ G' evs_p3 pt hevs_p2 hgv_rec hcl hdec_rel hevs_p3 hok)
        (fun evs_p4 hevs_p4 =>
          hevs_ok hrem_eq hver evs_p2 recG G₁ G' evs_p3 pt evs_p4
            hevs_p2 hgv_rec hcl hdec_rel hevs_p3 hok hevs_p4)
        hmsg_fold hs2_files htr20 hs2_sp hsp_sub hsp_align2 hver hcl hdec_rel hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s''
    · intro G₁ G' evs_p3 e sf P_f hver hcl hdec_rel hevs_p3 herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
            memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmpty_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out e ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_f
      exact stageP3_exit_prevEmpty_to_pollPost_placed B S hh hS stk' hneed hstk63
        y ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf rngPtr whisperMsgPtr y.g.msgG.msg
        preKeyMsgRem _ P_f R opkHi kyberPreKeyId signedPreKeyId e
        (hevs_err hrem_eq hver evs_p2 recG G₁ G' evs_p3 e hevs_p2 hgv_rec hcl hdec_rel hevs_p3 herr hne_p)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS htrusted hMatch hrem_eq hver herr hne_p)
        hent_f' hsf_sp htr_f hcs_f hvregs_f
    · intro evs_p3 sf P_f hver_ne hevs_p3 hent_f hsf_sp htr_f hcs_f hvregs_f _
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
            memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmpty_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out
              (.invalidMessage .preKey .decryptionFailed) ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (coinsAtPlaced y.g.coinsP y.g.coins) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_f
      exact stageP3_exit_prevEmpty_to_pollPost_placed B S hh hS stk' hneed hstk63
        y ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf rngPtr whisperMsgPtr y.g.msgG.msg
        preKeyMsgRem _ P_f R opkHi kyberPreKeyId signedPreKeyId
        (.invalidMessage .preKey .decryptionFailed)
        (hevs_verNe hrem_eq hver_ne evs_p2 recG evs_p3 hevs_p2 hgv_rec hevs_p3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_eq hver_ne)
        hent_f' hsf_sp htr_f hcs_f hvregs_f

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathBPlacedBudgetFd
