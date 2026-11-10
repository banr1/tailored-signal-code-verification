/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5Budget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.FetchDecrypt
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
meta import Lean -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNe
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common
import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Auxiliary Lemmas for Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Stage P3

Constructs `StageP3CalleesM3Placed` at `cliExternsPlaced mmpl W`, proves `sessionShimBudgetSpec`
version-mismatch lemmas (`stageP3_ver_ne_prevEmpty_sessionShim_placed_ok`), and discharges
zero-capacity Stage P3 error paths (`stageP3_sub5_err_zero_placed_ok`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (Crypto SessionState SignalMessage SignalProtocolError)
open CryptoVerification (
  LibsignalPlacement lsHandleErrorSym lsLogFilterAddr lsMemcpySym lsRustAllocSym lsRustDeallocSym
  lsRustNoAllocShimSym lsRustReallocSym lsmpl lsρ ls_hook_ok_ultra_of_mem withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack vecAt vecBuf vecHeader)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (recordResultAt rootStack sessionShimSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost protocolAddressAt sessionStateAt signalMessageAt
  speAt speWord utf8 vecResultAt
)
open CryptoVerification.LibsignalTripleRatchet.Getters (DropSpeGhost dropSpeStack withLsRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost growOneSpeStack lsLogOff
)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (SessionInline sessionHeap)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts (
  speAt_decomp6 speTag speTag_eq_speWord23_iff words6At
)
open CryptoVerification.E2E.Pqxdh.ResponderStore (pqxdhClosureStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved decryptPrekeySavedRegsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  cap_ne_noneCap_of_lt cell_join_head8 cell_split_head8 dfPtr_words_eq_decryptionFailedStr
  dropSessionStructure2Stack entails_replace_sub eq_of_sep_emp errs48_144_join
  extractLsb0_8_of_unpack64_cons memRegion17_split_eq memRegion20_fold memRegion20_split_eq
  memRegion48_words6_split_eq memRegion_17_split_eq recordError_preKey_of_speTag_ne_speWord23
  sessionStateAt_pack_head_tail sessionStateAt_unpack_head_tail sp370_36_err_split_eq
  speTag_ne_ok_of_ne_panic stageP3Sub5ExtraPre words3_repack_w32_2w64_w32
  words6At_preKey_decryptionFailed_entails_recordResultAt words6_entails_memRegion48
)
open CryptoVerification.CliHandshake.RespClosurePlaced (
  blkLib_eq_518 blkPl_518 instIsLsBlockProg_518 lsProg_518
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (
  genP3S5ModelPanicProp genP3SpillAll genP3SpillAll_entails_s5
  memRegion344_104_240_eq stackAt_root_split_grow
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  LsTokenInitM3 cloneExitPCPlaced dpClosureEntryM3Placed prevSessionsEmptyAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (pqLogLevelCellPlaced)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
  lsRustReallocSymCli
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots (
  cliGhostExterns_panic_handle_error cliGhostExterns_sat_of_cliExternsPlaced
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit dpPollEntryPlaced dpPollProgPlaced
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv
  VmPreserved rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (
  LsRetAddr624 lsRetAddr624_blockPlacement_base_add
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2PlacedBudget (
  dropSpe2VerSpec drop_spe2_ver_placed_ok_at
)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget (
  hookSat_noAllocShimBudget_of_withVmPreserved
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  chainClone3_placed_ok_of_hooks senderChainClone3_placed_ok_of_hooks
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget (
  drop_session_structure4_placed_ok_at
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5Budget (
  growOneSpe_post_zero_eq growOneSpe_pre_zero_eq
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  grow_one_spe_placed_ok_at set_session_state_placed_ok_at
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux (
  bind_sepWPp_false_steps_framed genP3PostPlaced genP3PrePlaced ret_sepWPp_frame_false
  sepWPp_weaken_frame
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux (
  bind_sepWP_lscro_frame_err call_lscl_nopanic_err call_lscl_ro_nopanic_err
  drop_spe2_placed_ok_at_of_dealloc fitsEnv_growOneSpe_of_fromVPostTd
  fitsEvents_alloc17_of_fromVPostTd freeOnlyEvs_append freeOnlyEvs_dealloc
  fromVPostTdEnv_of_nondup intro_lsro_decryptionFailed_err p3_alloc_2eac_placed_ok
  p3_err_dup_placed_wp p3_err_nondup_a_placed_wp p3_err_nondup_b_placed_wp
  p3_err_nondup_c_placed_wp p3_err_nondup_d_placed_wp p3_err_tail_dup_a_placed_wp
  p3_err_tail_nondup_a1_placed_wp p3_err_tail_nondup_a2_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlacedBudget (
  stageP3_err_ver_tail_prevEmpty_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlacedBudgetAux (
  StageP3VerNeM3Env dpClosureEntryVerPlaced fitsS1_of_fitsM3 fitsTail_of_fitsM3
  p3_err_ver_e_placed_wp p3_err_ver_f_placed_wp stageP3ErrPostPrevEmptyM3Placed
  stageP3VerNeM3Env_of_parts
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  bind_sepWP_lscro_frame_zero_placed cloneGen_vregs_placed_ok p3_alloc_33b0_zero_placed_ok
  stageP3_err_tail_common_zero_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget (
  pqxdhLogClosurePlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget (
  VerNeS1Env overVerNe_1e04_to_1e78_cro_placed_at_gen
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux (
  VerNeTailEnv bind_sepWP_cro_frame_tail bind_sepWPp_nopanic_tail
  cond_eq_adds64_of_ne_neg1_tail_pl fitsAlloc17_of_fitsEnv freeOnlyEvs_dealloc_192_8
  verNeTailEnv_of_freeSuffix weaken_frame_tail
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  ChainClone3OkPlaced SenderChainClone3OkPlaced genP3Pre_placed genP3S5PostFrame_placed
  stageP3ErrPost_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_noAllocShim_budget_sat cliExternsPlaced_realloc_budget_sat
  cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_shim_budget_sat
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv dropSessionStructureLocal2Spec growOneSpeSpec setSessionStateSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropSpeSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  FromFEnv FromMEnv FromVPostTdEnv SegCloneEnv SegTailEnv segCloneEvents
)

local elab "erase_hkdf_arm64_norm" : command => Lean.Elab.Command.liftCoreM do
  for n in [``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase n `arm64_norm
erase_hkdf_arm64_norm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

local macro "wp_steps_sync_518 " ext:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $ext))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## 1. Stage P3 Block-`518` Callee Bundle & CLI Instantiation -/

structure StageP3CalleesM3Placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  shim : subroutine_ok (lsProg_518 ext)
    (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
    sessionShimBudgetSpec
  alloc : subroutine_ok (lsProg_518 ext)
    (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
    (rustCliAllocBudgetSpec M A lim false)
  dealloc : subroutine_ok (lsProg_518 ext)
    (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    (rustCliDeallocBudgetSpec M A lim)
  memcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec
  grow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
    (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim))
  setState : subroutine_ok (lsProg_518 ext) (lsmpl.base 48)
    (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim))
  dropSpe2 : subroutine_ok (lsProg_518 ext) (lsmpl.base 511)
    (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim)))
  dropSs3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
    (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim))
  logClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
    (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)
  panic : ext lsHandleErrorSym = some Rust.panicked
  chainClone : ChainClone3OkPlaced A lim ext
  senderChainClone : SenderChainClone3OkPlaced A lim ext

theorem StageP3CalleesM3Placed.of_cliExternsPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (hLogClosure : subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)) :
    StageP3CalleesM3Placed A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  shim := ls_hook_ok_ultra_of_mem
    ((show lsRustNoAllocShimSymCli =
        "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" by decide) ▸
      cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq)
    (by decide)
  alloc := ls_hook_ok_ultra_of_mem
    ((show lsRustAllocSymCli = "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    (by decide)
  dealloc := ls_hook_ok_ultra_of_mem
    ((show lsRustDeallocSymCli = "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
    (by decide)
  memcpy := ls_hook_ok_ultra_of_mem
    ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
      cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)
    (by decide)
  grow := grow_one_spe_placed_ok_at
    ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
      hookSat_noAllocShimBudget_of_withVmPreserved
        (cliExternsPlaced_noAllocShim_budget_sat mmpl gh W hG.shim_eq))
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show lsRustReallocSymCli = lsRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hG)
  setState := set_session_state_placed_ok_at
    ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
      cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
  dropSpe2 := drop_spe2_placed_ok_at_of_dealloc (cliGhostExterns gh (cliExternsPlaced mmpl W))
    (ls_hook_ok_ultra_of_mem
      ((show lsRustDeallocSymCli = "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" by decide) ▸
        cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
      (by decide))
  dropSs3 := drop_session_structure4_placed_ok_at
    (callerProg := lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
    (by decide)
  logClosure := hLogClosure
  panic := cliGhostExterns_panic_handle_error mmpl gh W
  chainClone := chainClone3_placed_ok_of_hooks
    ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
      cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
      cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)
  senderChainClone := senderChainClone3_placed_ok_of_hooks
    ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
      cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
      cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)

/-! ## 2. `sessionShimBudgetSpec` Version-Mismatch Block & `FromMEnv ↔ StageP3VerNeM3Env` -/

private def sessionShimNormSpec : Spec Unit where
  pre := fun _ _ => ⌜True⌝ ∗ emp
  post := fun _ s0 sf => ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗ emp

private theorem subroutine_ok_sessionShimNorm {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry sessionShimBudgetSpec) :
    subroutine_ok prog entry sessionShimNormSpec := by
  refine subroutine_ok.of_codeLoaded fun u R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [sessionShimNormSpec] at hpre
  rw [sepConj_assoc, emp_sepConj, satisfies_pure_sepConj] at hpre
  refine h.mono_outcome u R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · dsimp only [sessionShimBudgetSpec, sessionShimSpec]
    rw [emp_sepConj]; exact hpre.2
  · rcases hout with ⟨hret, hcs, hpost⟩ | hp | he | ho
    · left; refine ⟨hret, hcs, ?_⟩
      dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
      dsimp only [sessionShimNormSpec]
      rw [sepConj_assoc, emp_sepConj, satisfies_pure_sepConj]
      exact ⟨⟨hpost.1, hpost.2.1⟩, hpost.2.2⟩
    · right; left; exact hp
    · right; right; left; exact he
    · right; right; right; exact ho

private theorem verNeS1Env_elim {evs : List AllocEvent} (h : VerNeS1Env evs) :
    ∃ ef, FreeOnlyEvs ef ∧ evs = rustAllocEvents 192 8 ++ ef := by
  rcases h with rfl | ⟨_, ef, rfl, rfl, hf⟩
  · exact ⟨[], fun _ h => False.elim (List.not_mem_nil h), (List.append_nil _).symm⟩
  · exact ⟨ef, hf, rfl⟩

private theorem verNeTailEnv_elim {evs : List AllocEvent} (h : VerNeTailEnv evs) :
    ∃ ef, FreeOnlyEvs ef ∧ evs = rustAllocEvents 17 1 ++ ef := by
  rcases h with rfl | ⟨_, ef, rfl, rfl, hf⟩
  · exact ⟨[], fun _ h => False.elim (List.not_mem_nil h), (List.append_nil _).symm⟩
  · exact ⟨ef, hf, rfl⟩

theorem stageP3VerNeM3Env_imp_fromMEnv (evs : List AllocEvent)
    (h : StageP3VerNeM3Env evs) : FromMEnv evs := by
  have hg0 : GrowOneSpeEnv 0#64 (rustAllocEvents 192 8) := Or.inl ⟨rfl, rfl⟩
  rcases h with hs1 | ⟨_, _, rfl, hs1, htail⟩
  · obtain ⟨ef1, hf1, rfl⟩ := verNeS1Env_elim hs1
    exact Or.inr ⟨rustAllocEvents 192 8, ef1, rfl, hg0, Or.inl (Or.inl hf1)⟩
  · obtain ⟨ef1, hf1, rfl⟩ := verNeS1Env_elim hs1
    obtain ⟨ef2, hf2, rfl⟩ := verNeTailEnv_elim htail
    exact Or.inr ⟨rustAllocEvents 192 8, (ef1 ++ rustAllocEvents 17 1) ++ ef2,
      by simp only [List.append_assoc], hg0,
      Or.inr ⟨ef1 ++ rustAllocEvents 17 1, ef2, rfl,
        Or.inr ⟨ef1, rustAllocEvents 17 1, rfl, hf1, rfl⟩, hf2⟩⟩

theorem fitsEnv_stageP3VerNeM3Env_of_fromMEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st0 : M.σ} (h : FitsEnv M lim st0 FromMEnv) :
    FitsEnv M lim st0 StageP3VerNeM3Env :=
  fun evs hevs => h evs (stageP3VerNeM3Env_imp_fromMEnv evs hevs)

theorem sp3e0_cell_336_entails_344 (sp val : BitVec 64) :
    ((sp + 0x3e0#64) ↦₆₄ val) ∗ memRegion (sp + 0x3e8#64) 336 ⊢
      memRegion (sp + 0x3e0#64) 344 := by
  rw [show (344 : Nat) = 8 + 336 from rfl,
      memRegion_split (sp + 0x3e0#64) 8 336 (by decide),
      show sp + 0x3e0#64 + 8#64 = sp + 0x3e8#64 by bv_omega,
      ProofLib.memRegion_eight (sp + 0x3e0#64)]
  exact sepConj_mono_left (Entails.sepExists_intro val)

set_option maxHeartbeats 800000 in
theorem p3_err_ver_d_sessionShim_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      sessionShimBudgetSpec)
    (st : M.σ) (s : State) (coroPtr retPtr savedX27 ssCap u_3e0 : BitVec 64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (blkPl_518).base + 7800#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (dpClosureEntryVerPlaced + 0x33b0#64) s
      (((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗ ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = 17#64 ∧
        s1.readReg64 .x1 = 1#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧ s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim' := subroutine_ok_sessionShimNorm hshim
  dsimp only [sessionShimNormSpec] at hshim'
  have hcond_cap := cond_eq_adds64_of_ne_neg1_tail_pl hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [dpClosureEntryVerPlaced, lsLogFilterAddr] at hpc ⊢
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  wp_call hshim' ()
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_518 ext ((blkPl_518).base + 0x33b0#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

def StageP3VerNePrevEmptySessionShimPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)),
    subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec) →
    ext lsHandleErrorSym = some Rust.panicked →
    ∀ (st_b : M.σ) (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr : BitVec 64),
      FitsEnv M lim st_b FromMEnv →
      initErrsPtr ≠ 0#64 →
      ∀ (msgVer : BitVec 32) (b_2c0 : BitVec 8) (g : RecordGhost) (G₁ recG : SessionGhost)
        (st : SessionState (List (BitVec 8))),
        LibsignalCodeRoLoaded lsmpl s1.mem →
        s1.pc = dpClosureEntryM3Placed + 0x1e04#64 →
        s1.status = .Running →
        s1.sp = s.sp →
        (s.sp &&& 15#64 == 0#64) = true →
        s1.trace = s0.trace →
        s1.readReg64 .x9 = msgVer.setWidth 64 →
        s1.readReg64 .x19 = coroPtr →
        s1.readReg64 .x24 = s.sp + 0x370#64 →
        s1.readReg64 .x27 = ctxPtr →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
          (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
            ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            memRegion (s.sp + 0x3e0#64) 344 ∗
            sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
            sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
            prevSessionsEmptyAt A.repAlloc coroPtr g ∗
            ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
            lsLogOff ∗
            memRegion outPtr 48 ∗
            memRegion (s.sp + 0x250#64) 20 ∗
            memRegion (s.sp + 0x270#64) 48 ∗
            memRegion (s.sp + 0x370#64) 36 ∗
            memRegion (s.sp + 0x930#64) 48 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim st_b s1 ∗
            stackAt s.sp growOneSpeStack)
          (fun sf P_f =>
            ∃ evs_vn : List AllocEvent,
              FromMEnv evs_vn ∧
              (P_f ⊢
                ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
                ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
                ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                memRegion (s.sp + 0x3e0#64) 344 ∗
                stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_vn st_b) s0 s sf
                  coroPtr outPtr (.invalidMessage .preKey .decryptionFailed)) ∧
              sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
              LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
          (fun _ _ => False)

set_option maxHeartbeats 1200000 in
theorem stageP3_ver_ne_prevEmpty_sessionShim_placed_ok [LibsignalPlacement] :
    StageP3VerNePrevEmptySessionShimPlacedStmt := by
  intro M A lim ext hshim halloc hdealloc hGrow hDropSS3 hLogClosure _hpanic
    st0 s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hfits_fromM hinit_ne msgVer b_2c0
    g G₁ recG st hcro1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
  have hfits : FitsEnv M lim st0 StageP3VerNeM3Env := fitsEnv_stageP3VerNeM3Env_of_fromMEnv hfits_fromM
  intro R hm hL1
  have hwp : SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗ prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st0 s1 ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f => (∃ evs : List AllocEvent, StageP3VerNeM3Env evs ∧ (P_f ⊢
        ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
        ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs st0) s0 s sf coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed))) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (fun _ _ => False) := by
    have hlog_c : lsLogOff = pqLogLevelCellPlaced := rfl; refine weaken_frame_tail (Entails.of_eq hlog_c) (by sep_focus) ?_
    have hs1 := overVerNe_1e04_to_1e78_cro_placed_at_gen (M := M) (A := A) (lim := lim) (Qp := fun _ _ => False)
      ext hLogClosure hGrow hDropSS3 st0 (fitsS1_of_fitsM3 hfits)
      s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
      hcro1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine bind_sepWPp_nopanic_tail hs1 (by sep_focus)
      fun s6b P_m6b hpc6b hrun6b
        ⟨⟨errsPtr, evs1, hevs1, hP6b⟩, hsp6b_s, htr6b_0, hx19_6b, _, hvregs_6b, hcro6b, hL6b⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hP6b) ?_
    let st6b := M.stepEvents evs1 st0
    have hfits_tail : FitsEnv M lim st6b VerNeTailEnv := fitsTail_of_fitsM3 hfits hevs1
    refine weaken_frame_tail
      (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun bs336 => ?_
    refine weaken_frame_tail
      (T := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
        SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
      (T' := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
        SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
    have hlog_eq : pqLogLevelCellPlaced = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
    refine weaken_frame_tail (Entails.of_eq hlog_eq) (by sep_focus) ?_
    have hsp6b_align : (s6b.sp &&& 15#64 == 0#64) = true := by rw [hsp6b_s]; exact hsp_align
    have hprev_f0 : prevSessionsEmptyAt A.repAlloc coroPtr g =
        ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
        (((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
         vecBuf A.repAlloc 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr []) := by
      unfold prevSessionsEmptyAt vecAt vecHeader; dsimp only [List.length_nil]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl
    refine weaken_frame_tail (Entails.of_eq hprev_f0) (by sep_focus) ?_
    simp only [sepConj_assoc]
    have hstep7 := p3_err_ver_d_sessionShim_placed_wp A lim ext hshim st6b s6b coroPtr outPtr ctxPtr
      recG.localIk.cap 0x8000000000000006#64 (cap_ne_noneCap_of_lt hcap_lt)
      hpc6b hrun6b hsp6b_align hx19_6b
    rw [hsp6b_s] at hstep7
    refine bind_sepWP_cro_frame_tail hcro6b hL6b hstep7 (by sep_focus)
      fun s7 hpc7 hrun7 hcro7 hL7 hregs7 => ?_
    rcases hregs7 with ⟨hsp7_6b, htr7_6b, hx0_7, hx1_7, hx19_7, hx24_7, hx25_7, hx26_7, _, _, hvregs_7⟩
    refine weaken_frame_tail (Entails.of_eq hprev_f0.symm) (by sep_focus) ?_
    refine weaken_frame_tail (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
    have hpack_ss :
        ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
          sessionHeap A.repAlloc recG st ⊢
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st hinl
    refine weaken_frame_tail hpack_ss (by sep_focus) ?_
    refine weaken_frame_tail (sp3e0_cell_336_entails_344 s.sp 0xffffffffffffffff#64)
      (by sep_focus) ?_
    have htail := stageP3_err_ver_tail_prevEmpty_placed_ok (M := M) (A := A) (lim := lim)
      (Qp := fun _ _ => False) ext halloc hdealloc hDropSS3 st6b hfits_tail
      s0 s s7 coroPtr outPtr errsPtr msgVer b_2c0 g recG st
      hcro7 hL7 hpc7 hrun7 hsp7_6b hsp_align (htr7_6b.trans htr6b_0)
      hx0_7 hx1_7 hx19_7 hx24_7 hx25_7 hx26_7
    refine bind_sepWPp_nopanic_tail htail (by sep_focus)
      fun sf P_mf hpcf hrunf ⟨⟨evs2, hevs2, hP_t⟩, hspf, htrf, hcc, hcrof, hLf, hvregs_f⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hP_t) ?_
    have hpool_eq :
        A.pool lim (M.stepEvents evs2 st6b) sf =
          A.pool lim (M.stepEvents (evs1 ++ evs2) st0) sf := by
      dsimp only [st6b]
      rw [← M.stepEvents_append]
    refine SepWPp.done hpcf hrunf ?_
    refine ⟨⟨evs1 ++ evs2, stageP3VerNeM3Env_of_parts hevs1 hevs2, ?_⟩,
      hspf, htrf, hcc, hcrof, hLf, by rw [hvregs_f, hvregs_7, hvregs_6b]⟩
    unfold stageP3ErrPostPrevEmptyM3Placed
    dsimp only [LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlacedBudget.stageP3ErrPostPrevEmptyPlaced,
      SessionState.recordError]
    rw [← hpool_eq]
    have hexists_errs :
        ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ⊢
          ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
            ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗
            ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 4#64
        (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64 (Entails.refl _)))
    exact entails_replace_sub hexists_errs (by sep_focus) (eq_of_sep_emp (by sep_focus))
  rcases hwp R hm hL1 with ⟨sf, hsteps,
    ⟨hpcf, hrunf, P_f, hmf, ⟨evs, hevs, hPf⟩, hspf, htrf, hcc, hcrof, _, hvregs_f⟩ | hpan | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf,
      evs, stageP3VerNeM3Env_imp_fromMEnv evs hevs, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## 3. Zero-Cap (`prevCap = 0`) Stage P3 Error Paths (`FromVPostTdEnv`) -/

theorem bind_sepWPp_frame_false {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_stage F : SepProp} {Q_stage Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage Q_stage (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm P_m, sm.pc = mid → sm.status = .Running → Q_stage sm P_m →
      SepWPp prog ret sm (P_m ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.congr_pre (by rw [sepConj_emp])
    (bind_sepWPp_false_steps_framed (F_frame := emp) hstage hP fun sm P_m _ hpcm hrunm hqm =>
      SepWPp.congr_pre (by rw [sepConj_emp]) (hnext sm P_m hpcm hrunm hqm))

set_option maxHeartbeats 1200000 in
private theorem stageP3_err_tail_dup_zero_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State)
    (coroPtr outPtr errsPtr prevStatesPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
       ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st_b s ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
            ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
            ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
            memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  refine sepWPp_weaken_frame (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG recSt) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]; refine SepWPp.exists_elim fun bs336 => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine sepWPp_weaken_frame (Entails.of_eq hrepack278) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun u_250 => ?_
  refine sepWPp_weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  refine sepWPp_weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_)
  have hstep1 := p3_err_tail_dup_a_placed_wp A lim st_b ext s coroPtr errsPtr recG.localIk.cap
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32) (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    w3 w4 u_250 u_258 u_370 u_378 u_384 u_38c (w0.extractLsb' 0 32) (w2.extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc hrun hsp_align hx19 hx24 hx25 hx28
  refine bind_sepWP_lscro_frame_err hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hx30_1, hvregs_1⟩
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A.repAlloc recG recSt ⊢ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG recSt hinl
  have hfold250 : ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64) (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32) (w2.extractLsb' 32 32)
  refine sepWPp_weaken_frame hpack_ss (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus)
      (sepWPp_weaken_frame (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000017#64 w0 w1 w2 w3 w4) (by sep_focus)
        (sepWPp_weaken_frame hfold250 (by sep_focus) ?_)))
  have hcommon := stageP3_err_tail_common_zero_placed_ok (Qp := fun _ _ => False) ext hDropSS3 st_b
    s0 s1 coroPtr outPtr 0x8000000000000017#64 prevStatesPtr w0 w1 w2 w3 w4 b_2c0 recG recSt
    hcro1 hpc1 hrun1 (by rw [hsp1_s]; exact hsp_align) (htr1_s.trans htr) hx0_1 hx19_1 hx22_1
    (by rw [hx25_1, hsp1_s]) (hx26_1.trans hx26) hx28_1 hx30_1
  rw [hsp1_s] at hcommon
  refine ret_sepWPp_frame_false hcommon (by sep_focus)
    fun sf _ _ _ ⟨evs, hevs_free, hP_c, hspf, htrf, hcc, hcrof, hvregs_f⟩ =>
      ⟨evs, hevs_free,
       Entails.trans (entails_replace_sub hP_c (by sep_focus) rfl)
         (Entails.of_eq (eq_of_sep_emp (by sep_focus))),
       hspf, htrf, hcc, hcrof, hvregs_f.trans hvregs_1⟩

set_option maxHeartbeats 1200000 in
private theorem stageP3_sub5_err_dup_zero_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr : BitVec 64)
    (ratVer counter : BitVec 32) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A.repAlloc (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st_b s ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
            ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
            ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            recordResultAt A.repAlloc outPtr (.error (.duplicatedMessage ratVer counter)) ∗
            memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  have hdecomp : vecResultAt A.repAlloc (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64, words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
          speAt A.repAlloc (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗ ((s.sp + 0x280#64) ↦₆₄ w1) ∗
        ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A.repAlloc (utf8 "decrypt") (s.sp + 0x270#64) (.duplicatedMessage ratVer counter) (by nofun)
    dsimp only [vecResultAt, speTag, speWord] at h1 ⊢; refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
  refine sepWPp_weaken_frame hdecomp (by sep_focus) ?_; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H =>
    sepWPp_weaken_frame
      (P₁ := ⌜∀ c : BitVec 64, words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A.repAlloc (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
      (P₂ := ⌜∀ c : BitVec 64, words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A.repAlloc (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
      (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hreassemble => ?_)
  have hstep1 := p3_err_dup_placed_wp A lim st_b ext s coroPtr outPtr hpc hrun hsp_align hx19 hx24
  refine bind_sepWP_lscro_frame_err hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1, hvregs_1⟩
  refine call_lscl_nopanic_err
    (x := ((⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost), st_b))
    (T := sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool lim st_b s1 ∗
          stackAt s.sp dropSessionStructure2Stack)
    hcro1 hDropSS3 hpc1 hrun1 (by simpa only [State.spAligned, hsp1_s] using hsp_align) hx30_1
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1_s])
    (And.intro hx0_1 (show LsRetAddr624 (s1.readReg64 .lr) by
      change LsRetAddr624 (s1.readReg64 .x30)
      rw [hx30_1]
      exact lsRetAddr624_blockPlacement_base_add 518 0x34dc#64 (by decide) (by decide)))
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1_s]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs1 => ?_
  refine sepWPp_weaken_frame
    (P₁ := ⌜s2.trace = s1.trace ∧ FreeOnlyEvs evs1⌝)
    (P₂ := ⌜s2.trace = s1.trace ∧ FreeOnlyEvs evs1⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨htr2_1, hevs1⟩ => ?_)
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have htail := stageP3_err_tail_dup_zero_placed_ok ext hDropSS3 (M.stepEvents evs1 st_b)
    s0 s2 coroPtr outPtr errsPtr prevStatesPtr w0 w1 w2 w3 w4 b_2c0 recG recSt
    hcro2 hpc2 hrun2 (by rw [hsp2_s]; exact hsp_align) (htr2_1.trans (htr1_s.trans htr))
    (hx19_cs2.trans hx19_1) (by rw [hx24_cs2, hx24_1, hsp2_s]) (by rw [hx25_cs2, hx25_1, hsp2_s])
    (hx26_cs2.trans hx26_1) (hx28_cs2.trans hx28_1)
  rw [hsp2_s] at htail
  refine ret_sepWPp_frame_false htail (by sep_focus)
    fun sf _ _ _ ⟨evs2, hevs2, hP_t, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  rw [← M.stepEvents_append] at hP_t
  dsimp only [recordResultAt, vecResultAt]
  refine ⟨evs1 ++ evs2, freeOnlyEvs_append hevs1 hevs2, ?_, hspf, htrf, hcc, hcrof,
    by rw [hvregs_f, hvregs_cs2, hvregs_1]⟩
  refine Entails.trans (entails_replace_sub hP_t (by sep_focus) rfl) ?_
  exact entails_replace_sub (hreassemble outPtr) (by sep_focus) (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
private theorem stageP3_err_tail_nondup_dec_zero_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSpe2 : subroutine_ok (lsProg_518 ext) (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim))))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State)
    (coroPtr outPtr errsPtr prevStatesPtr w0 w1 w2 w3 w4 : BitVec 64)
    (e : SignalProtocolError) (_ : e ≠ .panic) (b_2c0 : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = dpClosureEntryM3Placed + 0x34dc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       A.live errsPtr 192 8 ∗ speAt A.repAlloc (utf8 "decrypt") errsPtr e ∗ memRegion (errsPtr + 0x30#64) 144 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
       ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st_b s ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
            ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
            ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            words6At outPtr 0x8000000000000018#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
            memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  refine sepWPp_weaken_frame (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG recSt) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]; refine SepWPp.exists_elim fun bs336 => ?_
  refine sepWPp_weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_)
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine sepWPp_weaken_frame (Entails.of_eq hrepack278) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun u_250 =>
    sepWPp_weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 => SepWPp.exists_elim fun u_380 =>
    SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  have hstep1 := p3_err_tail_nondup_a1_placed_wp A lim st_b ext s coroPtr errsPtr hpc hrun hsp_align hx19
  refine bind_sepWP_lscro_frame_err hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1, hvregs_1⟩
  have hstack_drop : stackAt s.sp dropSessionStructure2Stack = memRegion (s.sp - 4192#64) 64 ∗ stackAt s.sp dropSpeStack :=
    stackAt_split_bottom s.sp dropSpeStack 64 (by decide)
  refine sepWPp_weaken_frame (Entails.of_eq hstack_drop) (by sep_focus) ?_
  refine call_lscl_ro_nopanic_err (spec := dropSpeSpec M A lim)
    (x := ((⟨errsPtr, utf8 "decrypt", e⟩ : DropSpeGhost), st_b))
    (T := speAt A.repAlloc (utf8 "decrypt") errsPtr e ∗ A.pool lim st_b s1 ∗ stackAt s.sp dropSpeStack)
    hcro1 hDropSpe2 hpc1 hrun1 (by simpa only [State.spAligned, hsp1_s] using hsp_align) hx30_1
    (by dsimp only [dropSpeSpec]; rw [hsp1_s])
    (And.intro hx0_1 (show LsRetAddr624 (s1.readReg64 .x30) by
      rw [hx30_1]
      exact lsRetAddr624_blockPlacement_base_add 518 0x34f4#64 (by decide) (by decide)))
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSpeSpec]; rw [hsp1_s]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_spe => ?_
  refine sepWPp_weaken_frame (P₁ := ⌜s2.trace = s1.trace⌝) (P₂ := ⌜s2.trace = s1.trace⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun htr2_1 => ?_)
  refine sepWPp_weaken_frame (P₁ := ⌜FreeOnlyEvs evs_spe⌝) (P₂ := ⌜FreeOnlyEvs evs_spe⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hevs_spe => ?_)
  have hjoin192 : memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 ⊢ memRegion errsPtr 192 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144) (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hstack_alloc : stackAt s.sp dropSpeStack = memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 32 (by decide)
  refine sepWPp_weaken_frame hjoin192 (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_)
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hstep3 := p3_err_tail_nondup_a2_placed_wp ext hdealloc (M.stepEvents evs_spe st_b) s2 coroPtr errsPtr recG.localIk.cap
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32) (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    w3 w4 u_250 u_258 u_370 u_378 u_384 u_38c (w0.extractLsb' 0 32) (w2.extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc2 hrun2 (by rw [hsp2_s]; exact hsp_align)
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1) (hx23_cs2.trans hx23_1)
    (by rw [hx24_cs2, hx24_1, hx24, hsp2_s]) (by rw [hx25_cs2, hx25_1, hx25, hsp2_s])
    (hx28_cs2.trans (hx28_1.trans hx28))
  rw [hsp2_s] at hstep3
  refine bind_sepWP_lscro_frame_err hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx22_3, _, hx25_3, hx26_3, _, hx28_3, _, hx30_3, hvregs_3⟩
  have hstack_restore : memRegion (s.sp - 4192#64) 64 ∗ memRegion (s.sp - 4128#64) 32 ∗
      stackAt s.sp allocHookStack ⊢ stackAt s.sp dropSessionStructure2Stack := by
    rw [hstack_drop, hstack_alloc]; exact Entails.refl _
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A.repAlloc recG recSt ⊢ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG recSt hinl
  have hfold250 : ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion20_fold (s.sp + 0x250#64)
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32) (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32) (w2.extractLsb' 32 32)
  refine sepWPp_weaken_frame hstack_restore (by sep_focus)
    (sepWPp_weaken_frame hpack_ss (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus)
        (sepWPp_weaken_frame (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000018#64 w0 w1 w2 w3 w4) (by sep_focus)
          (sepWPp_weaken_frame hfold250 (by sep_focus) ?_))))
  have hcommon := stageP3_err_tail_common_zero_placed_ok (Qp := fun _ _ => False) ext hDropSS3
    (M.stepEvents (rustDeallocEvents 192 8) (M.stepEvents evs_spe st_b))
    s0 s3 coroPtr outPtr 0x8000000000000018#64 prevStatesPtr w0 w1 w2 w3 w4 b_2c0 recG recSt
    hcro3 hpc3 hrun3 (by rw [hsp3_2]; exact hsp_align) (htr3_2.trans (htr2_1.trans (htr1_s.trans htr)))
    hx0_3 hx19_3 hx22_3 (by rw [hx25_3, hsp3_2]) (hx26_3.trans (hx26_cs2.trans (hx26_1.trans hx26))) hx28_3 hx30_3
  rw [hsp3_2] at hcommon
  refine ret_sepWPp_frame_false hcommon (by sep_focus)
    fun sf _ _ _ ⟨evs_c, hevs_c, hP_c, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hst_eq :
      M.stepEvents evs_c (M.stepEvents (rustDeallocEvents 192 8) (M.stepEvents evs_spe st_b)) =
        M.stepEvents (evs_spe ++ (rustDeallocEvents 192 8 ++ evs_c)) st_b := by
    simp only [← M.stepEvents_append, List.append_assoc]
  rw [hst_eq] at hP_c
  refine ⟨evs_spe ++ (rustDeallocEvents 192 8 ++ evs_c),
    freeOnlyEvs_append hevs_spe (freeOnlyEvs_append (freeOnlyEvs_dealloc 192 8) hevs_c),
    Entails.trans (entails_replace_sub hP_c (by sep_focus) rfl)
      (Entails.of_eq (eq_of_sep_emp (by sep_focus))),
    hspf, htrf, hcc, hcrof, by rw [hvregs_f, hvregs_3, hvregs_cs2, hvregs_1]⟩

def stageP3ErrPreZeroPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s s_pool : State)
    (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64) (e : SignalProtocolError) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ vecResultAt A.repAlloc (s.sp + 0x270#64) (.error e) ∗
  sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
  ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
  ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st_b s_pool ∗
  stackAt s.sp growOneSpeStack

set_option maxHeartbeats 1200000 in
private theorem stageP3_sub5_err_nondup_zero_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3Placed A lim ext)
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hfits : FitsEnv M lim st_b FromVPostTdEnv)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPreZeroPlaced A lim st_b s0 s s coroPtr outPtr initErrsPtr prevStatesPtr e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        ∃ evs_err : List AllocEvent,
          FromVPostTdEnv evs_err ∧
          (P_f ⊢ stageP3ErrPost_placed A lim (M.stepEvents evs_err st_b) s0 s sf coroPtr outPtr prevStatesPtr e) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  unfold stageP3ErrPreZeroPlaced
  have hrec_err : SessionState.recordError .preKey e = .invalidMessage .preKey .decryptionFailed :=
    recordError_preKey_of_speTag_ne_speWord23 he_npan htag_ne23
  refine intro_lsro_decryptionFailed_err hcro ?_
  have hdecomp : vecResultAt A.repAlloc (s.sp + 0x270#64) (.error e) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A.repAlloc (utf8 "decrypt") c e⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ speTag e) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
        ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
        ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A.repAlloc (utf8 "decrypt") (s.sp + 0x270#64) e he_npan
    dsimp only [vecResultAt] at h1 ⊢; refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
      (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
  refine sepWPp_weaken_frame hdecomp (by sep_focus) ?_; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine sepWPp_weaken_frame
    (P₁ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A.repAlloc (utf8 "decrypt") c e⌝)
    (P₂ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A.repAlloc (utf8 "decrypt") c e⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hreassemble => ?_)
  refine sepWPp_weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x930#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u930 => SepWPp.exists_elim fun u938 => SepWPp.exists_elim fun u940 =>
    SepWPp.exists_elim fun u948 => SepWPp.exists_elim fun u950 => SepWPp.exists_elim fun u958 => ?_
  have hstep1 := p3_err_nondup_a_placed_wp A lim st_b ext s coroPtr outPtr (speTag e)
    w0 w1 w2 w3 w4 u930 u938 u940 u948 u950 u958
    (speTag_ne_ok_of_ne_panic he_npan) htag_ne23 hpc hrun hsp_align hx19 hx24
  refine bind_sepWP_lscro_frame_err hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, _, _, _, _, hx19_1, hx24_1, hx25_1, hx26_1, _, _, _, hx30_1, hvregs_1⟩
  refine sepWPp_weaken_frame (words6_entails_memRegion48 (s.sp + 0x930#64) (speTag e) w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hstack_log := stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine sepWPp_weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_lscl_nopanic_err (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := lsLogOff ∗ stackAt s.sp pqxdhClosureStack)
    hcro1 hC.logClosure hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s]; rfl) trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr2_1, hvm2_1⟩ => ?_
  have hpool12 : A.pool lim st_b s1 = A.pool lim st_b s2 := (A.pool_of_vmPreserved hvm2_1).symm
  refine sepWPp_weaken_frame (Entails.of_eq hpool12) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq hstack_log.symm) (by sep_focus) ?_)
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, _, _, hvregs_cs2⟩
  have hstep3 := p3_err_nondup_b_placed_wp A lim st_b ext s2 coroPtr hpc2 hrun2
    (by rw [hsp2_s]; exact hsp_align) (hx19_cs2.trans hx19_1)
  rw [hsp2_s] at hstep3
  refine bind_sepWP_lscro_frame_err hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx25_3, hx26_3, _, _, _, hx30_3, hvregs_3⟩
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_2] using hsp_align
  have htr3_0 : s3.trace = s0.trace := htr3_2.trans (htr2_1.trans (htr1_s.trans htr))
  have hfits_grow := fitsEnv_growOneSpe_of_fromVPostTd hfits
  refine call_lscl_nopanic_err
    (spec := growOneSpeSpec M A lim)
    (x := ((s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))), st_b))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool lim st_b s3 ∗ stackAt s.sp growOneSpeStack)
    hcro3 hC.grow hpc3 hrun3 hsp3_al hx30_3
    (by
      rw [growOneSpe_pre_zero_eq M A lim st_b s3 (s.sp + 0x3c8#64) initErrsPtr hx0_3 hinit_ne hfits_grow,
        hsp3_2, pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus) (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  rw [growOneSpe_post_zero_eq M A lim st_b s3 s4 (s.sp + 0x3c8#64) initErrsPtr, hsp3_2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine sepWPp_weaken_frame (P₁ := ⌜s4.trace = s3.trace⌝) (P₂ := ⌜s4.trace = s3.trace⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun htr4_3 => ?_)
  refine sepWPp_weaken_frame
    (P₁ := ⌜errsPtr ≠ 0 ∧ errsPtr.toNat % 8 = 0⌝)
    (P₂ := ⌜errsPtr ≠ 0 ∧ errsPtr.toNat % 8 = 0⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ => ?_)
  have hsplit192 : memRegion errsPtr 192 = memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144) (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
  refine sepWPp_weaken_frame (Entails.of_eq hsplit192) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq (memRegion48_words6_split_eq errsPtr)) (by sep_focus) ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 => SepWPp.exists_elim fun e2 =>
    SepWPp.exists_elim fun e3 => SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  have hlog_eq : pqLogLevelCellPlaced = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine sepWPp_weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp4_s : s4.sp = s.sp := hsp4_3.trans hsp3_2
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, hvregs_cs4⟩
  have hstep5 := p3_err_nondup_c_placed_wp A lim (M.stepEvents (rustAllocEvents 192 8) st_b)
    ext hC.shim s4 coroPtr errsPtr (speTag e) w0 w1 w2 w3 w4 e0 e1 e2 e3 e4 e5
    hpc4 hrun4 (by rw [hsp4_s]; exact hsp_align) (hx19_cs4.trans hx19_3) (hx21_cs4.trans hx21_3)
    (by rw [hx25_cs4, hx25_3, hx25_cs2, hx25_1, hsp4_s])
  rw [hsp4_s] at hstep5
  refine bind_sepWP_lscro_frame_err hcro4 hstep5 (by sep_focus) fun s5 hpc5 hrun5 hcro5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hx0_5, hx1_5, hx19_5, hx24_5, hx25_5, hx26_5, _, _, _, hvregs_5⟩
  have htr5_0 : s5.trace = s0.trace := htr5_4.trans (htr4_3.trans htr3_0)
  have hreasm_errs : ((errsPtr + 0x0#64) ↦₆₄ speTag e) ∗ ((errsPtr + 0x8#64) ↦₆₄ w0) ∗
      ((errsPtr + 0x10#64) ↦₆₄ w1) ∗ ((errsPtr + 0x18#64) ↦₆₄ w2) ∗
      ((errsPtr + 0x20#64) ↦₆₄ w3) ∗ ((errsPtr + 0x28#64) ↦₆₄ w4) ∗ H ⊢
      speAt A.repAlloc (utf8 "decrypt") errsPtr e := by
    simpa only [words6At, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hreassemble errsPtr
  have hstack_alloc := stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  have hlog_eq2 : (lsLogFilterAddr ↦₆₄ 0#64) = lsLogOff := rfl
  refine sepWPp_weaken_frame (Entails.of_eq hlog_eq2) (by sep_focus)
    (sepWPp_weaken_frame hreasm_errs (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_))
  have hfits17 := fitsEvents_alloc17_of_fromVPostTd hfits
  have halloc17 := p3_alloc_2eac_placed_ok (A := A) (lim := lim) ext hC.alloc
    (M.stepEvents (rustAllocEvents 192 8) st_b) s5
    emp hfits17 hcro5 hpc5 hrun5 (by rw [hsp5_4]; exact hsp_align) hx0_5 hx1_5
  rw [sepConj_emp, hsp5_4] at halloc17
  refine bind_sepWPp_frame_false halloc17 (by sep_focus)
    fun s6 P_m6 hpc6 hrun6 ⟨hP6, hdf_ne, hsp6_5, htr6_5, hcs6, hcro6⟩ => ?_
  rw [sepConj_emp] at hP6
  refine sepWPp_weaken_frame hP6 (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq (memRegion17_split_eq (s6.readReg64 .x0))) (by sep_focus) ?_))
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun df_10 => SepWPp.exists_elim fun df_8 => SepWPp.exists_elim fun df_0 => ?_
  refine sepWPp_weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  rcases hcs6 with ⟨hx19_cs6, _, _, _, _, hx24_cs6, hx25_cs6, hx26_cs6, _, _, _, hvregs_cs6⟩
  have hstep7 := p3_err_nondup_d_placed_wp A lim
    (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b))
    ext s6 coroPtr (s6.readReg64 .x0)
    0x6974707972636564#64 0x656c696166206e6f#64 df_0 df_8 (speTag e) w0 w1 w2 df_10 (w3.extractLsb' 0 8)
    hdf_ne hpc6 hrun6 (by rw [hsp6_5]; exact hsp_align) rfl (hx19_cs6.trans hx19_5)
  rw [hsp6_5] at hstep7
  refine bind_sepWP_lscro_frame_err hcro6 hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx19_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7, hvregs_7⟩
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp.drop_frame
    (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  have hstack_drop2 := stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine sepWPp_weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s6.readReg64 .x0))) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_))
  refine call_lscl_nopanic_err
    (x := ((⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost),
           M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b)))
    (T := sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗
          A.pool lim (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b)) s7 ∗
          stackAt s.sp dropSessionStructure2Stack)
    hcro7 hC.dropSs3 hpc7 hrun7 (by simpa only [State.spAligned, hsp7_6] using hsp_align) hx30_7
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_6])
    (And.intro hx0_7 (show LsRetAddr624 (s7.readReg64 .lr) by
      change LsRetAddr624 (s7.readReg64 .x30)
      rw [hx30_7]
      exact lsRetAddr624_blockPlacement_base_add 518 0x34dc#64 (by decide) (by decide)))
    (by sep_focus)
    (hnext := fun s8 hpc8 hrun8 hsp8_7 _ hcs8 hcro8 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_6]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_drop1 => ?_
  refine sepWPp_weaken_frame
    (P₁ := ⌜s8.trace = s7.trace ∧ FreeOnlyEvs evs_drop1⌝)
    (P₂ := ⌜s8.trace = s7.trace ∧ FreeOnlyEvs evs_drop1⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨htr8_7, hevs_drop1⟩ => ?_)
  have hsp8_s : s8.sp = s.sp := hsp8_7.trans hsp7_6
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, hx28_cs8, _, hvregs_cs8⟩
  have htail := stageP3_err_tail_nondup_dec_zero_placed_ok ext hC.dealloc hC.dropSpe2 hC.dropSs3
    (M.stepEvents evs_drop1 (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b)))
    s0 s8 coroPtr outPtr errsPtr prevStatesPtr 17#64 (s6.readReg64 .x0) 17#64 w3' w4 e he_npan b_2c0 recG recSt
    hcro8 hpc8 hrun8 (by rw [hsp8_s]; exact hsp_align) (htr8_7.trans (htr7_6.trans (htr6_5.trans htr5_0)))
    (hx19_cs8.trans hx19_7)
    (by rw [hx24_cs8, hx24_7, hx24_cs6, hx24_5, hx24_cs4, hx24_3, hx24_cs2, hx24_1, hsp8_s])
    (by rw [hx25_cs8, hx25_7, hx25_cs6, hx25_5, hsp8_s])
    (hx26_cs8.trans (hx26_7.trans (hx26_cs6.trans (hx26_5.trans (hx26_cs4.trans (hx26_3.trans (hx26_cs2.trans hx26_1)))))))
    (hx28_cs8.trans hx28_7)
  rw [hsp8_s] at htail
  refine ret_sepWPp_frame_false htail (by sep_focus)
    fun sf _ _ _ ⟨evs_tail, hevs_tail, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A.repAlloc
    outPtr (s6.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  rw [RustCliAllocBudget.repAlloc_live] at hrec
  have hst_eq :
      M.stepEvents evs_tail
        (M.stepEvents evs_drop1
          (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b))) =
      M.stepEvents (rustAllocEvents 192 8 ++ (rustAllocEvents 17 1 ++ (evs_drop1 ++ evs_tail))) st_b := by
    simp only [← M.stepEvents_append, List.append_assoc]
  rw [hst_eq] at hPf
  refine ⟨rustAllocEvents 192 8 ++ (rustAllocEvents 17 1 ++ (evs_drop1 ++ evs_tail)),
    fromVPostTdEnv_of_nondup hevs_drop1 hevs_tail, ?_, hspf, htrf, hcc, hcrof,
    by rw [hvregs_f, hvregs_cs8, hvregs_7, hvregs_cs6, hvregs_5, hvregs_cs4, hvregs_3, hvregs_cs2, hvregs_1]⟩
  unfold stageP3ErrPost_placed CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPost_placed
  rw [hrec_err]
  have hrr : ∀ st_e, recordResultAt (A.atState lim st_e sf) outPtr (.error (.invalidMessage .preKey .decryptionFailed)) =
      recordResultAt A.repAlloc outPtr (.error (.invalidMessage .preKey .decryptionFailed)) := fun _ => rfl
  have hpl : ∀ st_e, (A.atState lim st_e sf).pool = A.pool lim st_e sf := fun _ => rfl
  rw [hrr, hpl]
  have herrs : ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ⊢
      ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
        ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗
        ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
    Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr
      (Entails.sepExists_right 1#64 (Entails.refl _)))
  refine Entails.trans (entails_replace_sub hPf (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub herrs (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hrec (by sep_focus) rfl) ?_
  exact entails_replace_sub (Entails.of_eq hstack_drop2.symm) (by sep_focus) (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_zero_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3Placed A lim ext)
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hfits : FitsEnv M lim st_b FromVPostTdEnv)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPreZeroPlaced A lim st_b s0 s s coroPtr outPtr initErrsPtr prevStatesPtr e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        ∃ evs_err : List AllocEvent,
          FromVPostTdEnv evs_err ∧
          (P_f ⊢ stageP3ErrPost_placed A lim (M.stepEvents evs_err st_b) s0 s sf coroPtr outPtr prevStatesPtr e) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  by_cases htag23 : speTag e = speWord 23
  · obtain ⟨ratVer, counter, rfl⟩ := speTag_eq_speWord23_iff.mp htag23
    unfold stageP3ErrPreZeroPlaced
    have hstack_drop2 : stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
      stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
    rw [hstack_drop2]
    have hdup := stageP3_sub5_err_dup_zero_placed_ok ext hC.dropSs3 st_b
      s0 s coroPtr outPtr initErrsPtr prevStatesPtr ratVer counter b_2c0 G₂ recG st₂ recSt
      hcro hpc hrun hsp_align htr hx19 hx24
    refine ret_sepWPp_frame_false hdup (by sep_focus)
      fun sf _ _ _ ⟨evs_dup, hevs_dup, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
    have herrs : ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ⊢
        ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗ ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 0#64 (Entails.sepExists_right initErrsPtr (Entails.sepExists_right 0#64 (Entails.refl _)))
    refine ⟨evs_dup, Or.inl hevs_dup, ?_, hspf, htrf, hcc, hcrof, hvregs_f⟩
    unfold stageP3ErrPost_placed CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPost_placed
    have hrr : recordResultAt (A.atState lim (M.stepEvents evs_dup st_b) sf) outPtr (.error (.duplicatedMessage ratVer counter)) = recordResultAt A.repAlloc outPtr (.error (.duplicatedMessage ratVer counter)) := rfl
    have hpl : (A.atState lim (M.stepEvents evs_dup st_b) sf).pool = A.pool lim (M.stepEvents evs_dup st_b) sf := rfl
    dsimp only [SessionState.recordError]; rw [hrr, hpl]
    refine Entails.trans (entails_replace_sub hPf (by sep_focus) rfl) ?_
    refine Entails.trans (entails_replace_sub herrs (by sep_focus) rfl) ?_
    exact entails_replace_sub (Entails.of_eq hstack_drop2.symm) (by sep_focus) (eq_of_sep_emp (by sep_focus))
  · exact stageP3_sub5_err_nondup_zero_placed_ok ext hC st_b s0 s coroPtr outPtr initErrsPtr prevStatesPtr
      hfits hinit_ne e he_npan htag23 b_2c0 G₂ recG st₂ recSt hcro hpc hrun hsp_align htr hx19 hx24

/-! ## 4. `LibsignalFullPlacement` / `LibsignalFrozen` Variants (Block `519` Discharged Internally) -/

section FrozenVariants

open CryptoVerification (
  LibsignalCodeLoaded LibsignalFrozen LibsignalFullPlacement
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget (
  bind_sepWP_fr_frame_budget call_raw_nopanic_fr_budget pqxdh_log_closure_frozen_placed_ok_of_block
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget (
  overVerNe_1e04_to_1e78_frozen_placed_at_gen
)

structure StageP3CalleesM3BasePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  shim : subroutine_ok (lsProg_518 ext)
    (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
    sessionShimBudgetSpec
  alloc : subroutine_ok (lsProg_518 ext)
    (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
    (rustCliAllocBudgetSpec M A lim false)
  dealloc : subroutine_ok (lsProg_518 ext)
    (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    (rustCliDeallocBudgetSpec M A lim)
  memcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec
  grow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
    (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim))
  setState : subroutine_ok (lsProg_518 ext) (lsmpl.base 48)
    (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim))
  dropSpe2 : subroutine_ok (lsProg_518 ext) (lsmpl.base 511)
    (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim)))
  dropSs3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
    (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim))
  panic : ext lsHandleErrorSym = some Rust.panicked
  chainClone : ChainClone3OkPlaced A lim ext
  senderChainClone : SenderChainClone3OkPlaced A lim ext

theorem StageP3CalleesM3BasePlaced.of_cliExternsPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    StageP3CalleesM3BasePlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  shim := ls_hook_ok_ultra_of_mem
    ((show lsRustNoAllocShimSymCli =
        "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" by decide) ▸
      cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq)
    (by decide)
  alloc := ls_hook_ok_ultra_of_mem
    ((show lsRustAllocSymCli = "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    (by decide)
  dealloc := ls_hook_ok_ultra_of_mem
    ((show lsRustDeallocSymCli = "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
    (by decide)
  memcpy := ls_hook_ok_ultra_of_mem
    ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
      cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)
    (by decide)
  grow := grow_one_spe_placed_ok_at
    ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
      hookSat_noAllocShimBudget_of_withVmPreserved
        (cliExternsPlaced_noAllocShim_budget_sat mmpl gh W hG.shim_eq))
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show lsRustReallocSymCli = lsRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hG)
  setState := set_session_state_placed_ok_at
    ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
      cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
  dropSpe2 := drop_spe2_placed_ok_at_of_dealloc (cliGhostExterns gh (cliExternsPlaced mmpl W))
    (ls_hook_ok_ultra_of_mem
      ((show lsRustDeallocSymCli = "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" by decide) ▸
        cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
      (by decide))
  dropSs3 := drop_session_structure4_placed_ok_at
    (callerProg := lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
    (by decide)
  panic := cliGhostExterns_panic_handle_error mmpl gh W
  chainClone := chainClone3_placed_ok_of_hooks
    ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
      cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
      cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)
  senderChainClone := senderChainClone3_placed_ok_of_hooks
    ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
      cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
      cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)

def StageP3VerNePrevEmptySessionShimFrozenPlacedStmt [LibsignalFullPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)),
    subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ext lsHandleErrorSym = some Rust.panicked →
    ∀ (st_b : M.σ) (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr : BitVec 64),
      FitsEnv M lim st_b FromMEnv →
      initErrsPtr ≠ 0#64 →
      ∀ (msgVer : BitVec 32) (b_2c0 : BitVec 8) (g : RecordGhost) (G₁ recG : SessionGhost)
        (st : SessionState (List (BitVec 8))),
        LibsignalFrozen lsmpl s1.mem →
        s1.pc = dpClosureEntryM3Placed + 0x1e04#64 →
        s1.status = .Running →
        s1.sp = s.sp →
        (s.sp &&& 15#64 == 0#64) = true →
        s1.trace = s0.trace →
        s1.readReg64 .x9 = msgVer.setWidth 64 →
        s1.readReg64 .x19 = coroPtr →
        s1.readReg64 .x24 = s.sp + 0x370#64 →
        s1.readReg64 .x27 = ctxPtr →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
          (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
            ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            memRegion (s.sp + 0x3e0#64) 344 ∗
            sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
            sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
            prevSessionsEmptyAt A.repAlloc coroPtr g ∗
            ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
            lsLogOff ∗
            memRegion outPtr 48 ∗
            memRegion (s.sp + 0x250#64) 20 ∗
            memRegion (s.sp + 0x270#64) 48 ∗
            memRegion (s.sp + 0x370#64) 36 ∗
            memRegion (s.sp + 0x930#64) 48 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim st_b s1 ∗
            stackAt s.sp growOneSpeStack)
          (fun sf P_f =>
            ∃ evs_vn : List AllocEvent,
              FromMEnv evs_vn ∧
              (P_f ⊢
                ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
                ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
                ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                memRegion (s.sp + 0x3e0#64) 344 ∗
                stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_vn st_b) s0 s sf
                  coroPtr outPtr (.invalidMessage .preKey .decryptionFailed)) ∧
              sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
              LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
          (fun _ _ => False)

set_option maxHeartbeats 1200000 in
theorem stageP3_ver_ne_prevEmpty_sessionShim_full_placed_ok [LibsignalFullPlacement] :
    StageP3VerNePrevEmptySessionShimFrozenPlacedStmt := by
  intro M A lim ext hshim halloc hdealloc hGrow hDropSS3 _hpanic
    st0 s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hfits_fromM hinit_ne msgVer b_2c0
    g G₁ recG st hfr1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
  have hfits : FitsEnv M lim st0 StageP3VerNeM3Env := fitsEnv_stageP3VerNeM3Env_of_fromMEnv hfits_fromM
  intro R hm hL1
  have hwp : SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗ prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st0 s1 ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f => (∃ evs : List AllocEvent, StageP3VerNeM3Env evs ∧ (P_f ⊢
        ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
        ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs st0) s0 s sf coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed))) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (fun _ _ => False) := by
    have hlog_c : lsLogOff = pqLogLevelCellPlaced := rfl; refine weaken_frame_tail (Entails.of_eq hlog_c) (by sep_focus) ?_
    have hs1 := overVerNe_1e04_to_1e78_frozen_placed_at_gen (M := M) (A := A) (lim := lim) (Qp := fun _ _ => False)
      ext hGrow hDropSS3 st0 (fitsS1_of_fitsM3 hfits)
      s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
      hfr1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine bind_sepWPp_nopanic_tail hs1 (by sep_focus)
      fun s6b P_m6b hpc6b hrun6b
        ⟨⟨errsPtr, evs1, hevs1, hP6b⟩, hsp6b_s, htr6b_0, hx19_6b, _, hvregs_6b, hcro6b, hL6b⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hP6b) ?_
    let st6b := M.stepEvents evs1 st0
    have hfits_tail : FitsEnv M lim st6b VerNeTailEnv := fitsTail_of_fitsM3 hfits hevs1
    refine weaken_frame_tail
      (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun bs336 => ?_
    refine weaken_frame_tail
      (T := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
        SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
      (T' := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
        SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
    have hlog_eq : pqLogLevelCellPlaced = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
    refine weaken_frame_tail (Entails.of_eq hlog_eq) (by sep_focus) ?_
    have hsp6b_align : (s6b.sp &&& 15#64 == 0#64) = true := by rw [hsp6b_s]; exact hsp_align
    have hprev_f0 : prevSessionsEmptyAt A.repAlloc coroPtr g =
        ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
        (((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
         vecBuf A.repAlloc 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr []) := by
      unfold prevSessionsEmptyAt vecAt vecHeader; dsimp only [List.length_nil]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl
    refine weaken_frame_tail (Entails.of_eq hprev_f0) (by sep_focus) ?_
    simp only [sepConj_assoc]
    have hstep7 := p3_err_ver_d_sessionShim_placed_wp A lim ext hshim st6b s6b coroPtr outPtr ctxPtr
      recG.localIk.cap 0x8000000000000006#64 (cap_ne_noneCap_of_lt hcap_lt)
      hpc6b hrun6b hsp6b_align hx19_6b
    rw [hsp6b_s] at hstep7
    refine bind_sepWP_cro_frame_tail hcro6b hL6b hstep7 (by sep_focus)
      fun s7 hpc7 hrun7 hcro7 hL7 hregs7 => ?_
    rcases hregs7 with ⟨hsp7_6b, htr7_6b, hx0_7, hx1_7, hx19_7, hx24_7, hx25_7, hx26_7, _, _, hvregs_7⟩
    refine weaken_frame_tail (Entails.of_eq hprev_f0.symm) (by sep_focus) ?_
    refine weaken_frame_tail (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
    have hpack_ss :
        ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
          sessionHeap A.repAlloc recG st ⊢
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st hinl
    refine weaken_frame_tail hpack_ss (by sep_focus) ?_
    refine weaken_frame_tail (sp3e0_cell_336_entails_344 s.sp 0xffffffffffffffff#64)
      (by sep_focus) ?_
    have htail := stageP3_err_ver_tail_prevEmpty_placed_ok (M := M) (A := A) (lim := lim)
      (Qp := fun _ _ => False) ext halloc hdealloc hDropSS3 st6b hfits_tail
      s0 s s7 coroPtr outPtr errsPtr msgVer b_2c0 g recG st
      hcro7 hL7 hpc7 hrun7 hsp7_6b hsp_align (htr7_6b.trans htr6b_0)
      hx0_7 hx1_7 hx19_7 hx24_7 hx25_7 hx26_7
    refine bind_sepWPp_nopanic_tail htail (by sep_focus)
      fun sf P_mf hpcf hrunf ⟨⟨evs2, hevs2, hP_t⟩, hspf, htrf, hcc, hcrof, hLf, hvregs_f⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hP_t) ?_
    have hpool_eq :
        A.pool lim (M.stepEvents evs2 st6b) sf =
          A.pool lim (M.stepEvents (evs1 ++ evs2) st0) sf := by
      dsimp only [st6b]
      rw [← M.stepEvents_append]
    refine SepWPp.done hpcf hrunf ?_
    refine ⟨⟨evs1 ++ evs2, stageP3VerNeM3Env_of_parts hevs1 hevs2, ?_⟩,
      hspf, htrf, hcc, hcrof, hLf, by rw [hvregs_f, hvregs_7, hvregs_6b]⟩
    unfold stageP3ErrPostPrevEmptyM3Placed
    dsimp only [LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlacedBudget.stageP3ErrPostPrevEmptyPlaced,
      SessionState.recordError]
    rw [← hpool_eq]
    have hexists_errs :
        ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ⊢
          ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
            ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗
            ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 4#64
        (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64 (Entails.refl _)))
    exact entails_replace_sub hexists_errs (by sep_focus) (eq_of_sep_emp (by sep_focus))
  rcases hwp R hm hL1 with ⟨sf, hsteps,
    ⟨hpcf, hrunf, P_f, hmf, ⟨evs, hevs, hPf⟩, hspf, htrf, hcc, hcrof, _, hvregs_f⟩ | hpan | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf,
      evs, stageP3VerNeM3Env_imp_fromMEnv evs hevs, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem lscro_of_frozen_aux [LibsignalPlacement] {m : Memory}
    (hfr : LibsignalFrozen lsmpl m) : LibsignalCodeRoLoaded lsmpl m :=
  ⟨LibsignalCodeLoaded.of_codeLoaded hfr.2, hfr.1⟩

private theorem bind_sepWP_lsfr_frame_err [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_step : SepProp} {P_step_post : State → SepProp}
    {F : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalFrozen lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL =>
    bind_sepWP_fr_frame_budget hL hfr hstep hP
      (fun sm hpcm hrunm _ hfrm hregs => hnext sm hpcm hrunm hfrm hregs) R hm hL

private theorem call_lsfr_nopanic_err [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hcall : subroutine_ok prog entry (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalFrozen lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL =>
    call_raw_nopanic_fr_budget hL hfr hcall hpc hrun hsp hlr hspec hφ hP
      hpan_false hexit_false hoom_false
      (fun sf hpcf hrunf hspf hsp_alf hcsf _ hfrf =>
        hnext sf hpcf hrunf hspf hsp_alf hcsf hfrf)
      R hm hL

set_option maxHeartbeats 1200000 in
private theorem stageP3_sub5_err_nondup_zero_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3BasePlaced A lim ext)
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hfits : FitsEnv M lim st_b FromVPostTdEnv)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPreZeroPlaced A lim st_b s0 s s coroPtr outPtr initErrsPtr prevStatesPtr e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        ∃ evs_err : List AllocEvent,
          FromVPostTdEnv evs_err ∧
          (P_f ⊢ stageP3ErrPost_placed A lim (M.stepEvents evs_err st_b) s0 s sf coroPtr outPtr prevStatesPtr e) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  have hcro : LibsignalCodeRoLoaded lsmpl s.mem := lscro_of_frozen_aux hfr
  unfold stageP3ErrPreZeroPlaced
  have hrec_err : SessionState.recordError .preKey e = .invalidMessage .preKey .decryptionFailed :=
    recordError_preKey_of_speTag_ne_speWord23 he_npan htag_ne23
  refine intro_lsro_decryptionFailed_err hcro ?_
  have hdecomp : vecResultAt A.repAlloc (s.sp + 0x270#64) (.error e) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A.repAlloc (utf8 "decrypt") c e⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ speTag e) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
        ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
        ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A.repAlloc (utf8 "decrypt") (s.sp + 0x270#64) e he_npan
    dsimp only [vecResultAt] at h1 ⊢; refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
      (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
  refine sepWPp_weaken_frame hdecomp (by sep_focus) ?_; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine sepWPp_weaken_frame
    (P₁ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A.repAlloc (utf8 "decrypt") c e⌝)
    (P₂ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A.repAlloc (utf8 "decrypt") c e⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hreassemble => ?_)
  refine sepWPp_weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x930#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u930 => SepWPp.exists_elim fun u938 => SepWPp.exists_elim fun u940 =>
    SepWPp.exists_elim fun u948 => SepWPp.exists_elim fun u950 => SepWPp.exists_elim fun u958 => ?_
  have hstep1 := p3_err_nondup_a_placed_wp A lim st_b ext s coroPtr outPtr (speTag e)
    w0 w1 w2 w3 w4 u930 u938 u940 u948 u950 u958
    (speTag_ne_ok_of_ne_panic he_npan) htag_ne23 hpc hrun hsp_align hx19 hx24
  refine bind_sepWP_lsfr_frame_err hfr hstep1 (by sep_focus) fun s1 hpc1 hrun1 hfr1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, _, _, _, _, hx19_1, hx24_1, hx25_1, hx26_1, _, _, _, hx30_1, hvregs_1⟩
  refine sepWPp_weaken_frame (words6_entails_memRegion48 (s.sp + 0x930#64) (speTag e) w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hstack_log := stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine sepWPp_weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_lsfr_nopanic_err (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := lsLogOff ∗ stackAt s.sp pqxdhClosureStack)
    hfr1 (pqxdh_log_closure_frozen_placed_ok_of_block (callerProg := lsProg_518 ext))
    hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s]; rfl) trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hfr2 => ?_)
  have hcro2 : LibsignalCodeRoLoaded lsmpl s2.mem := lscro_of_frozen_aux hfr2
  dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr2_1, hvm2_1⟩ => ?_
  have hpool12 : A.pool lim st_b s1 = A.pool lim st_b s2 := (A.pool_of_vmPreserved hvm2_1).symm
  refine sepWPp_weaken_frame (Entails.of_eq hpool12) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq hstack_log.symm) (by sep_focus) ?_)
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, _, _, hvregs_cs2⟩
  have hstep3 := p3_err_nondup_b_placed_wp A lim st_b ext s2 coroPtr hpc2 hrun2
    (by rw [hsp2_s]; exact hsp_align) (hx19_cs2.trans hx19_1)
  rw [hsp2_s] at hstep3
  refine bind_sepWP_lscro_frame_err hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx25_3, hx26_3, _, _, _, hx30_3, hvregs_3⟩
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_2] using hsp_align
  have htr3_0 : s3.trace = s0.trace := htr3_2.trans (htr2_1.trans (htr1_s.trans htr))
  have hfits_grow := fitsEnv_growOneSpe_of_fromVPostTd hfits
  refine call_lscl_nopanic_err
    (spec := growOneSpeSpec M A lim)
    (x := ((s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))), st_b))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool lim st_b s3 ∗ stackAt s.sp growOneSpeStack)
    hcro3 hC.grow hpc3 hrun3 hsp3_al hx30_3
    (by
      rw [growOneSpe_pre_zero_eq M A lim st_b s3 (s.sp + 0x3c8#64) initErrsPtr hx0_3 hinit_ne hfits_grow,
        hsp3_2, pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus) (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  rw [growOneSpe_post_zero_eq M A lim st_b s3 s4 (s.sp + 0x3c8#64) initErrsPtr, hsp3_2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine sepWPp_weaken_frame (P₁ := ⌜s4.trace = s3.trace⌝) (P₂ := ⌜s4.trace = s3.trace⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun htr4_3 => ?_)
  refine sepWPp_weaken_frame
    (P₁ := ⌜errsPtr ≠ 0 ∧ errsPtr.toNat % 8 = 0⌝)
    (P₂ := ⌜errsPtr ≠ 0 ∧ errsPtr.toNat % 8 = 0⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ => ?_)
  have hsplit192 : memRegion errsPtr 192 = memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144) (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
  refine sepWPp_weaken_frame (Entails.of_eq hsplit192) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq (memRegion48_words6_split_eq errsPtr)) (by sep_focus) ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 => SepWPp.exists_elim fun e2 =>
    SepWPp.exists_elim fun e3 => SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  have hlog_eq : pqLogLevelCellPlaced = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine sepWPp_weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp4_s : s4.sp = s.sp := hsp4_3.trans hsp3_2
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, hvregs_cs4⟩
  have hstep5 := p3_err_nondup_c_placed_wp A lim (M.stepEvents (rustAllocEvents 192 8) st_b)
    ext hC.shim s4 coroPtr errsPtr (speTag e) w0 w1 w2 w3 w4 e0 e1 e2 e3 e4 e5
    hpc4 hrun4 (by rw [hsp4_s]; exact hsp_align) (hx19_cs4.trans hx19_3) (hx21_cs4.trans hx21_3)
    (by rw [hx25_cs4, hx25_3, hx25_cs2, hx25_1, hsp4_s])
  rw [hsp4_s] at hstep5
  refine bind_sepWP_lscro_frame_err hcro4 hstep5 (by sep_focus) fun s5 hpc5 hrun5 hcro5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hx0_5, hx1_5, hx19_5, hx24_5, hx25_5, hx26_5, _, _, _, hvregs_5⟩
  have htr5_0 : s5.trace = s0.trace := htr5_4.trans (htr4_3.trans htr3_0)
  have hreasm_errs : ((errsPtr + 0x0#64) ↦₆₄ speTag e) ∗ ((errsPtr + 0x8#64) ↦₆₄ w0) ∗
      ((errsPtr + 0x10#64) ↦₆₄ w1) ∗ ((errsPtr + 0x18#64) ↦₆₄ w2) ∗
      ((errsPtr + 0x20#64) ↦₆₄ w3) ∗ ((errsPtr + 0x28#64) ↦₆₄ w4) ∗ H ⊢
      speAt A.repAlloc (utf8 "decrypt") errsPtr e := by
    simpa only [words6At, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hreassemble errsPtr
  have hstack_alloc := stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  have hlog_eq2 : (lsLogFilterAddr ↦₆₄ 0#64) = lsLogOff := rfl
  refine sepWPp_weaken_frame (Entails.of_eq hlog_eq2) (by sep_focus)
    (sepWPp_weaken_frame hreasm_errs (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_))
  have hfits17 := fitsEvents_alloc17_of_fromVPostTd hfits
  have halloc17 := p3_alloc_2eac_placed_ok (A := A) (lim := lim) ext hC.alloc
    (M.stepEvents (rustAllocEvents 192 8) st_b) s5
    emp hfits17 hcro5 hpc5 hrun5 (by rw [hsp5_4]; exact hsp_align) hx0_5 hx1_5
  rw [sepConj_emp, hsp5_4] at halloc17
  refine bind_sepWPp_frame_false halloc17 (by sep_focus)
    fun s6 P_m6 hpc6 hrun6 ⟨hP6, hdf_ne, hsp6_5, htr6_5, hcs6, hcro6⟩ => ?_
  rw [sepConj_emp] at hP6
  refine sepWPp_weaken_frame hP6 (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq (memRegion17_split_eq (s6.readReg64 .x0))) (by sep_focus) ?_))
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun df_10 => SepWPp.exists_elim fun df_8 => SepWPp.exists_elim fun df_0 => ?_
  refine sepWPp_weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  rcases hcs6 with ⟨hx19_cs6, _, _, _, _, hx24_cs6, hx25_cs6, hx26_cs6, _, _, _, hvregs_cs6⟩
  have hstep7 := p3_err_nondup_d_placed_wp A lim
    (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b))
    ext s6 coroPtr (s6.readReg64 .x0)
    0x6974707972636564#64 0x656c696166206e6f#64 df_0 df_8 (speTag e) w0 w1 w2 df_10 (w3.extractLsb' 0 8)
    hdf_ne hpc6 hrun6 (by rw [hsp6_5]; exact hsp_align) rfl (hx19_cs6.trans hx19_5)
  rw [hsp6_5] at hstep7
  refine bind_sepWP_lscro_frame_err hcro6 hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx19_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7, hvregs_7⟩
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp.drop_frame
    (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  have hstack_drop2 := stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine sepWPp_weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s6.readReg64 .x0))) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_))
  refine call_lscl_nopanic_err
    (x := ((⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost),
           M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b)))
    (T := sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗
          A.pool lim (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b)) s7 ∗
          stackAt s.sp dropSessionStructure2Stack)
    hcro7 hC.dropSs3 hpc7 hrun7 (by simpa only [State.spAligned, hsp7_6] using hsp_align) hx30_7
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_6])
    (And.intro hx0_7 (show LsRetAddr624 (s7.readReg64 .lr) by
      change LsRetAddr624 (s7.readReg64 .x30)
      rw [hx30_7]
      exact lsRetAddr624_blockPlacement_base_add 518 0x34dc#64 (by decide) (by decide)))
    (by sep_focus)
    (hnext := fun s8 hpc8 hrun8 hsp8_7 _ hcs8 hcro8 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_6]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_drop1 => ?_
  refine sepWPp_weaken_frame
    (P₁ := ⌜s8.trace = s7.trace ∧ FreeOnlyEvs evs_drop1⌝)
    (P₂ := ⌜s8.trace = s7.trace ∧ FreeOnlyEvs evs_drop1⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨htr8_7, hevs_drop1⟩ => ?_)
  have hsp8_s : s8.sp = s.sp := hsp8_7.trans hsp7_6
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, hx28_cs8, _, hvregs_cs8⟩
  have htail := stageP3_err_tail_nondup_dec_zero_placed_ok ext hC.dealloc hC.dropSpe2 hC.dropSs3
    (M.stepEvents evs_drop1 (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b)))
    s0 s8 coroPtr outPtr errsPtr prevStatesPtr 17#64 (s6.readReg64 .x0) 17#64 w3' w4 e he_npan b_2c0 recG recSt
    hcro8 hpc8 hrun8 (by rw [hsp8_s]; exact hsp_align) (htr8_7.trans (htr7_6.trans (htr6_5.trans htr5_0)))
    (hx19_cs8.trans hx19_7)
    (by rw [hx24_cs8, hx24_7, hx24_cs6, hx24_5, hx24_cs4, hx24_3, hx24_cs2, hx24_1, hsp8_s])
    (by rw [hx25_cs8, hx25_7, hx25_cs6, hx25_5, hsp8_s])
    (hx26_cs8.trans (hx26_7.trans (hx26_cs6.trans (hx26_5.trans (hx26_cs4.trans (hx26_3.trans (hx26_cs2.trans hx26_1)))))))
    (hx28_cs8.trans hx28_7)
  rw [hsp8_s] at htail
  refine ret_sepWPp_frame_false htail (by sep_focus)
    fun sf _ _ _ ⟨evs_tail, hevs_tail, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A.repAlloc
    outPtr (s6.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  rw [RustCliAllocBudget.repAlloc_live] at hrec
  have hst_eq :
      M.stepEvents evs_tail
        (M.stepEvents evs_drop1
          (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b))) =
      M.stepEvents (rustAllocEvents 192 8 ++ (rustAllocEvents 17 1 ++ (evs_drop1 ++ evs_tail))) st_b := by
    simp only [← M.stepEvents_append, List.append_assoc]
  rw [hst_eq] at hPf
  refine ⟨rustAllocEvents 192 8 ++ (rustAllocEvents 17 1 ++ (evs_drop1 ++ evs_tail)),
    fromVPostTdEnv_of_nondup hevs_drop1 hevs_tail, ?_, hspf, htrf, hcc, hcrof,
    by rw [hvregs_f, hvregs_cs8, hvregs_7, hvregs_cs6, hvregs_5, hvregs_cs4, hvregs_3, hvregs_cs2, hvregs_1]⟩
  unfold stageP3ErrPost_placed CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPost_placed
  rw [hrec_err]
  have hrr : ∀ st_e, recordResultAt (A.atState lim st_e sf) outPtr (.error (.invalidMessage .preKey .decryptionFailed)) =
      recordResultAt A.repAlloc outPtr (.error (.invalidMessage .preKey .decryptionFailed)) := fun _ => rfl
  have hpl : ∀ st_e, (A.atState lim st_e sf).pool = A.pool lim st_e sf := fun _ => rfl
  rw [hrr, hpl]
  have herrs : ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ⊢
      ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
        ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗
        ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
    Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr
      (Entails.sepExists_right 1#64 (Entails.refl _)))
  refine Entails.trans (entails_replace_sub hPf (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub herrs (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hrec (by sep_focus) rfl) ?_
  exact entails_replace_sub (Entails.of_eq hstack_drop2.symm) (by sep_focus) (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_zero_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3BasePlaced A lim ext)
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hfits : FitsEnv M lim st_b FromVPostTdEnv)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPreZeroPlaced A lim st_b s0 s s coroPtr outPtr initErrsPtr prevStatesPtr e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        ∃ evs_err : List AllocEvent,
          FromVPostTdEnv evs_err ∧
          (P_f ⊢ stageP3ErrPost_placed A lim (M.stepEvents evs_err st_b) s0 s sf coroPtr outPtr prevStatesPtr e) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  have hcro : LibsignalCodeRoLoaded lsmpl s.mem := lscro_of_frozen_aux hfr
  by_cases htag23 : speTag e = speWord 23
  · obtain ⟨ratVer, counter, rfl⟩ := speTag_eq_speWord23_iff.mp htag23
    unfold stageP3ErrPreZeroPlaced
    have hstack_drop2 : stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
      stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
    rw [hstack_drop2]
    have hdup := stageP3_sub5_err_dup_zero_placed_ok ext hC.dropSs3 st_b
      s0 s coroPtr outPtr initErrsPtr prevStatesPtr ratVer counter b_2c0 G₂ recG st₂ recSt
      hcro hpc hrun hsp_align htr hx19 hx24
    refine ret_sepWPp_frame_false hdup (by sep_focus)
      fun sf _ _ _ ⟨evs_dup, hevs_dup, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
    have herrs : ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ⊢
        ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗ ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 0#64 (Entails.sepExists_right initErrsPtr (Entails.sepExists_right 0#64 (Entails.refl _)))
    refine ⟨evs_dup, Or.inl hevs_dup, ?_, hspf, htrf, hcc, hcrof, hvregs_f⟩
    unfold stageP3ErrPost_placed CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPost_placed
    have hrr : recordResultAt (A.atState lim (M.stepEvents evs_dup st_b) sf) outPtr (.error (.duplicatedMessage ratVer counter)) = recordResultAt A.repAlloc outPtr (.error (.duplicatedMessage ratVer counter)) := rfl
    have hpl : (A.atState lim (M.stepEvents evs_dup st_b) sf).pool = A.pool lim (M.stepEvents evs_dup st_b) sf := rfl
    dsimp only [SessionState.recordError]; rw [hrr, hpl]
    refine Entails.trans (entails_replace_sub hPf (by sep_focus) rfl) ?_
    refine Entails.trans (entails_replace_sub herrs (by sep_focus) rfl) ?_
    exact entails_replace_sub (Entails.of_eq hstack_drop2.symm) (by sep_focus) (eq_of_sep_emp (by sep_focus))
  · exact stageP3_sub5_err_nondup_zero_full_placed_ok ext hC st_b s0 s coroPtr outPtr initErrsPtr prevStatesPtr
      hfits hinit_ne e he_npan htag23 b_2c0 G₂ recG st₂ recSt hfr hpc hrun hsp_align htr hx19 hx24

end FrozenVariants

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux
