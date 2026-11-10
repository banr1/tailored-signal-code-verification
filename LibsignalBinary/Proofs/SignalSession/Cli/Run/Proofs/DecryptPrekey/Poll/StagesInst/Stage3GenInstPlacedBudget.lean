/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
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
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Stage P3 Instantiations

Proves zero-capacity version-mismatch and clone-prefix lemmas (`stageP3_ver_ne_zero_placed_ok`,
`stageP3_clone_vregs_prefix_placed_steps`) and instantiates `StageP3PrevEmptyVRegsPlacedStmt`,
`StageP3GenStepsVRegsPlacedStmt`, and `StageP3Prev1VRegsPlacedStmt` (plus `LibsignalFrozen`
variants) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto SessionState SignalMessage SignalProtocolError)
open CryptoVerification (
  LibsignalPlacement lsLogFilterAddr lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (recordResultAt rootStack)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost decryptDraws protocolAddressAt sessionStateAt
  signalMessageAt uuidTryParse vecResultAt
)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  growOneSpeStack lsLogOff setSessionStateStack
)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (SessionInline sessionHeap)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved decryptPrekeySavedRegsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  cap_ne_noneCap_of_lt cell_join_head8 cell_split_head8 dfPtr_words_eq_decryptionFailedStr
  dropSessionStructure2Stack entails_replace_sub eq_of_sep_emp errs48_144_join
  extractLsb0_8_of_unpack64_cons memRegion20_fold memRegion20_split_eq
  memRegion48_words6_split_eq memRegion_17_split_eq sessionStateAt_pack_head_tail
  sessionStateAt_unpack_head_tail sp370_36_err_split_eq stageP3Sub5ExtraPre
  words3_repack_w32_2w64_w32 words6At_preKey_decryptionFailed_entails_recordResultAt
  words6_entails_memRegion48 )
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (
  genP3S5Model genP3S5ModelPanicProp genP3SpillAll genP3SpillAll_entails_s5
  memRegion344_104_240_eq stackAt_root_split_grow
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (LsTokenInitM3 cloneExitPCPlaced)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (OverPrevEncOK)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (pqLogLevelCellPlaced)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit dpPollEntryPlaced dpPollProgPlaced stageP3Sub5ExtraPrePrevEmpty
)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
  fitsEvents_append rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2PlacedBudget (dropSpe2VerSpec drop_spe2_ver_placed_ok_at)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux (
  bind_sepWPp_false_steps_framed genP3PostPlaced genP3PrePlaced genP3S5PostFramePlaced
  postTryDecrypt_entails_s5DispatchPrevEmpty_placed ret_sepWPp_frame_false
  sepWPp_frame_false_qp sepWPp_lift_false_qp sepWPp_weaken_frame
  stageP3DispatchOkMidPrevEmptyPlaced stageP3DispatchPrePrevEmptyPlaced
  stageP3ErrPostPrevEmptyM3Placed stageP3ErrPrePrevEmptyM3Placed stageP3_sub5_decResult_placed_ok )
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudget (stageP3_sub5_err_prevEmpty_placed_ok)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux (
  bind_sepWP_lscro_frame_err call_lscl_ro_nopanic_err freeOnlyEvs_append intro_lsro_decryptionFailed_err )
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlacedBudgetAux (
  StageP3VerNeM3Env dpClosureEntryVerPlaced fitsS1_of_fitsM3 fitsTail_of_fitsM3
  p3_err_ver_e_placed_wp p3_err_ver_f_placed_wp stageP3VerNeM3Env_of_parts )
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget (
  OverVerNe1e04CliAtPlacedBody stageP3_call_tryDecrypt_prev1_placed_steps )
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  cloneGen_vregs_placed_ok p3_alloc_33b0_zero_placed_ok stageP3_err_tail_common_zero_placed_ok )
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget (pqxdhLogClosurePlacedSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget (overVerNe_1e04_to_1e78_cro_placed_at_gen)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux (
  VerNeTailEnv bind_sepWP_cro_frame_tail bind_sepWPp_nopanic_tail fitsAlloc17_of_fitsEnv
  freeOnlyEvs_dealloc_192_8 verNeTailEnv_of_freeSuffix weaken_frame_tail )
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux (VerNeTopEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  StageP3Prev1VRegsAtPlacedStmt StageP3Prev1VRegsPlacedStmt )
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  ChainClone3OkPlaced SenderChainClone3OkPlaced StageP3Env StageP3ErrEnv StageP3GenStepsVRegsPlacedStmt
  StageP3OkPrefixEnv StageP3PrevEmptyVRegsPlacedStmt StageP3VerNeEnv genP3Pre_placed
  genP3S5PostFrame_placed pollTryDecryptPlacedSpecTPTight stageP3DispatchOkMidPrevEmpty_placed
  stageP3DispatchOkMid_placed stageP3ErrPostPrevEmpty_placed stageP3ErrPost_placed stageP3TryDecryptEnvArgs )
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux (
  StageP3CalleesM3Placed StageP3VerNePrevEmptySessionShimPlacedStmt bind_sepWPp_frame_false
  fitsEnv_stageP3VerNeM3Env_of_fromMEnv p3_err_ver_d_sessionShim_placed_wp sp3e0_cell_336_entails_344
  stageP3ErrPreZeroPlaced stageP3VerNeM3Env_imp_fromMEnv stageP3_sub5_err_zero_placed_ok
  stageP3_ver_ne_prevEmpty_sessionShim_placed_ok )
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (dropSessionStructureLocal2Spec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  FromMEnv FromVPostTdEnv SegCloneEnv TryDecryptEnvArgs segCloneEvents )

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux (
  StageP3CalleesM3Placed StageP3VerNePrevEmptySessionShimPlacedStmt
  stageP3_sub5_err_zero_placed_ok stageP3_ver_ne_prevEmpty_sessionShim_placed_ok
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

/-! ## 1. Zero-Cap (`prevCap = 0`) Version-Mismatch Path & Clone Prefix -/

set_option maxHeartbeats 1200000 in
private theorem stageP3_err_ver_tail_zero_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3Placed A lim ext)
    (st0 : M.σ) (hfits : FitsEnv M lim st0 VerNeTailEnv)
    (s0 s s7 : State) (coroPtr outPtr errsPtr prevStatesPtr : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro7 : LibsignalCodeRoLoaded lsmpl s7.mem)
    (hpc7 : s7.pc = dpClosureEntryVerPlaced + 0x33b0#64) (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr7 : s7.trace = s0.trace)
    (hx0_7 : s7.readReg64 .x0 = 17#64) (hx1_7 : s7.readReg64 .x1 = 1#64)
    (hx19_7 : s7.readReg64 .x19 = coroPtr) (hx24_7 : s7.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_7 : s7.readReg64 .x25 = s.sp + 0x210#64) (hx26_7 : s7.readReg64 .x26 = outPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
       memRegion (errsPtr + 12#64) 36 ∗ memRegion (errsPtr + 48#64) 144 ∗ A.live errsPtr 192 8 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st0 s7 ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          VerNeTailEnv evs ∧
          (P_f ⊢ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
            memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            recordResultAt A.repAlloc outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
            memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s.sp growOneSpeStack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s7)
      (fun _ _ => False) := by
  have hstack_alloc := stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine sepWPp_weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have halloc17 := p3_alloc_33b0_zero_placed_ok (Qp := fun _ _ => False) ext hC.alloc st0 s7 emp
    (fitsAlloc17_of_fitsEnv hfits) hcro7 hpc7 hrun7 (by rw [hs7_sp]; exact hsp_align) hx0_7 hx1_7
  rw [sepConj_emp, hs7_sp] at halloc17
  refine bind_sepWPp_frame_false halloc17 (by sep_focus)
    fun s8 P_m8 hpc8 hrun8 ⟨hP8, hdf_ne, hsp8_7, htr8_7, hcs8, hcro8⟩ => ?_
  rw [sepConj_emp] at hP8
  let st8 := M.stepEvents (rustAllocEvents 17 1) st0
  refine sepWPp_weaken_frame hP8 (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq (memRegion_17_split_eq (s8.readReg64 .x0))) (by sep_focus) ?_))
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_df10 => SepWPp.exists_elim fun u_df8 => SepWPp.exists_elim fun u_df0 =>
    sepWPp_weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x270#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_270 => SepWPp.exists_elim fun u_278 => SepWPp.exists_elim fun u_280 =>
    SepWPp.exists_elim fun u_288 => SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 =>
    sepWPp_weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, _, _, hvregs_cs8⟩
  refine intro_lsro_decryptionFailed_err hcro8 ?_
  have hstep9 := p3_err_ver_e_placed_wp A lim ext st8 s8 coroPtr (s8.readReg64 .x0) errsPtr
    0x6974707972636564#64 0x656c696166206e6f#64 u_df0 u_df8 u_270 u_278 u_280 u_288 u_df10 (w3.extractLsb' 0 8)
    hdf_ne hpc8 hrun8 (by rw [hsp8_7]; exact hsp_align) rfl (hx19_cs8.trans hx19_7)
  rw [hsp8_7] at hstep9
  refine bind_sepWP_lscro_frame_err hcro8 hstep9 (by sep_focus) fun s9 hpc9 hrun9 hcro9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx19_9, hx21_9, hx22_9, hx23_9, hx24_9, hx25_9, hx26_9, _, hx28_9, _, hx30_9, hvregs_9⟩
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp.drop_frame
    (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64)) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s8.readReg64 .x0))) (by sep_focus) ?_)
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  have hstack_spe := stackAt_split_bottom s.sp dropSpeStack 480 (by decide)
  refine sepWPp_weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq hstack_spe) (by sep_focus) ?_)
  refine call_lscl_ro_nopanic_err (spec := dropSpe2VerSpec M A lim) (x := (errsPtr, msgVer, st8))
    (φ := s9.readReg64 .x0 = errsPtr)
    (T := (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
          memRegion (errsPtr + 12#64) 36 ∗ A.pool lim st8 s9 ∗ stackAt s.sp dropSpeStack)
    hcro9 (drop_spe2_ver_placed_ok_at (M := M) (A := A) (lim := lim)) hpc9 hrun9
    (by simpa only [State.spAligned, hsp9_8] using hsp_align) hx30_9
    (by dsimp only [dropSpe2VerSpec]; rw [hsp9_8]) hx0_9 (by sep_focus)
    (hnext := fun s10 hpc10 hrun10 hsp10_9 _ hcs10 hcro10 => ?_)
  dsimp only [dropSpe2VerSpec]; rw [hsp9_8, sepConj_assoc]
  refine SepWPp.pure_elim fun htr10_9 =>
    sepWPp_weaken_frame (Entails.of_eq (errs48_144_join errsPtr)) (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq hstack_spe.symm) (by sep_focus)
        (sepWPp_weaken_frame (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_))
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => sepWPp_weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_)
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) 17#64 (s8.readReg64 .x0) 17#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine sepWPp_weaken_frame (Entails.of_eq hrepack278) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun u_250 =>
    sepWPp_weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 => SepWPp.exists_elim fun u_380 =>
    SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 =>
    sepWPp_weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp10_s : s10.sp = s.sp := hsp10_9.trans hsp9_8
  rcases hcs10 with ⟨hx19_cs10, _, hx21_cs10, hx22_cs10, hx23_cs10, hx24_cs10, hx25_cs10, hx26_cs10, _, hx28_cs10, _, hvregs_cs10⟩
  have hstep11 := p3_err_ver_f_placed_wp ext hC.dealloc st8 s10 coroPtr errsPtr recG.localIk.cap
    ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)
    w3' w4 u_250 u_258 u_370 u_378 u_384 u_38c
    ((17#64 : BitVec 64).extractLsb' 0 32) ((17#64 : BitVec 64).extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc10 hrun10 (by rw [hsp10_s]; exact hsp_align)
    (hx19_cs10.trans hx19_9) (hx21_cs10.trans hx21_9) (hx22_cs10.trans hx22_9) (hx23_cs10.trans hx23_9)
    (by rw [hx24_cs10, hx24_9, hx24_cs8, hx24_7, hsp10_s])
    (by rw [hx25_cs10, hx25_9, hx25_cs8, hx25_7, hsp10_s]) (hx28_cs10.trans hx28_9)
  rw [hsp10_s] at hstep11
  refine bind_sepWP_lscro_frame_err hcro10 hstep11 (by sep_focus) fun s11 hpc11 hrun11 hcro11 hregs11 => ?_
  rcases hregs11 with ⟨hsp11_10, htr11_10, hx0_11, hx19_11, hx22_11, _, hx25_11, hx26_11, _, hx28_11, _, hx30_11, hvregs_11⟩
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A.repAlloc recG st ⊢ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st hinl
  have hfold250 : ((s.sp + 0x250#64) ↦₆₄ ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ (17#64 : BitVec 64).extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion20_fold (s.sp + 0x250#64)
      ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
      ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32) ((17#64 : BitVec 64).extractLsb' 32 32)
  have hstack_drop2 := stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  let st11 := M.stepEvents (rustDeallocEvents 192 8) st8
  refine sepWPp_weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus)
    (sepWPp_weaken_frame hpack_ss (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus)
        (sepWPp_weaken_frame
          (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000018#64 17#64 (s8.readReg64 .x0) 17#64 w3' w4) (by sep_focus)
          (sepWPp_weaken_frame hfold250 (by sep_focus)
            (sepWPp_weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_)))))
  have hcommon := stageP3_err_tail_common_zero_placed_ok (Qp := fun _ _ => False) ext hC.dropSs3 st11
    s0 s11 coroPtr outPtr 0x8000000000000018#64 prevStatesPtr 17#64 (s8.readReg64 .x0) 17#64 w3' w4 b_2c0 recG st
    hcro11 hpc11 hrun11 (by rw [hsp11_10]; exact hsp_align) (htr11_10.trans (htr10_9.trans (htr9_8.trans (htr8_7.trans htr7))))
    hx0_11 hx19_11 hx22_11 (by rw [hx25_11, hsp11_10])
    (hx26_11.trans (hx26_cs10.trans (hx26_9.trans (hx26_cs8.trans hx26_7)))) hx28_11 hx30_11
  rw [hsp11_10] at hcommon
  refine ret_sepWPp_frame_false hcommon (by sep_focus)
    fun sf _ _ _ ⟨evs_c, hfree_c, hP_c, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A.repAlloc outPtr (s8.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  rw [RustCliAllocBudget.repAlloc_live] at hrec
  have hpool_eq :
      M.stepEvents evs_c st11 =
        M.stepEvents (rustAllocEvents 17 1 ++ (rustDeallocEvents 192 8 ++ evs_c)) st0 := by
    dsimp only [st11, st8]; simp only [← M.stepEvents_append, List.append_assoc]
  rw [hpool_eq] at hP_c
  refine ⟨rustAllocEvents 17 1 ++ (rustDeallocEvents 192 8 ++ evs_c),
    verNeTailEnv_of_freeSuffix (freeOnlyEvs_append freeOnlyEvs_dealloc_192_8 hfree_c),
    Entails.trans (entails_replace_sub hP_c (by sep_focus) rfl)
      (Entails.trans (entails_replace_sub hrec (by sep_focus) rfl)
        (entails_replace_sub (Entails.of_eq hstack_drop2.symm) (by sep_focus) (eq_of_sep_emp (by sep_focus)))),
    hspf, htrf, hcc, hcrof, by rw [hvregs_f, hvregs_11, hvregs_cs10, hvregs_9, hvregs_cs8]⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_ver_ne_zero_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3Placed A lim ext)
    (st0 : M.σ) (hfits_m : FitsEnv M lim st0 FromMEnv)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64) (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64) (hx27_1 : s1.readReg64 .x27 = ctxPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ lsLogOff ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st0 s1 ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FromMEnv evs ∧
          (P_f ⊢ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            stageP3ErrPost_placed A lim (M.stepEvents evs st0) s0 s sf coroPtr outPtr prevStatesPtr
              (.invalidMessage .preKey .decryptionFailed)) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (fun _ _ => False) := by
  have hfits : FitsEnv M lim st0 StageP3VerNeM3Env := fitsEnv_stageP3VerNeM3Env_of_fromMEnv hfits_m
  intro R hm hL1
  have hwp : SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st0 s1 ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f => ∃ evs : List AllocEvent, FromMEnv evs ∧
        (P_f ⊢ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A lim (M.stepEvents evs st0) s0 s sf coroPtr outPtr prevStatesPtr
            (.invalidMessage .preKey .decryptionFailed)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (fun _ _ => False) := by
    have hlog_c : lsLogOff = pqLogLevelCellPlaced := rfl; refine weaken_frame_tail (Entails.of_eq hlog_c) (by sep_focus) ?_
    have hs1 := overVerNe_1e04_to_1e78_cro_placed_at_gen (M := M) (A := A) (lim := lim)
      (Qp := fun _ _ => False)
      ext hC.logClosure hC.grow hC.dropSs3 st0 (fitsS1_of_fitsM3 hfits)
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
      (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_)
    have hlog_eq : pqLogLevelCellPlaced = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
    refine weaken_frame_tail (Entails.of_eq hlog_eq) (by sep_focus) ?_
    have hstep7 := p3_err_ver_d_sessionShim_placed_wp A lim ext hC.shim st6b s6b coroPtr outPtr ctxPtr
      recG.localIk.cap 0x8000000000000006#64 (cap_ne_noneCap_of_lt hcap_lt)
      hpc6b hrun6b (by rw [hsp6b_s]; exact hsp_align) hx19_6b
    rw [hsp6b_s] at hstep7
    refine bind_sepWP_cro_frame_tail hcro6b hL6b hstep7 (by sep_focus)
      fun s7 hpc7 hrun7 hcro7 _ hregs7 => ?_
    rcases hregs7 with ⟨hsp7_6b, htr7_6b, hx0_7, hx1_7, hx19_7, hx24_7, hx25_7, hx26_7, _, _, hvregs_7⟩
    have hlog_eq2 : (lsLogFilterAddr ↦₆₄ 0#64) = lsLogOff := rfl
    refine weaken_frame_tail (Entails.of_eq hlog_eq2) (by sep_focus) ?_
    have hpack_ss :
        ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
          sessionHeap A.repAlloc recG st ⊢
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st hinl
    refine weaken_frame_tail hpack_ss (by sep_focus) ?_
    refine weaken_frame_tail (sp3e0_cell_336_entails_344 s.sp 0xffffffffffffffff#64)
      (by sep_focus) ?_
    have htail := stageP3_err_ver_tail_zero_placed_ok ext hC st6b hfits_tail
      s0 s s7 coroPtr outPtr errsPtr prevStatesPtr msgVer b_2c0 recG st
      hcro7 hpc7 hrun7 hsp7_6b hsp_align (htr7_6b.trans htr6b_0)
      hx0_7 hx1_7 hx19_7 hx24_7 hx25_7 hx26_7
    refine ret_sepWPp_frame_false htail (by sep_focus)
      fun sf _ _ _ ⟨evs2, hevs2, hP_t, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
    have hpool_eq : M.stepEvents evs2 st6b = M.stepEvents (evs1 ++ evs2) st0 := by
      dsimp only [st6b]; rw [← M.stepEvents_append]
    rw [hpool_eq] at hP_t
    have hevs_m : FromMEnv (evs1 ++ evs2) :=
      stageP3VerNeM3Env_imp_fromMEnv (evs1 ++ evs2) (stageP3VerNeM3Env_of_parts hevs1 hevs2)
    refine ⟨evs1 ++ evs2, hevs_m, ?_, hspf, htrf, hcc, hcrof, by rw [hvregs_f, hvregs_7, hvregs_6b]⟩
    unfold stageP3ErrPost_placed CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPost_placed
    dsimp only [SessionState.recordError]
    have hrr : recordResultAt (A.atState lim (M.stepEvents (evs1 ++ evs2) st0) sf) outPtr (.error (.invalidMessage .preKey .decryptionFailed)) =
        recordResultAt A.repAlloc outPtr (.error (.invalidMessage .preKey .decryptionFailed)) := rfl
    have hpl : (A.atState lim (M.stepEvents (evs1 ++ evs2) st0) sf).pool = A.pool lim (M.stepEvents (evs1 ++ evs2) st0) sf := rfl; rw [hrr, hpl]
    have hexists_errs :
        ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ⊢
          ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
            ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗
            ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 4#64
        (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64 (Entails.refl _)))
    refine Entails.trans (entails_replace_sub hP_t (by sep_focus) rfl) ?_
    exact entails_replace_sub hexists_errs (by sep_focus) (eq_of_sep_emp (by sep_focus))
  exact hwp R hm hL1

def stageP3DispatchPreZeroPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s s_pool : State)
    (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (res : Except SignalProtocolError (List (BitVec 8))) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  vecResultAt A.repAlloc (s.sp + 0x270#64) res ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ lsLogOff ∗ memRegion outPtr 48 ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st_b s_pool ∗
  stackAt s.sp growOneSpeStack

theorem postTryDecrypt_entails_s5Dispatch_zero_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (s0 s s_pool : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8) (res : Except SignalProtocolError (List (BitVec 8)))
    (G' recG : SessionGhost) (st₂ st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (coinsPost : SepProp) :
    (LsTokenInitM3 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G' st₂ ∗
      vecResultAt A.repAlloc (s.sp + 0x270#64) res ∗ protocolAddressAt A.repAlloc rem remAddrPtr ∗
      protocolAddressAt A.repAlloc loc locAddrPtr ∗ signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
      coinsPost ∗ lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool lim st_b s_pool) ∗
    (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0) ⊢
    stageP3DispatchPreZeroPlaced A lim st_b s0 s s_pool coroPtr outPtr initErrsPtr prevStatesPtr
      res b_2c0 G' recG st₂ st ∗
    genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      msgVer rem loc msgG msg coinsPost := by
  unfold stageP3Sub5ExtraPre stageP3DispatchPreZeroPlaced genP3S5PostFrame_placed
  unfold CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
    LsTokenInit LsTokenInitM3
  rw [stackAt_root_split_grow s.sp, ← memRegion344_104_240_eq s.sp]
  exact entails_replace_sub (genP3SpillAll_entails_s5 s.sp) (by sep_focus) (eq_of_sep_emp (by sep_focus))

theorem stageP3_clone_vregs_prefix_placed_steps [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (C : Crypto) (K : MlKem) (ext : String → Option (State → State))
    (hC : StageP3CalleesM3Placed A lim ext)
    (hcc : ChainClone3OkPlaced A lim ext) (hscc : SenderChainClone3OkPlaced A lim ext)
    (st_b : M.σ) (s0 s : State)
    (coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (P_extra F_frame : SepProp) (Q : State → SepProp → Prop)
    (hfits_clone : FitsEnv M lim st_b (SegCloneEnv recG st))
    (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpPollEntryPlaced + 0x1778#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hCont : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 → s1.pc = cloneExitPCPlaced st msgVer → s1.status = .Running →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      (P1 ⊢ genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b) s.sp
          (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
          (LsTokenInitM3 ∗ P_extra ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q
        (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
      (LsTokenInit ∗ genP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr
          locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ P_extra ∗ F_frame)
      Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hstep := cloneGen_vregs_placed_ok ext hC.shim hC.alloc hC.memcpy hcc hscc st_b s0 s s.sp
    (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg hfits_clone hrc_lt hsp_align hsp_root hcro hpc hrun htr
  let F : SepProp := LsTokenInitM3 ∗ P_extra ∗ F_frame
  have hP : (LsTokenInit ∗ genP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        P_extra ∗ F_frame) =
      genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ F := by
    change (LsTokenInitM3 ∗ genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        P_extra ∗ F_frame) = _
    dsimp only [F]; sep_ac_rfl
  rw [hP, sepConj_assoc] at hm
  obtain ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hent1, htr1, hcro1, hvregs1_s⟩ | ⟨_, _, _, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstep (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps', hout'⟩ := hCont s1 (P1 ∗ F) hsteps hpc1 hrun1 htr1
      (hvregs1_s.trans hvregs) hcro1 (sepConj_mono_left hent1) R hm1 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact hpanm.elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. `FitsEnv` Projections on `StageP3Env` -/

theorem fitsEnv_segClone_of_stageP3Env {M : AllocCostModel} {lim : BudgetLimits}
    {st_b : M.σ} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {rest : List (BitVec 8)}
    (hfits : FitsEnv M lim st_b (StageP3Env tdEnv recG st rem loc msgG msg msgVer rest)) :
    FitsEnv M lim st_b (SegCloneEnv recG st) := by
  intro e1 he1
  refine hfits e1 ?_
  by_cases hver : st.version = msgVer
  · simp only [StageP3Env, hver, ↓reduceIte]
    exact ⟨recG, ⟨rfl, rfl, rfl, rfl⟩, Or.inl he1⟩
  · simp only [StageP3Env, hver, ↓reduceIte]
    exact Or.inl he1

theorem fitsEnv_td_of_stageP3Env {M : AllocCostModel} {lim : BudgetLimits}
    {st_b : M.σ} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {recG G₁ : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {rest : List (BitVec 8)}
    (hver : st.version = msgVer) (hcl : CloneRel recG G₁)
    (hfits : FitsEnv M lim st_b (StageP3Env tdEnv recG st rem loc msgG msg msgVer rest)) :
    FitsEnv M lim (M.stepEvents (segCloneEvents recG st) st_b)
      (tdEnv (stageP3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)) := by
  intro e_td htd
  have hfull : StageP3Env tdEnv recG st rem loc msgG msg msgVer rest
      (segCloneEvents recG st ++ e_td) := by
    simp only [StageP3Env, hver, ↓reduceIte]
    exact ⟨G₁, hcl, Or.inr ⟨segCloneEvents recG st, e_td, rfl, rfl, Or.inl htd⟩⟩
  exact ((fitsEvents_append M lim (segCloneEvents recG st) e_td st_b).mp (hfits _ hfull)).2

theorem fitsEnv_postTd_of_stageP3Env {M : AllocCostModel} {lim : BudgetLimits}
    {st_b : M.σ} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {recG G₁ : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {rest : List (BitVec 8)} {evs_td : List AllocEvent}
    (hver : st.version = msgVer) (hcl : CloneRel recG G₁)
    (htd : tdEnv (stageP3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) evs_td)
    (hfits : FitsEnv M lim st_b (StageP3Env tdEnv recG st rem loc msgG msg msgVer rest)) :
    FitsEnv M lim (M.stepEvents evs_td (M.stepEvents (segCloneEvents recG st) st_b))
      FromVPostTdEnv := by
  intro e_post hpost
  have hfull : StageP3Env tdEnv recG st rem loc msgG msg msgVer rest
      ((segCloneEvents recG st ++ evs_td) ++ e_post) := by
    simp only [StageP3Env, hver, ↓reduceIte, List.append_assoc]
    exact ⟨G₁, hcl, Or.inr ⟨segCloneEvents recG st, evs_td ++ e_post, rfl, rfl,
      Or.inr ⟨evs_td, e_post, rfl, htd, hpost⟩⟩⟩
  rw [← M.stepEvents_append]
  exact ((fitsEvents_append M lim (segCloneEvents recG st ++ evs_td) e_post st_b).mp
    (hfits _ hfull)).2

theorem fitsEnv_fromM_of_stageP3Env {M : AllocCostModel} {lim : BudgetLimits}
    {st_b : M.σ} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {rest : List (BitVec 8)}
    (hver : st.version ≠ msgVer)
    (hfits : FitsEnv M lim st_b (StageP3Env tdEnv recG st rem loc msgG msg msgVer rest)) :
    FitsEnv M lim (M.stepEvents (segCloneEvents recG st) st_b) FromMEnv := by
  intro e_m hm
  have hfull : StageP3Env tdEnv recG st rem loc msgG msg msgVer rest
      (segCloneEvents recG st ++ e_m) := by
    simp only [StageP3Env, hver, ↓reduceIte]
    exact Or.inr ⟨segCloneEvents recG st, e_m, rfl, rfl, hm⟩
  exact ((fitsEvents_append M lim (segCloneEvents recG st) e_m st_b).mp (hfits _ hfull)).2

/-! ## 3. Top-Level Stage P3 Instantiation Theorems -/

set_option maxHeartbeats 1200000 in
theorem stageP3PrevEmptyVRegs_placed_ok [LibsignalPlacement]
    (hCallees : ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
      (ext : String → Option (State → State)),
      AllocContractsXCliPlaced A lim ext →
      subroutine_ok (dpPollProgPlaced ext) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
      StageP3CalleesM3Placed A lim ext) :
    StageP3PrevEmptyVRegsPlacedStmt := by
  intro M A lim tdEnv st_b ext C ctl K hA hcc hscc hroot hDropSS3 s0 s coroPtr ctxPtr outPtr
    initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest g recG st rem loc msgG
    msg F_frame Q hfits hinit_ne hnot_self hseeds hrc_lt hpq_lt hcro hpc hrun hsp_align hsp_root
    htr hvregs hOk hErr hVerNe
  have hC := hCallees ext hA hDropSS3
  have hfits_clone := fitsEnv_segClone_of_stageP3Env hfits
  refine stageP3_clone_vregs_prefix_placed_steps C K ext hC hcc hscc st_b
    s0 s coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    (stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0) F_frame Q
    hfits_clone hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 (SepWPp.weaken_pre
    (P' := (genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b) s.sp
        (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG
        st rem loc msgG msg s1 ∗
      (LsTokenInitM3 ∗
        stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0)) ∗ F_frame)
    (Entails.of_eq (by sep_ac_rfl)) ?_)
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostEqPlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      sepWPp_weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hclone_rel => ?_)
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_td := fitsEnv_td_of_stageP3Env hver hclone_rel hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    change SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 _ Q _
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    let F_dec : SepProp := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0
    refine SepWPp.weaken_pre (P' := (LsTokenInitM3 ∗
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A.repAlloc rem remAddrPtr ∗
        protocolAddressAt A.repAlloc loc locAddrPtr ∗
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool lim st_clone s1) ∗
        (F_dec ∗ F_frame))
      (Entails.of_eq (eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K tdEnv hroot st_clone s0 s s1
      coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest G₁ st rem loc msgG msg
      (F_dec ∗ F_frame) Q hver hfits_td hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hcro1 hpc1 hrun1 hs1_sp htr1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' evs_td hsteps12 htd_evs hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2
          hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    let st_td := M.stepEvents evs_td st_clone
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left (postTryDecrypt_entails_s5DispatchPrevEmpty_placed A lim st_td s0 s s2
          coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr g msgVer b_2c0
          (genP3S5Model C K rem loc msg rest st).1 G' recG
          (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
          (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPrePrevEmptyPlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3DispatchPrePrevEmptyPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by simpa [hres, Except.toBool] using hdec_rel
      have hfits_post := fitsEnv_postTd_of_stageP3Env hver hclone_rel htd_evs hfits
      have hvec_eq_s2 : vecResultAt (A.atState lim st_td s2) (s.sp + 0x270#64) (.error e) =
          vecResultAt A.repAlloc (s.sp + 0x270#64) (.error e) := rfl
      have hss_g_eq_s2 : sessionStateAt (A.atState lim st_td s2) (s.sp + 0xa90#64) G'
          (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
          (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hss_rec_eq_s2 : sessionStateAt (A.atState lim st_td s2) (coroPtr + 0xf8#64) recG st =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
      have hprev_eq_s2 :
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt
            (A.atState lim st_td s2) coroPtr g =
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt
            A.repAlloc coroPtr g := rfl
      have hpool_eq_s2 : (A.atState lim st_td s2).pool = A.pool lim st_td s2 := rfl
      simp only [hvec_eq_s2, hss_g_eq_s2, hss_rec_eq_s2, hprev_eq_s2, hpool_eq_s2]
      have herr := stageP3_sub5_err_prevEmpty_placed_ok ext hC.shim hC.alloc hC.dealloc hC.memcpy
        hC.grow hDropSS3 hC.logClosure hC.panic st_td s0 s2 coroPtr outPtr initErrsPtr
        hfits_post hinit_ne e he_npan b_2c0 g G' recG
        (genP3S5Model C K rem loc msg rest st).2 st hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrevEmptyM3Placed
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPrePrevEmptyM3Placed
        at herr
      have herr_post : ∀ st_e sf,
          stageP3ErrPostPrevEmptyM3Placed A lim st_e s0 s2 sf coroPtr outPtr e =
            stageP3ErrPostPrevEmpty_placed A lim st_e s0 s sf coroPtr outPtr e := by
        intro st_e sf
        unfold stageP3ErrPostPrevEmptyM3Placed stageP3ErrPostPrevEmpty_placed
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPostPrevEmptyM3Placed
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPostPrevEmpty_placed
        rw [hs2_sp]
      simp only [herr_post, hs2_sp] at herr
      simp only [hvec_eq_s2, hss_g_eq_s2, hss_rec_eq_s2, hprev_eq_s2, hpool_eq_s2] at herr
      apply sepWPp_lift_false_qp; apply sepWPp_frame_false_qp
      refine ret_sepWPp_frame_false herr (by sep_focus)
        fun sf _ _ _ ⟨evs_err, herr_evs, hPf_err, hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      let evs_tot := segCloneEvents recG st ++ (evs_td ++ evs_err)
      have hevs_tot : StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs_tot :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_err, rfl, rfl,
          Or.inr ⟨evs_td, evs_err, rfl, htd_evs, herr_evs⟩⟩
      have hstep_tot : M.stepEvents evs_err st_td = M.stepEvents evs_tot st_b := by
        dsimp only [st_td, st_clone, evs_tot]; simp only [← M.stepEvents_append, List.append_assoc]
      rw [hstep_tot] at hPf_err
      refine hErr G₁ G' evs_tot e sf _ hver hclone_rel hdec_false hevs_tot hres he_npan ?_
        hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      unfold genP3S5PostFrame_placed
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
        genP3S5PostFramePlaced
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3S5PostFramePlaced
        LsTokenInit LsTokenInitM3
      exact Entails.trans (entails_replace_sub hPf_err (by sep_focus) rfl)
        (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by simpa [hres, Except.toBool] using hdec_rel
      have hstack_set : stackAt s.sp growOneSpeStack =
          memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hvec_eq_s2 : vecResultAt (A.atState lim st_td s2) (s.sp + 0x270#64) (.ok pt) =
          vecResultAt A.repAlloc (s.sp + 0x270#64) (.ok pt) := rfl
      have hss_g_eq_s2 : sessionStateAt (A.atState lim st_td s2) (s.sp + 0xa90#64) G'
          (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
          (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hss_rec_eq_s2 : sessionStateAt (A.atState lim st_td s2) (coroPtr + 0xf8#64) recG st =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
      have hprev_eq_s2 :
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt
            (A.atState lim st_td s2) coroPtr g =
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt
            A.repAlloc coroPtr g := rfl
      have hpool_eq_s2 : (A.atState lim st_td s2).pool = A.pool lim st_td s2 := rfl
      simp only [hvec_eq_s2, hss_g_eq_s2, hss_rec_eq_s2, hprev_eq_s2, hpool_eq_s2]
      have hok := stageP3_sub5_decResult_placed_ok ext hC.memcpy hC.setState st_td s0 s2
        coroPtr outPtr pt G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_false_steps_framed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨evs_free, ptCap, ptPtr, hevs_free,
          hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      let evs_ok := segCloneEvents recG st ++ (evs_td ++ evs_free)
      have hevs_ok : StageP3OkPrefixEnv tdEnv recG G₁ st rem loc msgG msg rest evs_ok :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_free, rfl, rfl,
          Or.inr ⟨evs_td, evs_free, rfl, htd_evs, hevs_free⟩⟩
      have hstep_ok : M.stepEvents evs_free st_td = M.stepEvents evs_ok st_b := by
        dsimp only [st_td, st_clone, evs_ok]; simp only [← M.stepEvents_append, List.append_assoc]
      rw [hstep_ok] at hPs'
      refine hOk G₁ G' evs_ok pt ptCap ptPtr s' _ hver hclone_rel hdec_true hevs_ok hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2) hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2)
        hx28' hcro' ?_
      unfold stageP3DispatchOkMidPrevEmpty_placed
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3DispatchOkMidPrevEmpty_placed
        genP3S5PostFrame_placed
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
        genP3S5PostFramePlaced
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3S5PostFramePlaced
        LsTokenInit LsTokenInitM3
      rw [hstack_set]
      have hlive_s' :
          (if ptCap = 0#64 then emp
           else (A.atState lim (M.stepEvents evs_ok st_b) s').live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) =
          (if ptCap = 0#64 then emp
           else A.live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) := rfl
      have hss_s' :
          sessionStateAt (A.atState lim (M.stepEvents evs_ok st_b) s') (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hprev_s' :
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.prevSessionsEmptyAt
            (A.atState lim (M.stepEvents evs_ok st_b) s') coroPtr g =
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt
            A.repAlloc coroPtr g := rfl
      have hpool_s' :
          (A.atState lim (M.stepEvents evs_ok st_b) s').pool =
          A.pool lim (M.stepEvents evs_ok st_b) s' := rfl
      rw [hlive_s', hss_s', hprev_s', hpool_s']
      exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_false_qp; apply sepWPp_frame_false_qp
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostNePlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
      stageP3Sub5ExtraPrePrevEmpty
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      sepWPp_weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ => ?_)
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_fromM := fitsEnv_fromM_of_stageP3Env hver hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    refine sepWPp_weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq (stackAt_root_split_grow s.sp)) (by sep_focus)
        (sepWPp_weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_))
    have hprev_m : CryptoVerification.SignalSession.Cli.RunProofs.Poll.prevSessionsEmptyAt A.repAlloc coroPtr g =
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt A.repAlloc coroPtr g := rfl
    rw [hprev_m]
    have hver_ne := stageP3_ver_ne_prevEmpty_sessionShim_placed_ok ext hC.shim hC.alloc hC.dealloc
      hC.grow hDropSS3 hC.logClosure hC.panic st_clone s0 s s1 coroPtr ctxPtr outPtr initErrsPtr
      hfits_fromM hinit_ne msgVer b_2c0 g G₁ recG st
      hcro1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine ret_sepWPp_frame_false hver_ne (by sep_focus)
      fun sf _ _ _ ⟨evs_vn, hvn_evs, hPf_vn, hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    let evs_vn_tot := segCloneEvents recG st ++ evs_vn
    have hevs_vn_tot : StageP3VerNeEnv recG st evs_vn_tot :=
      Or.inr ⟨segCloneEvents recG st, evs_vn, rfl, rfl, hvn_evs⟩
    have hstep_vn : M.stepEvents evs_vn st_clone = M.stepEvents evs_vn_tot st_b := by
      dsimp only [st_clone, evs_vn_tot]; rw [← M.stepEvents_append]
    rw [hstep_vn] at hPf_vn
    have herr_eq :
        LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlacedBudgetAux.stageP3ErrPostPrevEmptyM3Placed
          A lim (M.stepEvents evs_vn_tot st_b) s0 s sf coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed) =
        stageP3ErrPostPrevEmpty_placed A lim (M.stepEvents evs_vn_tot st_b) s0 s sf coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed) := rfl
    rw [herr_eq] at hPf_vn
    refine hVerNe evs_vn_tot sf _ hver hevs_vn_tot ?_ hspf htrf hcc_f
      (hvregsf_1.trans hvregs1) hcrof
    unfold genP3S5PostFrame_placed
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
      LsTokenInit LsTokenInitM3
    exact Entails.trans (sepConj_mono_left hPf_vn) (Entails.of_eq (eq_of_sep_emp (by sep_focus)))

set_option maxHeartbeats 1200000 in
theorem stageP3GenStepsVRegs_placed_ok [LibsignalPlacement]
    (hCallees : ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
      (ext : String → Option (State → State)),
      AllocContractsXCliPlaced A lim ext → StageP3CalleesM3Placed A lim ext) :
    StageP3GenStepsVRegsPlacedStmt := by
  intro M A lim tdEnv st_b ext C ctl K hA hcc hscc hroot s0 s coroPtr ctxPtr outPtr initErrsPtr
    prevStatesPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest recG st rem loc msgG
    msg F_frame Q hfits hinit_ne hnot_self hseeds hrc_lt hpq_lt hcro hpc hrun hsp_align hsp_root
    htr hvregs hOk hErr hVerNe
  have hC := hCallees ext hA
  have hfits_clone := fitsEnv_segClone_of_stageP3Env hfits
  refine stageP3_clone_vregs_prefix_placed_steps C K ext hC hcc hscc st_b
    s0 s coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    (stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0) F_frame Q
    hfits_clone hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 (SepWPp.weaken_pre
    (P' := (genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b) s.sp
        (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG
        st rem loc msgG msg s1 ∗
      (LsTokenInitM3 ∗
        stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0)) ∗ F_frame)
    (Entails.of_eq (by sep_ac_rfl)) ?_)
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostEqPlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      sepWPp_weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hclone_rel => ?_)
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_td := fitsEnv_td_of_stageP3Env hver hclone_rel hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    change SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 _ Q _
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    let F_dec : SepProp := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0
    refine SepWPp.weaken_pre (P' := (LsTokenInitM3 ∗
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A.repAlloc rem remAddrPtr ∗
        protocolAddressAt A.repAlloc loc locAddrPtr ∗
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool lim st_clone s1) ∗
        (F_dec ∗ F_frame))
      (Entails.of_eq (eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K tdEnv hroot st_clone s0 s s1
      coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest G₁ st rem loc msgG msg
      (F_dec ∗ F_frame) Q hver hfits_td hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hcro1 hpc1 hrun1 hs1_sp htr1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' evs_td hsteps12 htd_evs hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2
          hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    let st_td := M.stepEvents evs_td st_clone
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left (postTryDecrypt_entails_s5Dispatch_zero_placed A lim st_td s0 s s2
          coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr remAddrPtr locAddrPtr whisperMsgPtr
          msgVer b_2c0 (genP3S5Model C K rem loc msg rest st).1 G' recG
          (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
          (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPreZeroPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by simpa [hres, Except.toBool] using hdec_rel
      have hfits_post := fitsEnv_postTd_of_stageP3Env hver hclone_rel htd_evs hfits
      have herr := stageP3_sub5_err_zero_placed_ok ext hC st_td s0 s2 coroPtr outPtr initErrsPtr
        prevStatesPtr hfits_post hinit_ne e he_npan b_2c0 G' recG
        (genP3S5Model C K rem loc msg rest st).2 st hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPreZeroPlaced at herr
      have herr_post : ∀ st_e sf,
          stageP3ErrPost_placed A lim st_e s0 s2 sf coroPtr outPtr prevStatesPtr e =
            stageP3ErrPost_placed A lim st_e s0 s sf coroPtr outPtr prevStatesPtr e := by
        intro st_e sf
        unfold stageP3ErrPost_placed
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPost_placed
        rw [hs2_sp]
      simp only [herr_post, hs2_sp] at herr
      apply sepWPp_lift_false_qp; apply sepWPp_frame_false_qp
      refine ret_sepWPp_frame_false herr (by sep_focus)
        fun sf _ _ _ ⟨evs_err, herr_evs, hPf_err, hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      let evs_tot := segCloneEvents recG st ++ (evs_td ++ evs_err)
      have hevs_tot : StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs_tot :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_err, rfl, rfl,
          Or.inr ⟨evs_td, evs_err, rfl, htd_evs, herr_evs⟩⟩
      have hstep_tot : M.stepEvents evs_err st_td = M.stepEvents evs_tot st_b := by
        dsimp only [st_td, st_clone, evs_tot]; simp only [← M.stepEvents_append, List.append_assoc]
      rw [hstep_tot] at hPf_err
      refine hErr G₁ G' evs_tot e sf _ hver hclone_rel hdec_false hevs_tot hres he_npan ?_
        hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      unfold genP3S5PostFrame_placed
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
        LsTokenInit
      exact Entails.trans (entails_replace_sub hPf_err (by sep_focus) rfl)
        (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by simpa [hres, Except.toBool] using hdec_rel
      have hstack_set : stackAt s.sp growOneSpeStack =
          memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_placed_ok ext hC.memcpy hC.setState st_td s0 s2
        coroPtr outPtr pt G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_false_steps_framed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨evs_free, ptCap, ptPtr, hevs_free,
          hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      let evs_ok := segCloneEvents recG st ++ (evs_td ++ evs_free)
      have hevs_ok : StageP3OkPrefixEnv tdEnv recG G₁ st rem loc msgG msg rest evs_ok :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_free, rfl, rfl,
          Or.inr ⟨evs_td, evs_free, rfl, htd_evs, hevs_free⟩⟩
      have hstep_ok : M.stepEvents evs_free st_td = M.stepEvents evs_ok st_b := by
        dsimp only [st_td, st_clone, evs_ok]; simp only [← M.stepEvents_append, List.append_assoc]
      rw [hstep_ok] at hPs'
      refine hOk G₁ G' evs_ok pt ptCap ptPtr s' _ hver hclone_rel hdec_true hevs_ok hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2) hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2)
        hx28' hcro' ?_
      unfold stageP3DispatchOkMid_placed
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3DispatchOkMid_placed
        genP3S5PostFrame_placed
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
        LsTokenInit
      rw [hstack_set]
      have hlive_s' :
          (if ptCap = 0#64 then emp
           else (A.atState lim (M.stepEvents evs_ok st_b) s').live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) =
          (if ptCap = 0#64 then emp
           else A.live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) := rfl
      have hss_s' :
          sessionStateAt (A.atState lim (M.stepEvents evs_ok st_b) s') (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hpool_s' :
          (A.atState lim (M.stepEvents evs_ok st_b) s').pool =
          A.pool lim (M.stepEvents evs_ok st_b) s' := rfl
      rw [hlive_s', hss_s', hpool_s']
      exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_false_qp; apply sepWPp_frame_false_qp
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostNePlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
      stageP3Sub5ExtraPre
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      sepWPp_weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ => ?_)
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_fromM := fitsEnv_fromM_of_stageP3Env hver hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    refine sepWPp_weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq (stackAt_root_split_grow s.sp)) (by sep_focus)
        (sepWPp_weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_))
    have hver_ne := stageP3_ver_ne_zero_placed_ok ext hC st_clone hfits_fromM s0 s s1 coroPtr ctxPtr
      outPtr initErrsPtr prevStatesPtr hinit_ne msgVer b_2c0 G₁ recG st
      hcro1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine ret_sepWPp_frame_false hver_ne (by sep_focus)
      fun sf _ _ _ ⟨evs_vn, hvn_evs, hPf_vn, hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    let evs_vn_tot := segCloneEvents recG st ++ evs_vn
    have hevs_vn_tot : StageP3VerNeEnv recG st evs_vn_tot :=
      Or.inr ⟨segCloneEvents recG st, evs_vn, rfl, rfl, hvn_evs⟩
    have hstep_vn : M.stepEvents evs_vn st_clone = M.stepEvents evs_vn_tot st_b := by
      dsimp only [st_clone, evs_vn_tot]; rw [← M.stepEvents_append]
    rw [hstep_vn] at hPf_vn
    refine hVerNe evs_vn_tot sf _ hver hevs_vn_tot ?_ hspf htrf hcc_f
      (hvregsf_1.trans hvregs1) hcrof
    unfold genP3S5PostFrame_placed
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
      LsTokenInit LsTokenInitM3
    exact Entails.trans (sepConj_mono_left hPf_vn) (Entails.of_eq (eq_of_sep_emp (by sep_focus)))

theorem stageP3Prev1VRegs_placed_of_verNeAt [LibsignalPlacement]
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
    StageP3Prev1VRegsAtPlacedStmt A lim tdEnv PrevEncOK :=
  LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget.stageP3Prev1D3_placed_of_verNeAt
    hLog519 hVerNeAt

theorem cliVerNe1e04_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (hLog519 : subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)) :
    OverVerNe1e04CliAtPlacedBody A lim OverPrevEncOK VerNeTopEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget.cliVerNe1e04_placed_ok
    mmpl gh W hG hLog519

theorem stageP3_prev1_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (hLogClosure : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim gh →
      subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 519)
        (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)) :
    StageP3Prev1VRegsPlacedStmt A lim tdEnv :=
  LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget.stageP3_prev1_d3_placed_ok
    hLogClosure

/-! ## 4. `LibsignalFullPlacement` / `LibsignalFrozen` Variants (Block `519` Discharged Internally) -/

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux (
  StageP3CalleesM3BasePlaced StageP3VerNePrevEmptySessionShimFrozenPlacedStmt
  stageP3_sub5_err_zero_full_placed_ok stageP3_ver_ne_prevEmpty_sessionShim_full_placed_ok
)

section FrozenVariants

open CryptoVerification (
  IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalHooks
  libsignalFrozen_of_keepsFrozen lsHandleErrorSym lsMemcpySym
  lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsRustReallocSym
  ls_hook_ok_ultra_of_mem
)
open CryptoVerification.CliHandshake.RespClosurePlaced (instIsLsBlockProg_518)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32 SpqrModel extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (
  lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli
)
open CryptoVerification.SignalSession.Cli.RunGlue (cliExternsPlaced_row cliGhostExterns_shim)
open CryptoVerification.SignalSession.Cli.Slots (
  cliGhostExterns_panic_handle_error cliGhostExterns_sat_of_cliExternsPlaced
)
open LibsignalBinary.Heap (
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  pollTryDecryptM3PlacedSpecP pollTryDecryptM3PlacedSpecTPTight
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudget (
  stageP3_sub5_err_prevEmpty_full_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget (
  OverVerNe1e04CliAtFrozenPlacedBody overVerNe1e04CliAtFrozenPlacedBody_of_hooks_chain5
  stageP3Gen_prev1_vregs_at_full_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlacedBudget (
  chainMerge5CroPlacedOkExt_cli
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget (
  overVerNe_1e04_to_1e78_frozen_placed_at_gen
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget (
  cliDropSessionStructure4_placed_ok_at cliGrowOneSpe_518_placed_ok cliSetSessionState_518_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  StageP3Prev1VRegsAtFrozenPlacedStmt StageP3Prev1VRegsFrozenPlacedStmt
  overPollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3GenStepsVRegsFrozenPlacedStmt StageP3PrevEmptyVRegsFrozenPlacedStmt
  pollTryDecryptPlacedSpecP
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux (
  StageP3CalleesM3BasePlaced StageP3VerNePrevEmptySessionShimFrozenPlacedStmt
  lscro_of_frozen_aux stageP3_sub5_err_zero_full_placed_ok
  stageP3_ver_ne_prevEmpty_sessionShim_full_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_framelessMemcpy_budget_sat cliExternsPlaced_realloc_budget_sat
  cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_sessionMemmove_budget_sat
  cliExternsPlaced_shim_budget_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)

set_option maxHeartbeats 1200000 in
private theorem stageP3_err_ver_tail_zero_base_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3BasePlaced A lim ext)
    (st0 : M.σ) (hfits : FitsEnv M lim st0 VerNeTailEnv)
    (s0 s s7 : State) (coroPtr outPtr errsPtr prevStatesPtr : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro7 : LibsignalCodeRoLoaded lsmpl s7.mem)
    (hpc7 : s7.pc = dpClosureEntryVerPlaced + 0x33b0#64) (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr7 : s7.trace = s0.trace)
    (hx0_7 : s7.readReg64 .x0 = 17#64) (hx1_7 : s7.readReg64 .x1 = 1#64)
    (hx19_7 : s7.readReg64 .x19 = coroPtr) (hx24_7 : s7.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_7 : s7.readReg64 .x25 = s.sp + 0x210#64) (hx26_7 : s7.readReg64 .x26 = outPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
       memRegion (errsPtr + 12#64) 36 ∗ memRegion (errsPtr + 48#64) 144 ∗ A.live errsPtr 192 8 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st0 s7 ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          VerNeTailEnv evs ∧
          (P_f ⊢ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
            memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            recordResultAt A.repAlloc outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
            memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s.sp growOneSpeStack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s7)
      (fun _ _ => False) := by
  have hstack_alloc := stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine sepWPp_weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have halloc17 := p3_alloc_33b0_zero_placed_ok (Qp := fun _ _ => False) ext hC.alloc st0 s7 emp
    (fitsAlloc17_of_fitsEnv hfits) hcro7 hpc7 hrun7 (by rw [hs7_sp]; exact hsp_align) hx0_7 hx1_7
  rw [sepConj_emp, hs7_sp] at halloc17
  refine bind_sepWPp_frame_false halloc17 (by sep_focus)
    fun s8 P_m8 hpc8 hrun8 ⟨hP8, hdf_ne, hsp8_7, htr8_7, hcs8, hcro8⟩ => ?_
  rw [sepConj_emp] at hP8
  let st8 := M.stepEvents (rustAllocEvents 17 1) st0
  refine sepWPp_weaken_frame hP8 (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq (memRegion_17_split_eq (s8.readReg64 .x0))) (by sep_focus) ?_))
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_df10 => SepWPp.exists_elim fun u_df8 => SepWPp.exists_elim fun u_df0 =>
    sepWPp_weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x270#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_270 => SepWPp.exists_elim fun u_278 => SepWPp.exists_elim fun u_280 =>
    SepWPp.exists_elim fun u_288 => SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 =>
    sepWPp_weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, _, _, hvregs_cs8⟩
  refine intro_lsro_decryptionFailed_err hcro8 ?_
  have hstep9 := p3_err_ver_e_placed_wp A lim ext st8 s8 coroPtr (s8.readReg64 .x0) errsPtr
    0x6974707972636564#64 0x656c696166206e6f#64 u_df0 u_df8 u_270 u_278 u_280 u_288 u_df10 (w3.extractLsb' 0 8)
    hdf_ne hpc8 hrun8 (by rw [hsp8_7]; exact hsp_align) rfl (hx19_cs8.trans hx19_7)
  rw [hsp8_7] at hstep9
  refine bind_sepWP_lscro_frame_err hcro8 hstep9 (by sep_focus) fun s9 hpc9 hrun9 hcro9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx19_9, hx21_9, hx22_9, hx23_9, hx24_9, hx25_9, hx26_9, _, hx28_9, _, hx30_9, hvregs_9⟩
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp.drop_frame
    (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64)) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s8.readReg64 .x0))) (by sep_focus) ?_)
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  have hstack_spe := stackAt_split_bottom s.sp dropSpeStack 480 (by decide)
  refine sepWPp_weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq hstack_spe) (by sep_focus) ?_)
  refine call_lscl_ro_nopanic_err (spec := dropSpe2VerSpec M A lim) (x := (errsPtr, msgVer, st8))
    (φ := s9.readReg64 .x0 = errsPtr)
    (T := (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
          memRegion (errsPtr + 12#64) 36 ∗ A.pool lim st8 s9 ∗ stackAt s.sp dropSpeStack)
    hcro9 (drop_spe2_ver_placed_ok_at (M := M) (A := A) (lim := lim)) hpc9 hrun9
    (by simpa only [State.spAligned, hsp9_8] using hsp_align) hx30_9
    (by dsimp only [dropSpe2VerSpec]; rw [hsp9_8]) hx0_9 (by sep_focus)
    (hnext := fun s10 hpc10 hrun10 hsp10_9 _ hcs10 hcro10 => ?_)
  dsimp only [dropSpe2VerSpec]; rw [hsp9_8, sepConj_assoc]
  refine SepWPp.pure_elim fun htr10_9 =>
    sepWPp_weaken_frame (Entails.of_eq (errs48_144_join errsPtr)) (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq hstack_spe.symm) (by sep_focus)
        (sepWPp_weaken_frame (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_))
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => sepWPp_weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_)
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) 17#64 (s8.readReg64 .x0) 17#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine sepWPp_weaken_frame (Entails.of_eq hrepack278) (by sep_focus)
    (sepWPp_weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun u_250 =>
    sepWPp_weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 => SepWPp.exists_elim fun u_380 =>
    SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 =>
    sepWPp_weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp10_s : s10.sp = s.sp := hsp10_9.trans hsp9_8
  rcases hcs10 with ⟨hx19_cs10, _, hx21_cs10, hx22_cs10, hx23_cs10, hx24_cs10, hx25_cs10, hx26_cs10, _, hx28_cs10, _, hvregs_cs10⟩
  have hstep11 := p3_err_ver_f_placed_wp ext hC.dealloc st8 s10 coroPtr errsPtr recG.localIk.cap
    ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)
    w3' w4 u_250 u_258 u_370 u_378 u_384 u_38c
    ((17#64 : BitVec 64).extractLsb' 0 32) ((17#64 : BitVec 64).extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc10 hrun10 (by rw [hsp10_s]; exact hsp_align)
    (hx19_cs10.trans hx19_9) (hx21_cs10.trans hx21_9) (hx22_cs10.trans hx22_9) (hx23_cs10.trans hx23_9)
    (by rw [hx24_cs10, hx24_9, hx24_cs8, hx24_7, hsp10_s])
    (by rw [hx25_cs10, hx25_9, hx25_cs8, hx25_7, hsp10_s]) (hx28_cs10.trans hx28_9)
  rw [hsp10_s] at hstep11
  refine bind_sepWP_lscro_frame_err hcro10 hstep11 (by sep_focus) fun s11 hpc11 hrun11 hcro11 hregs11 => ?_
  rcases hregs11 with ⟨hsp11_10, htr11_10, hx0_11, hx19_11, hx22_11, _, hx25_11, hx26_11, _, hx28_11, _, hx30_11, hvregs_11⟩
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A.repAlloc recG st ⊢ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st hinl
  have hfold250 : ((s.sp + 0x250#64) ↦₆₄ ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ (17#64 : BitVec 64).extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion20_fold (s.sp + 0x250#64)
      ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
      ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32) ((17#64 : BitVec 64).extractLsb' 32 32)
  have hstack_drop2 := stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  let st11 := M.stepEvents (rustDeallocEvents 192 8) st8
  refine sepWPp_weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus)
    (sepWPp_weaken_frame hpack_ss (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus)
        (sepWPp_weaken_frame
          (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000018#64 17#64 (s8.readReg64 .x0) 17#64 w3' w4) (by sep_focus)
          (sepWPp_weaken_frame hfold250 (by sep_focus)
            (sepWPp_weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_)))))
  have hcommon := stageP3_err_tail_common_zero_placed_ok (Qp := fun _ _ => False) ext hC.dropSs3 st11
    s0 s11 coroPtr outPtr 0x8000000000000018#64 prevStatesPtr 17#64 (s8.readReg64 .x0) 17#64 w3' w4 b_2c0 recG st
    hcro11 hpc11 hrun11 (by rw [hsp11_10]; exact hsp_align) (htr11_10.trans (htr10_9.trans (htr9_8.trans (htr8_7.trans htr7))))
    hx0_11 hx19_11 hx22_11 (by rw [hx25_11, hsp11_10])
    (hx26_11.trans (hx26_cs10.trans (hx26_9.trans (hx26_cs8.trans hx26_7)))) hx28_11 hx30_11
  rw [hsp11_10] at hcommon
  refine ret_sepWPp_frame_false hcommon (by sep_focus)
    fun sf _ _ _ ⟨evs_c, hfree_c, hP_c, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A.repAlloc outPtr (s8.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  rw [RustCliAllocBudget.repAlloc_live] at hrec
  have hpool_eq :
      M.stepEvents evs_c st11 =
        M.stepEvents (rustAllocEvents 17 1 ++ (rustDeallocEvents 192 8 ++ evs_c)) st0 := by
    dsimp only [st11, st8]; simp only [← M.stepEvents_append, List.append_assoc]
  rw [hpool_eq] at hP_c
  refine ⟨rustAllocEvents 17 1 ++ (rustDeallocEvents 192 8 ++ evs_c),
    verNeTailEnv_of_freeSuffix (freeOnlyEvs_append freeOnlyEvs_dealloc_192_8 hfree_c),
    Entails.trans (entails_replace_sub hP_c (by sep_focus) rfl)
      (Entails.trans (entails_replace_sub hrec (by sep_focus) rfl)
        (entails_replace_sub (Entails.of_eq hstack_drop2.symm) (by sep_focus) (eq_of_sep_emp (by sep_focus)))),
    hspf, htrf, hcc, hcrof, by rw [hvregs_f, hvregs_11, hvregs_cs10, hvregs_9, hvregs_cs8]⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_ver_ne_zero_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3BasePlaced A lim ext)
    (st0 : M.σ) (hfits_m : FitsEnv M lim st0 FromMEnv)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hfr1 : LibsignalFrozen lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64) (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64) (hx27_1 : s1.readReg64 .x27 = ctxPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ lsLogOff ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st0 s1 ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FromMEnv evs ∧
          (P_f ⊢ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            stageP3ErrPost_placed A lim (M.stepEvents evs st0) s0 s sf coroPtr outPtr prevStatesPtr
              (.invalidMessage .preKey .decryptionFailed)) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (fun _ _ => False) := by
  have hfits : FitsEnv M lim st0 StageP3VerNeM3Env := fitsEnv_stageP3VerNeM3Env_of_fromMEnv hfits_m
  intro R hm hL1
  have hwp : SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st0 s1 ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f => ∃ evs : List AllocEvent, FromMEnv evs ∧
        (P_f ⊢ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A lim (M.stepEvents evs st0) s0 s sf coroPtr outPtr prevStatesPtr
            (.invalidMessage .preKey .decryptionFailed)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (fun _ _ => False) := by
    have hlog_c : lsLogOff = pqLogLevelCellPlaced := rfl; refine weaken_frame_tail (Entails.of_eq hlog_c) (by sep_focus) ?_
    have hs1 := overVerNe_1e04_to_1e78_frozen_placed_at_gen (M := M) (A := A) (lim := lim)
      (Qp := fun _ _ => False)
      ext hC.grow hC.dropSs3 st0 (fitsS1_of_fitsM3 hfits)
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
      (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_)
    have hlog_eq : pqLogLevelCellPlaced = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
    refine weaken_frame_tail (Entails.of_eq hlog_eq) (by sep_focus) ?_
    have hstep7 := p3_err_ver_d_sessionShim_placed_wp A lim ext hC.shim st6b s6b coroPtr outPtr ctxPtr
      recG.localIk.cap 0x8000000000000006#64 (cap_ne_noneCap_of_lt hcap_lt)
      hpc6b hrun6b (by rw [hsp6b_s]; exact hsp_align) hx19_6b
    rw [hsp6b_s] at hstep7
    refine bind_sepWP_cro_frame_tail hcro6b hL6b hstep7 (by sep_focus)
      fun s7 hpc7 hrun7 hcro7 _ hregs7 => ?_
    rcases hregs7 with ⟨hsp7_6b, htr7_6b, hx0_7, hx1_7, hx19_7, hx24_7, hx25_7, hx26_7, _, _, hvregs_7⟩
    have hlog_eq2 : (lsLogFilterAddr ↦₆₄ 0#64) = lsLogOff := rfl
    refine weaken_frame_tail (Entails.of_eq hlog_eq2) (by sep_focus) ?_
    have hpack_ss :
        ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
          sessionHeap A.repAlloc recG st ⊢
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st hinl
    refine weaken_frame_tail hpack_ss (by sep_focus) ?_
    refine weaken_frame_tail (sp3e0_cell_336_entails_344 s.sp 0xffffffffffffffff#64)
      (by sep_focus) ?_
    have htail := stageP3_err_ver_tail_zero_base_placed_ok ext hC st6b hfits_tail
      s0 s s7 coroPtr outPtr errsPtr prevStatesPtr msgVer b_2c0 recG st
      hcro7 hpc7 hrun7 hsp7_6b hsp_align (htr7_6b.trans htr6b_0)
      hx0_7 hx1_7 hx19_7 hx24_7 hx25_7 hx26_7
    refine ret_sepWPp_frame_false htail (by sep_focus)
      fun sf _ _ _ ⟨evs2, hevs2, hP_t, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
    have hpool_eq : M.stepEvents evs2 st6b = M.stepEvents (evs1 ++ evs2) st0 := by
      dsimp only [st6b]; rw [← M.stepEvents_append]
    rw [hpool_eq] at hP_t
    have hevs_m : FromMEnv (evs1 ++ evs2) :=
      stageP3VerNeM3Env_imp_fromMEnv (evs1 ++ evs2) (stageP3VerNeM3Env_of_parts hevs1 hevs2)
    refine ⟨evs1 ++ evs2, hevs_m, ?_, hspf, htrf, hcc, hcrof, by rw [hvregs_f, hvregs_7, hvregs_6b]⟩
    unfold stageP3ErrPost_placed CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPost_placed
    dsimp only [SessionState.recordError]
    have hrr : recordResultAt (A.atState lim (M.stepEvents (evs1 ++ evs2) st0) sf) outPtr (.error (.invalidMessage .preKey .decryptionFailed)) =
        recordResultAt A.repAlloc outPtr (.error (.invalidMessage .preKey .decryptionFailed)) := rfl
    have hpl : (A.atState lim (M.stepEvents (evs1 ++ evs2) st0) sf).pool = A.pool lim (M.stepEvents (evs1 ++ evs2) st0) sf := rfl; rw [hrr, hpl]
    have hexists_errs :
        ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ⊢
          ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
            ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗
            ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 4#64
        (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64 (Entails.refl _)))
    refine Entails.trans (entails_replace_sub hP_t (by sep_focus) rfl) ?_
    exact entails_replace_sub hexists_errs (by sep_focus) (eq_of_sep_emp (by sep_focus))
  exact hwp R hm hL1

theorem stageP3_clone_vregs_prefix_base_placed_steps [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (C : Crypto) (K : MlKem) (ext : String → Option (State → State))
    (hC : StageP3CalleesM3BasePlaced A lim ext)
    (hcc : ChainClone3OkPlaced A lim ext) (hscc : SenderChainClone3OkPlaced A lim ext)
    (st_b : M.σ) (s0 s : State)
    (coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (P_extra F_frame : SepProp) (Q : State → SepProp → Prop)
    (hfits_clone : FitsEnv M lim st_b (SegCloneEnv recG st))
    (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpPollEntryPlaced + 0x1778#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hCont : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 → s1.pc = cloneExitPCPlaced st msgVer → s1.status = .Running →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      (P1 ⊢ genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b) s.sp
          (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
          (LsTokenInitM3 ∗ P_extra ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q
        (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
      (LsTokenInit ∗ genP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr
          locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ P_extra ∗ F_frame)
      Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hstep := cloneGen_vregs_placed_ok ext hC.shim hC.alloc hC.memcpy hcc hscc st_b s0 s s.sp
    (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg hfits_clone hrc_lt hsp_align hsp_root hcro hpc hrun htr
  let F : SepProp := LsTokenInitM3 ∗ P_extra ∗ F_frame
  have hP : (LsTokenInit ∗ genP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        P_extra ∗ F_frame) =
      genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ F := by
    change (LsTokenInitM3 ∗ genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        P_extra ∗ F_frame) = _
    dsimp only [F]; sep_ac_rfl
  rw [hP, sepConj_assoc] at hm
  obtain ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hent1, htr1, hcro1, hvregs1_s⟩ | ⟨_, _, _, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstep (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps', hout'⟩ := hCont s1 (P1 ∗ F) hsteps hpc1 hrun1 htr1
      (hvregs1_s.trans hvregs) hcro1 (sepConj_mono_left hent1) R hm1 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact hpanm.elim
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1200000 in
theorem stageP3PrevEmptyVRegs_of_base_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (st_b : M.σ) (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : MlKem)
    (hC : StageP3CalleesM3BasePlaced A lim ext)
    (hcc : ChainClone3OkPlaced A lim ext) (hscc : SenderChainClone3OkPlaced A lim ext)
    (hroot : subroutine_ok (dpPollProgPlaced ext) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv)))
    (hDropSS3 : subroutine_ok (dpPollProgPlaced ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim))) :
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b (StageP3Env tdEnv recG st rem loc msgG msg msgVer rest) →
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      LibsignalFrozen lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced ext) s s' → s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running → s'.sp = s.sp → s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrevEmpty_placed A lim (M.stepEvents evs_p3 st_b) s0 s s'
            coroPtr outPtr initErrsPtr ptCap ptPtr g pt b_2c0 G'
            (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr outPtr e ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_p3 : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNeEnv recG st evs_p3 →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          genP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0) := by
  intro s0 s coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr cur
    msgVer b_2c0 rest g recG st rem loc msgG msg F_frame Q hfits
    hinit_ne hnot_self hseeds hrc_lt hpq_lt hfr hpc hrun hsp_align hsp_root htr hvregs hOk hErr hVerNe
  have hcro : LibsignalCodeRoLoaded lsmpl s.mem := lscro_of_frozen_aux hfr
  have hfits_clone := fitsEnv_segClone_of_stageP3Env hfits
  refine stageP3_clone_vregs_prefix_base_placed_steps C K ext hC hcc hscc st_b
    s0 s coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    (stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0) F_frame Q
    hfits_clone hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  have hfr1 : LibsignalFrozen lsmpl s1.mem := libsignalFrozen_of_keepsFrozen hfr hsteps01.keepsFrozen
  refine SepWPp.weaken_pre hent1 (SepWPp.weaken_pre
    (P' := (genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b) s.sp
        (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG
        st rem loc msgG msg s1 ∗
      (LsTokenInitM3 ∗
        stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0)) ∗ F_frame)
    (Entails.of_eq (by sep_ac_rfl)) ?_)
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostEqPlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      sepWPp_weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hclone_rel => ?_)
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_td := fitsEnv_td_of_stageP3Env hver hclone_rel hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    change SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 _ Q _
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    let F_dec : SepProp := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0
    refine SepWPp.weaken_pre (P' := (LsTokenInitM3 ∗
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A.repAlloc rem remAddrPtr ∗
        protocolAddressAt A.repAlloc loc locAddrPtr ∗
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool lim st_clone s1) ∗
        (F_dec ∗ F_frame))
      (Entails.of_eq (eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K tdEnv hroot st_clone s0 s s1
      coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest G₁ st rem loc msgG msg
      (F_dec ∗ F_frame) Q hver hfits_td hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hcro1 hpc1 hrun1 hs1_sp htr1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' evs_td hsteps12 htd_evs hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2
          hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    have hfr2 : LibsignalFrozen lsmpl s2.mem := libsignalFrozen_of_keepsFrozen hfr hsteps02.keepsFrozen
    let st_td := M.stepEvents evs_td st_clone
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left (postTryDecrypt_entails_s5DispatchPrevEmpty_placed A lim st_td s0 s s2
          coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr g msgVer b_2c0
          (genP3S5Model C K rem loc msg rest st).1 G' recG
          (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
          (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPrePrevEmptyPlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3DispatchPrePrevEmptyPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by simpa [hres, Except.toBool] using hdec_rel
      have hfits_post := fitsEnv_postTd_of_stageP3Env hver hclone_rel htd_evs hfits
      have hvec_eq_s2 : vecResultAt (A.atState lim st_td s2) (s.sp + 0x270#64) (.error e) =
          vecResultAt A.repAlloc (s.sp + 0x270#64) (.error e) := rfl
      have hss_g_eq_s2 : sessionStateAt (A.atState lim st_td s2) (s.sp + 0xa90#64) G'
          (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
          (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hss_rec_eq_s2 : sessionStateAt (A.atState lim st_td s2) (coroPtr + 0xf8#64) recG st =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
      have hprev_eq_s2 :
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt
            (A.atState lim st_td s2) coroPtr g =
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt
            A.repAlloc coroPtr g := rfl
      have hpool_eq_s2 : (A.atState lim st_td s2).pool = A.pool lim st_td s2 := rfl
      simp only [hvec_eq_s2, hss_g_eq_s2, hss_rec_eq_s2, hprev_eq_s2, hpool_eq_s2]
      have herr := stageP3_sub5_err_prevEmpty_full_placed_ok ext hC.shim hC.alloc hC.dealloc
        hC.memcpy hC.grow hDropSS3 hC.panic st_td s0 s2 coroPtr outPtr initErrsPtr
        hfits_post hinit_ne e he_npan b_2c0 g G' recG
        (genP3S5Model C K rem loc msg rest st).2 st hfr2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrevEmptyM3Placed
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPrePrevEmptyM3Placed
        at herr
      have herr_post : ∀ st_e sf,
          stageP3ErrPostPrevEmptyM3Placed A lim st_e s0 s2 sf coroPtr outPtr e =
            stageP3ErrPostPrevEmpty_placed A lim st_e s0 s sf coroPtr outPtr e := by
        intro st_e sf
        unfold stageP3ErrPostPrevEmptyM3Placed stageP3ErrPostPrevEmpty_placed
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPostPrevEmptyM3Placed
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPostPrevEmpty_placed
        rw [hs2_sp]
      simp only [herr_post, hs2_sp] at herr
      simp only [hvec_eq_s2, hss_g_eq_s2, hss_rec_eq_s2, hprev_eq_s2, hpool_eq_s2] at herr
      apply sepWPp_lift_false_qp; apply sepWPp_frame_false_qp
      refine ret_sepWPp_frame_false herr (by sep_focus)
        fun sf _ _ _ ⟨evs_err, herr_evs, hPf_err, hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      let evs_tot := segCloneEvents recG st ++ (evs_td ++ evs_err)
      have hevs_tot : StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs_tot :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_err, rfl, rfl,
          Or.inr ⟨evs_td, evs_err, rfl, htd_evs, herr_evs⟩⟩
      have hstep_tot : M.stepEvents evs_err st_td = M.stepEvents evs_tot st_b := by
        dsimp only [st_td, st_clone, evs_tot]; simp only [← M.stepEvents_append, List.append_assoc]
      rw [hstep_tot] at hPf_err
      refine hErr G₁ G' evs_tot e sf _ hver hclone_rel hdec_false hevs_tot hres he_npan ?_
        hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      unfold genP3S5PostFrame_placed
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
        genP3S5PostFramePlaced
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3S5PostFramePlaced
        LsTokenInit LsTokenInitM3
      exact Entails.trans (entails_replace_sub hPf_err (by sep_focus) rfl)
        (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by simpa [hres, Except.toBool] using hdec_rel
      have hstack_set : stackAt s.sp growOneSpeStack =
          memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hvec_eq_s2 : vecResultAt (A.atState lim st_td s2) (s.sp + 0x270#64) (.ok pt) =
          vecResultAt A.repAlloc (s.sp + 0x270#64) (.ok pt) := rfl
      have hss_g_eq_s2 : sessionStateAt (A.atState lim st_td s2) (s.sp + 0xa90#64) G'
          (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
          (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hss_rec_eq_s2 : sessionStateAt (A.atState lim st_td s2) (coroPtr + 0xf8#64) recG st =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
      have hprev_eq_s2 :
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt
            (A.atState lim st_td s2) coroPtr g =
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt
            A.repAlloc coroPtr g := rfl
      have hpool_eq_s2 : (A.atState lim st_td s2).pool = A.pool lim st_td s2 := rfl
      simp only [hvec_eq_s2, hss_g_eq_s2, hss_rec_eq_s2, hprev_eq_s2, hpool_eq_s2]
      have hok := stageP3_sub5_decResult_placed_ok ext hC.memcpy hC.setState st_td s0 s2
        coroPtr outPtr pt G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_false_steps_framed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨evs_free, ptCap, ptPtr, hevs_free,
          hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      let evs_ok := segCloneEvents recG st ++ (evs_td ++ evs_free)
      have hevs_ok : StageP3OkPrefixEnv tdEnv recG G₁ st rem loc msgG msg rest evs_ok :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_free, rfl, rfl,
          Or.inr ⟨evs_td, evs_free, rfl, htd_evs, hevs_free⟩⟩
      have hstep_ok : M.stepEvents evs_free st_td = M.stepEvents evs_ok st_b := by
        dsimp only [st_td, st_clone, evs_ok]; simp only [← M.stepEvents_append, List.append_assoc]
      rw [hstep_ok] at hPs'
      refine hOk G₁ G' evs_ok pt ptCap ptPtr s' _ hver hclone_rel hdec_true hevs_ok hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2) hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2)
        hx28' hcro' ?_
      unfold stageP3DispatchOkMidPrevEmpty_placed
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3DispatchOkMidPrevEmpty_placed
        genP3S5PostFrame_placed
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
        genP3S5PostFramePlaced
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3S5PostFramePlaced
        LsTokenInit LsTokenInitM3
      rw [hstack_set]
      have hlive_s' :
          (if ptCap = 0#64 then emp
           else (A.atState lim (M.stepEvents evs_ok st_b) s').live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) =
          (if ptCap = 0#64 then emp
           else A.live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) := rfl
      have hss_s' :
          sessionStateAt (A.atState lim (M.stepEvents evs_ok st_b) s') (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hprev_s' :
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.prevSessionsEmptyAt
            (A.atState lim (M.stepEvents evs_ok st_b) s') coroPtr g =
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt
            A.repAlloc coroPtr g := rfl
      have hpool_s' :
          (A.atState lim (M.stepEvents evs_ok st_b) s').pool =
          A.pool lim (M.stepEvents evs_ok st_b) s' := rfl
      rw [hlive_s', hss_s', hprev_s', hpool_s']
      exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_false_qp; apply sepWPp_frame_false_qp
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostNePlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
      stageP3Sub5ExtraPrePrevEmpty
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      sepWPp_weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ => ?_)
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_fromM := fitsEnv_fromM_of_stageP3Env hver hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    refine sepWPp_weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq (stackAt_root_split_grow s.sp)) (by sep_focus)
        (sepWPp_weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_))
    have hprev_m : CryptoVerification.SignalSession.Cli.RunProofs.Poll.prevSessionsEmptyAt A.repAlloc coroPtr g =
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt A.repAlloc coroPtr g := rfl
    rw [hprev_m]
    have hver_ne := stageP3_ver_ne_prevEmpty_sessionShim_full_placed_ok ext hC.shim hC.alloc
      hC.dealloc hC.grow hDropSS3 hC.panic st_clone s0 s s1 coroPtr ctxPtr outPtr initErrsPtr
      hfits_fromM hinit_ne msgVer b_2c0 g G₁ recG st
      hfr1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine ret_sepWPp_frame_false hver_ne (by sep_focus)
      fun sf _ _ _ ⟨evs_vn, hvn_evs, hPf_vn, hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    let evs_vn_tot := segCloneEvents recG st ++ evs_vn
    have hevs_vn_tot : StageP3VerNeEnv recG st evs_vn_tot :=
      Or.inr ⟨segCloneEvents recG st, evs_vn, rfl, rfl, hvn_evs⟩
    have hstep_vn : M.stepEvents evs_vn st_clone = M.stepEvents evs_vn_tot st_b := by
      dsimp only [st_clone, evs_vn_tot]; rw [← M.stepEvents_append]
    rw [hstep_vn] at hPf_vn
    have herr_eq :
        LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlacedBudgetAux.stageP3ErrPostPrevEmptyM3Placed
          A lim (M.stepEvents evs_vn_tot st_b) s0 s sf coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed) =
        stageP3ErrPostPrevEmpty_placed A lim (M.stepEvents evs_vn_tot st_b) s0 s sf coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed) := rfl
    rw [herr_eq] at hPf_vn
    refine hVerNe evs_vn_tot sf _ hver hevs_vn_tot ?_ hspf htrf hcc_f
      (hvregsf_1.trans hvregs1) hcrof
    unfold genP3S5PostFrame_placed
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
      LsTokenInit LsTokenInitM3
    exact Entails.trans (sepConj_mono_left hPf_vn) (Entails.of_eq (eq_of_sep_emp (by sep_focus)))

theorem stageP3PrevEmptyVRegs_full_placed_ok [LibsignalFullPlacement]
    (hCallees : ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
      (ext : String → Option (State → State)),
      AllocContractsXCliPlaced A lim ext →
      subroutine_ok (dpPollProgPlaced ext) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
      StageP3CalleesM3BasePlaced A lim ext) :
    StageP3PrevEmptyVRegsFrozenPlacedStmt := by
  intro M A lim tdEnv st_b ext C ctl K hA hcc hscc hroot hDropSS3
  exact stageP3PrevEmptyVRegs_of_base_full_placed_ok st_b ext C ctl K
    (hCallees ext hA hDropSS3) hcc hscc hroot hDropSS3

set_option maxHeartbeats 1200000 in
theorem stageP3GenStepsVRegs_of_base_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (st_b : M.σ) (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : MlKem)
    (hC : StageP3CalleesM3BasePlaced A lim ext)
    (hcc : ChainClone3OkPlaced A lim ext) (hscc : SenderChainClone3OkPlaced A lim ext)
    (hroot : subroutine_ok (dpPollProgPlaced ext) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv))) :
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b (StageP3Env tdEnv recG st rem loc msgG msg msgVer rest) →
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      LibsignalFrozen lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced ext) s s' → s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running → s'.sp = s.sp → s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMid_placed A lim (M.stepEvents evs_p3 st_b) s0 s s'
            coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr pt b_2c0 G'
            (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr outPtr prevStatesPtr e ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_p3 : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNeEnv recG st evs_p3 →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr outPtr prevStatesPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          genP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0 ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0) := by
  intro s0 s coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest recG st rem loc msgG msg F_frame Q
    hfits hinit_ne hnot_self hseeds hrc_lt hpq_lt hfr hpc hrun hsp_align hsp_root htr hvregs
    hOk hErr hVerNe
  have hcro : LibsignalCodeRoLoaded lsmpl s.mem := lscro_of_frozen_aux hfr
  have hfits_clone := fitsEnv_segClone_of_stageP3Env hfits
  refine stageP3_clone_vregs_prefix_base_placed_steps C K ext hC hcc hscc st_b
    s0 s coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    (stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0) F_frame Q
    hfits_clone hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  have hfr1 : LibsignalFrozen lsmpl s1.mem := libsignalFrozen_of_keepsFrozen hfr hsteps01.keepsFrozen
  refine SepWPp.weaken_pre hent1 (SepWPp.weaken_pre
    (P' := (genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b) s.sp
        (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG
        st rem loc msgG msg s1 ∗
      (LsTokenInitM3 ∗
        stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0)) ∗ F_frame)
    (Entails.of_eq (by sep_ac_rfl)) ?_)
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostEqPlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      sepWPp_weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hclone_rel => ?_)
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_td := fitsEnv_td_of_stageP3Env hver hclone_rel hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    change SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 _ Q _
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    let F_dec : SepProp := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0
    refine SepWPp.weaken_pre (P' := (LsTokenInitM3 ∗
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A.repAlloc rem remAddrPtr ∗
        protocolAddressAt A.repAlloc loc locAddrPtr ∗
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool lim st_clone s1) ∗
        (F_dec ∗ F_frame))
      (Entails.of_eq (eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K tdEnv hroot st_clone s0 s s1
      coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest G₁ st rem loc msgG msg
      (F_dec ∗ F_frame) Q hver hfits_td hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hcro1 hpc1 hrun1 hs1_sp htr1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' evs_td hsteps12 htd_evs hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2
          hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    have hfr2 : LibsignalFrozen lsmpl s2.mem := libsignalFrozen_of_keepsFrozen hfr hsteps02.keepsFrozen
    let st_td := M.stepEvents evs_td st_clone
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left (postTryDecrypt_entails_s5Dispatch_zero_placed A lim st_td s0 s s2
          coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr remAddrPtr locAddrPtr whisperMsgPtr
          msgVer b_2c0 (genP3S5Model C K rem loc msg rest st).1 G' recG
          (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
          (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPreZeroPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by simpa [hres, Except.toBool] using hdec_rel
      have hfits_post := fitsEnv_postTd_of_stageP3Env hver hclone_rel htd_evs hfits
      have herr := stageP3_sub5_err_zero_full_placed_ok ext hC st_td s0 s2 coroPtr outPtr
        initErrsPtr prevStatesPtr hfits_post hinit_ne e he_npan b_2c0 G' recG
        (genP3S5Model C K rem loc msg rest st).2 st hfr2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPreZeroPlaced at herr
      have herr_post : ∀ st_e sf,
          stageP3ErrPost_placed A lim st_e s0 s2 sf coroPtr outPtr prevStatesPtr e =
            stageP3ErrPost_placed A lim st_e s0 s sf coroPtr outPtr prevStatesPtr e := by
        intro st_e sf
        unfold stageP3ErrPost_placed
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPost_placed
        rw [hs2_sp]
      simp only [herr_post, hs2_sp] at herr
      apply sepWPp_lift_false_qp; apply sepWPp_frame_false_qp
      refine ret_sepWPp_frame_false herr (by sep_focus)
        fun sf _ _ _ ⟨evs_err, herr_evs, hPf_err, hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      let evs_tot := segCloneEvents recG st ++ (evs_td ++ evs_err)
      have hevs_tot : StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs_tot :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_err, rfl, rfl,
          Or.inr ⟨evs_td, evs_err, rfl, htd_evs, herr_evs⟩⟩
      have hstep_tot : M.stepEvents evs_err st_td = M.stepEvents evs_tot st_b := by
        dsimp only [st_td, st_clone, evs_tot]; simp only [← M.stepEvents_append, List.append_assoc]
      rw [hstep_tot] at hPf_err
      refine hErr G₁ G' evs_tot e sf _ hver hclone_rel hdec_false hevs_tot hres he_npan ?_
        hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      unfold genP3S5PostFrame_placed
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
        LsTokenInit
      exact Entails.trans (entails_replace_sub hPf_err (by sep_focus) rfl)
        (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by simpa [hres, Except.toBool] using hdec_rel
      have hstack_set : stackAt s.sp growOneSpeStack =
          memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_placed_ok ext hC.memcpy hC.setState st_td s0 s2
        coroPtr outPtr pt G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_false_steps_framed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨evs_free, ptCap, ptPtr, hevs_free,
          hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      let evs_ok := segCloneEvents recG st ++ (evs_td ++ evs_free)
      have hevs_ok : StageP3OkPrefixEnv tdEnv recG G₁ st rem loc msgG msg rest evs_ok :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_free, rfl, rfl,
          Or.inr ⟨evs_td, evs_free, rfl, htd_evs, hevs_free⟩⟩
      have hstep_ok : M.stepEvents evs_free st_td = M.stepEvents evs_ok st_b := by
        dsimp only [st_td, st_clone, evs_ok]; simp only [← M.stepEvents_append, List.append_assoc]
      rw [hstep_ok] at hPs'
      refine hOk G₁ G' evs_ok pt ptCap ptPtr s' _ hver hclone_rel hdec_true hevs_ok hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2) hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2)
        hx28' hcro' ?_
      unfold stageP3DispatchOkMid_placed
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3DispatchOkMid_placed
        genP3S5PostFrame_placed
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
        LsTokenInit
      rw [hstack_set]
      have hlive_s' :
          (if ptCap = 0#64 then emp
           else (A.atState lim (M.stepEvents evs_ok st_b) s').live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) =
          (if ptCap = 0#64 then emp
           else A.live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) := rfl
      have hss_s' :
          sessionStateAt (A.atState lim (M.stepEvents evs_ok st_b) s') (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hpool_s' :
          (A.atState lim (M.stepEvents evs_ok st_b) s').pool =
          A.pool lim (M.stepEvents evs_ok st_b) s' := rfl
      rw [hlive_s', hss_s', hpool_s']
      exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_false_qp; apply sepWPp_frame_false_qp
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostNePlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
      stageP3Sub5ExtraPre
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      sepWPp_weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ => ?_)
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_fromM := fitsEnv_fromM_of_stageP3Env hver hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    refine sepWPp_weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus)
      (sepWPp_weaken_frame (Entails.of_eq (stackAt_root_split_grow s.sp)) (by sep_focus)
        (sepWPp_weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_))
    have hver_ne := stageP3_ver_ne_zero_full_placed_ok ext hC st_clone hfits_fromM s0 s s1 coroPtr
      ctxPtr outPtr initErrsPtr prevStatesPtr hinit_ne msgVer b_2c0 G₁ recG st
      hfr1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine ret_sepWPp_frame_false hver_ne (by sep_focus)
      fun sf _ _ _ ⟨evs_vn, hvn_evs, hPf_vn, hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    let evs_vn_tot := segCloneEvents recG st ++ evs_vn
    have hevs_vn_tot : StageP3VerNeEnv recG st evs_vn_tot :=
      Or.inr ⟨segCloneEvents recG st, evs_vn, rfl, rfl, hvn_evs⟩
    have hstep_vn : M.stepEvents evs_vn st_clone = M.stepEvents evs_vn_tot st_b := by
      dsimp only [st_clone, evs_vn_tot]; rw [← M.stepEvents_append]
    rw [hstep_vn] at hPf_vn
    refine hVerNe evs_vn_tot sf _ hver hevs_vn_tot ?_ hspf htrf hcc_f
      (hvregsf_1.trans hvregs1) hcrof
    unfold genP3S5PostFrame_placed
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
      LsTokenInit LsTokenInitM3
    exact Entails.trans (sepConj_mono_left hPf_vn) (Entails.of_eq (eq_of_sep_emp (by sep_focus)))

theorem stageP3GenStepsVRegs_full_placed_ok [LibsignalFullPlacement]
    (hCallees : ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
      (ext : String → Option (State → State)),
      AllocContractsXCliPlaced A lim ext → StageP3CalleesM3BasePlaced A lim ext) :
    StageP3GenStepsVRegsFrozenPlacedStmt := by
  intro M A lim tdEnv st_b ext C ctl K hA hcc hscc hroot
  exact stageP3GenStepsVRegs_of_base_full_placed_ok st_b ext C ctl K
    (hCallees ext hA) hcc hscc hroot

private theorem hookNoop_rustAllocShimVm_hookOk_frz : HookOk hookNoop rustAllocShimVmSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  dsimp only [rustAllocShimVmSpec, hookNoop, retHook, id_eq] at hpre ⊢
  rw [emp_sepConj] at hpre
  rw [satisfies_pure_sepConj]
  exact ⟨⟨⟨by cases s0; rfl, by cases s0; rfl, by cases s0; rfl, by cases s0; rfl,
    by cases s0; rfl, by cases s0; rfl, by cases s0; rfl⟩,
    ⟨⟨by cases s0; rfl, by cases s0; rfl, by cases s0; rfl⟩,
     by cases s0; rfl, fun _ => by cases s0; rfl, fun _ _ _ => by cases s0; rfl⟩⟩, hpre⟩

private theorem cli_rustAllocShimVm_sat_frz (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (hShim : gh.shim = hookNoop) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      rustAllocShimVmSpec :=
  (show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
    ⟨hookNoop, (cliGhostExterns_shim gh (cliExternsPlaced mmpl W)).trans (congrArg some hShim),
      hookNoop_rustAllocShimVm_hookOk_frz⟩

private theorem cli_framelessMemcpy_sat_frz [LibsignalPlacement] {M : AllocCostModel}
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

private theorem pollTryDecryptM3PlacedSpecTPTight_eq_over_frz [LibsignalPlacement]
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
    (cli_rustAllocShimVm_sat_frz mmpl gh W hG.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show lsRustReallocSymCli = lsRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hG)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
    (cli_framelessMemcpy_sat_frz mmpl gh W hG)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_sessionMemmove_budget_sat mmpl W extHookStack))
    (cliGhostExterns_panic_handle_error mmpl gh W)
    (chainMerge5CroPlacedOkExt_cli mmpl gh W hG)

theorem stageP3Prev1VRegs_full_placed_of_verNeAt [LibsignalFullPlacement]
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
    StageP3Prev1VRegsAtFrozenPlacedStmt A lim tdEnv PrevEncOK := by
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
    rw [pollTryDecryptM3PlacedSpecTPTight_eq_over_frz]
    exact hroot
  exact stageP3Gen_prev1_vregs_at_full_placed_ok ext W.C 0#64 W.Q.K
    hshim halloc hdealloc hmemcpy
    (cliGrowOneSpe_518_placed_ok mmpl gh W hG)
    (cliSetSessionState_518_placed_ok mmpl gh W hG)
    hDropSS3 hcc hscc hrootM3
    (hVerNeAt mmpl gh W hG hAllocX hDropSS3)
    st_b s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr
    cur msgVer b_2c0 enc rest recG st rem loc msgG msg F_frame Q
    hfits hinit hcap hprev hv4 hns hsd hrc hpq hfr hpc hrun hsp hroot_sp hfp htr hvregs
    (fun G₁ G' pt ptCap ptPtr evs_ok s' P_s' => hOk G₁ G' evs_ok pt ptCap ptPtr s' P_s')
    (fun G₁ G' e evs_err sf P_f => hErr G₁ G' evs_err e sf P_f)
    (fun evs_vn sf P_f hver hevs hPf => hVerNe evs_vn sf P_f hver hevs
      (Entails.trans hPf (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
          (sepConj_mono_right (entails_anyHeap emp)))))))))

theorem stageP3_prev1_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop} :
    StageP3Prev1VRegsFrozenPlacedStmt A lim tdEnv :=
  stageP3Prev1VRegs_full_placed_of_verNeAt
    (fun mmpl gh W hG _ _ => cliVerNe1e04_full_placed_ok mmpl gh W hG)

end FrozenVariants

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudget
