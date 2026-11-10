/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Substage P3.5 Error Paths

Budget-threaded `[LibsignalPlacement]` and `[LibsignalFullPlacement]` proofs of
`StageP3Sub5ErrPrevEmptyPlacedStmt` (`+0x1cd8 → s0.readReg64 .x30` under `FromVPostTdEnv`) and
`stageP3Gen_prevEmpty_vregs_placed_ok_of_clone`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding
  dropSessionStructureLocal2Spec growOneSpeSpec
open CryptoVerification.LibsignalTripleRatchet.RawByteMove CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 hiding
  growOneSpe_post_zero_eq growOneSpe_pre_zero_eq
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  coro_e0_3w_344_entails_368 dpClosureEntryM3Placed prevSessionsEmptyAt prevSessionsEmptyAt_unpack
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (pqLogLevelCellPlaced)
open CryptoVerification.CliHandshake.RespClosurePlaced CryptoVerification.CliHandshake.Placed
open CryptoVerification.LibsignalTripleRatchet.Getters hiding dropSpeSpec
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5Budget (
  growOneSpe_post_zero_eq growOneSpe_pre_zero_eq
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux (
  bind_sepWPp_false_steps_framed ret_sepWPp_frame_false stageP3ErrPostPrevEmptyM3Placed
  stageP3ErrPrePrevEmptyM3Placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  CloneGenVRegsPlacedStmt StageP3PrevEmptyVRegsM3PlacedStmt StageP3Sub5ErrPrevEmptyPlacedStmt
  StageP3VerNePrevEmptyPlacedStmt stageP3Gen_prevEmpty_vregs_placed_ok_of_parts
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux (
  bind_sepWP_lscro_frame_err call_lscl_nopanic_err call_lscl_ro_nopanic_err
  drop_spe2_placed_ok_at_of_dealloc fitsEnv_growOneSpe_of_fromVPostTd
  fitsEvents_alloc17_of_fromVPostTd freeOnlyEvs_append freeOnlyEvs_dealloc
  fromVPostTdEnv_of_nondup intro_lsro_decryptionFailed_err p3_alloc_2eac_placed_ok
  p3_err_dup_placed_wp p3_err_nondup_a_placed_wp p3_err_nondup_b_placed_wp
  p3_err_nondup_c_placed_wp p3_err_nondup_d_placed_wp p3_err_tail_dup_a_placed_wp
  p3_err_tail_nondup_a1_placed_wp p3_err_tail_nondup_a2_placed_wp
  p3_err_tail_prev_dealloc_placed_wp p3_err_tail_prev_zero_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget (
  pqxdhLogClosurePlacedSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec growOneSpeSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (FromVPostTdEnv)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## Common epilogue and duplicate-message error path (`speTag e = speWord 23`) -/

private theorem bind_sepWPp_frame_false {prog : Program} {mid ret : BitVec 64} {s : State}
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
/-- General-`prevCap` budget-threaded common error epilogue (`lsmpl.base 512 → s0.readReg64 .x30`)
under `[LibsignalPlacement]`. -/
theorem stageP3_err_tail_common_prevEmpty_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errTag w0 w1 w2 w3 w4 : BitVec 64) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = lsmpl.base 512) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 = dpClosureEntryM3Placed + 0x359c#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st_b s ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs_common : List AllocEvent,
          FreeOnlyEvs evs_common ∧
          (P_f ⊢ memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            words6At outPtr errTag w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs_common st_b) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  refine call_lscl_nopanic_err
    (x := ((⟨coroPtr + 0xf8#64, recG, recSt⟩ : DropSessionStructureGhost), st_b))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ A.pool lim st_b s ∗
      stackAt s.sp dropSessionStructure2Stack)
    hcro hDropSS3 hpc hrun hsp_al hx30 (by dsimp only [dropSessionStructureLocal2Spec])
    (And.intro hx0 (show LsRetAddr624 (s.readReg64 .lr) by
      change LsRetAddr624 (s.readReg64 .x30)
      rw [hx30]
      exact lsRetAddr624_blockPlacement_base_add 518 0x359c#64 (by decide) (by decide)))
    (by sep_focus)
    (hnext := fun s1 hpc1 hrun1 hsp1_s _ hcs1 hcro1 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_ss => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜s1.trace = s.trace ∧ FreeOnlyEvs evs_ss⌝)
    (P₂ := ⌜s1.trace = s.trace ∧ FreeOnlyEvs evs_ss⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨htr1_s, hevs_ss⟩ => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  rcases hcs1 with ⟨hx19_cs1, _, _, hx22_cs1, _, _, hx25_cs1, hx26_cs1, _, hx28_cs1, _, hvregs_cs1⟩
  have hx19_1 : s1.readReg64 .x19 = coroPtr := hx19_cs1.trans hx19
  have hx22_1 : s1.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64 := hx22_cs1.trans hx22
  have hx25_1 : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_cs1, hx25, hsp1_s]
  have hx26_1 : s1.readReg64 .x26 = outPtr := hx26_cs1.trans hx26
  have hx28_1 : s1.readReg64 .x28 = errTag := hx28_cs1.trans hx28
  refine P3P4.SepWPp.weaken_frame (prevSessionsEmptyAt_unpack A.repAlloc coroPtr g) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝)
    (P₂ := ⌜g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64) (w2.extractLsb' 32 32) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (P3P4.outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ret2c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0 => ?_
  have hrepack_out1c := (repack20_32_64_64_to_64_64_32 (outPtr + 0x1c#64)
    (w2.extractLsb' 32 32) w3 w4).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out1c
  have hrepack_out8 := (words3_repack_w32_2w64_w32 (outPtr + 0x8#64) w0 w1 w2).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out8
  have hout_words :
      ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₆₄ w0) ∗
      ((outPtr + 0x10#64) ↦₆₄ w1) ∗ ((outPtr + 0x18#64) ↦₆₄ w2) ∗
      ((outPtr + 0x20#64) ↦₆₄ w3) ∗ ((outPtr + 0x28#64) ↦₆₄ w4) ⊢
      words6At outPtr errTag w0 w1 w2 w3 w4 := by
    unfold words6At; rw [BitVec.add_zero]; exact Entails.refl _
  by_cases hcap : g.prevCap = 0#64
  · simp only [hcap, ↓reduceIte, emp_sepConj, sepConj_emp]
    have hstep2 := p3_err_tail_prev_zero_placed_wp (A := A) (lim := lim) ext
      (M.stepEvents evs_ss st_b) s1 coroPtr outPtr errTag g.prevPtr
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hpc1 hrun1 hsp1_align hx19_1 hx22_1 hx25_1 hx26_1 hx28_1
    rw [hsp1_s] at hstep2
    refine bind_sepWP_lscro_frame_err hcro1 hstep2 (by sep_focus)
      fun sf hpcf hrunf hcrof hregsf => ?_
    rcases hregsf with ⟨hspf_s, htrf_1, hvregs_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine P3P4.SepWPp.weaken_frame (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (sp370_36_err_fold s.sp
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        w3 w4 (w2.extractLsb' 32 32))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hout_words (by sep_focus) ?_
    exact SepWPp.done hpcf hrunf ⟨evs_ss, hevs_ss,
      Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
      hspf_s, htrf_1.trans (htr1_s.trans htr),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hcrof, hvregs_f.trans hvregs_cs1⟩
  · simp only [hcap, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
    have hstack_alloc :
        stackAt s.sp dropSessionStructure2Stack =
          memRegion (s.sp - 4192#64) 96 ∗ stackAt s.sp allocHookStack :=
      stackAt_split_bottom s.sp allocHookStack 96 (by decide)
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
    have hstep2 := p3_err_tail_prev_dealloc_placed_wp ext hdealloc (M.stepEvents evs_ss st_b)
      s1 coroPtr outPtr errTag g.prevCap g.prevPtr
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hcap hprev_lt hpc1 hrun1 hsp1_align hx19_1 hx22_1 hx25_1 hx26_1 hx28_1
    rw [hsp1_s] at hstep2
    refine bind_sepWP_lscro_frame_err hcro1 hstep2 (by sep_focus)
      fun sf hpcf hrunf hcrof hregsf => ?_
    rcases hregsf with ⟨hspf_s, htrf_1, hvregs_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (sp370_36_err_fold s.sp
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        w3 w4 (w2.extractLsb' 32 32))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hout_words (by sep_focus) ?_
    have hst_eq : M.stepEvents (rustDeallocEvents (g.prevCap.toNat * 24) 8)
        (M.stepEvents evs_ss st_b) =
        M.stepEvents (evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8) st_b :=
      (M.stepEvents_append evs_ss (rustDeallocEvents (g.prevCap.toNat * 24) 8) st_b).symm
    rw [hst_eq]
    exact SepWPp.done hpcf hrunf ⟨evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8,
      freeOnlyEvs_append hevs_ss (freeOnlyEvs_dealloc (g.prevCap.toNat * 24) 8),
      Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
      hspf_s, htrf_1.trans (htr1_s.trans htr),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hcrof, hvregs_f.trans hvregs_cs1⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_err_tail_dup_prevEmpty_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr w0 w1 w2 w3 w4 : BitVec 64) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
       ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st_b s ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs_common : List AllocEvent,
          FreeOnlyEvs evs_common ∧
          (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
            memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs_common st_b) sf ∗
            stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  refine P3P4.SepWPp.weaken_frame (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG recSt) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun u_250 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
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
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000017#64 w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hfold250 : ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64) (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32) (w2.extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hsp1_s]
  have hcommon := stageP3_err_tail_common_prevEmpty_placed_ok ext hdealloc hDropSS3 st_b
    s0 s1 coroPtr outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 b_2c0 g recG recSt
    hcro1 hpc1 hrun1 hsp1_align (htr1_s.trans htr) hx0_1 hx19_1 hx22_1 hx25_1' (hx26_1.trans hx26) hx28_1 hx30_1
  rw [hsp1_s] at hcommon
  refine ret_sepWPp_frame_false hcommon (by sep_focus)
    fun sf _ _ _ ⟨evs_common, hevs_c, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  exact ⟨evs_common, hevs_c,
    entails_replace_sub hPf (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)),
    hspf, htrf, hcc, hcrof, hvregs_f.trans hvregs_1⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_dup_prevEmpty_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr : BitVec 64) (ratVer counter : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A.repAlloc (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st_b s ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs_dup : List AllocEvent,
          FreeOnlyEvs evs_dup ∧
          (P_f ⊢ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            recordResultAt A.repAlloc outPtr (.error (.duplicatedMessage ratVer counter)) ∗
            memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs_dup st_b) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  have hdecomp : vecResultAt A.repAlloc (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64, words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
          speAt A.repAlloc (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
        ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
        ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A.repAlloc (utf8 "decrypt") (s.sp + 0x270#64) (.duplicatedMessage ratVer counter) (by nofun)
    dsimp only [vecResultAt, speTag, speWord] at h1 ⊢
    refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hdecomp (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64, words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
      speAt A.repAlloc (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
    (P₂ := ⌜∀ c : BitVec 64, words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
      speAt A.repAlloc (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hreassemble => ?_
  have hstep1 := p3_err_dup_placed_wp A lim st_b ext s coroPtr outPtr hpc hrun hsp_align hx19 hx24
  refine bind_sepWP_lscro_frame_err hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  refine call_lscl_nopanic_err
    (x := ((⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost), st_b))
    (T := sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool lim st_b s1 ∗
      stackAt s.sp dropSessionStructure2Stack)
    hcro1 hDropSS3 hpc1 hrun1 hsp1_al hx30_1 (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1_s])
    (And.intro hx0_1 (show LsRetAddr624 (s1.readReg64 .lr) by
      change LsRetAddr624 (s1.readReg64 .x30)
      rw [hx30_1]
      exact lsRetAddr624_blockPlacement_base_add 518 0x34dc#64 (by decide) (by decide)))
    (by sep_focus) (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp1_s]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_drop1 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜s2.trace = s1.trace ∧ FreeOnlyEvs evs_drop1⌝)
    (P₂ := ⌜s2.trace = s1.trace ∧ FreeOnlyEvs evs_drop1⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨htr2_1, hevs_drop1⟩ => ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx24_2 : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_cs2, hx24_1, hsp2_s]
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hsp2_s]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hx28_2 : s2.readReg64 .x28 = 0x8000000000000017#64 := hx28_cs2.trans hx28_1
  have htail := stageP3_err_tail_dup_prevEmpty_placed_ok ext hdealloc hDropSS3
    (M.stepEvents evs_drop1 st_b) s0 s2 coroPtr outPtr errsPtr w0 w1 w2 w3 w4 b_2c0 g recG recSt
    hcro2 hpc2 hrun2 hsp2_align (htr2_1.trans (htr1_s.trans htr)) hx19_2 hx24_2 hx25_2 hx26_2 hx28_2
  rw [hsp2_s] at htail
  refine ret_sepWPp_frame_false htail (by sep_focus)
    fun sf _ _ _ ⟨evs_tail, hevs_tail, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec : words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
      recordResultAt A.repAlloc outPtr (.error (.duplicatedMessage ratVer counter)) := hreassemble outPtr
  have hst_eq : M.stepEvents evs_tail (M.stepEvents evs_drop1 st_b) =
      M.stepEvents (evs_drop1 ++ evs_tail) st_b :=
    (M.stepEvents_append evs_drop1 evs_tail st_b).symm
  rw [hst_eq] at hPf
  refine ⟨evs_drop1 ++ evs_tail, freeOnlyEvs_append hevs_drop1 hevs_tail, ?_,
    hspf, htrf, hcc, hcrof, by rw [hvregs_f, hvregs_cs2, hvregs_1]⟩
  refine Entails.trans (entails_replace_sub hPf (by sep_focus) rfl) ?_
  exact entails_replace_sub hrec (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

/-! ## Non-duplicate error path (`speTag e ≠ speWord 23`) -/

set_option maxHeartbeats 1200000 in
theorem stageP3_err_tail_nondup_dec_prevEmpty_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr w0 w1 w2 w3 w4 : BitVec 64)
    (e : SignalProtocolError) (_he_npan : e ≠ .panic) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ A.live errsPtr 192 8 ∗
       speAt A.repAlloc (utf8 "decrypt") errsPtr e ∗ memRegion (errsPtr + 0x30#64) 144 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((s.sp + 0x278#64) ↦₆₄ w0) ∗ ((s.sp + 0x280#64) ↦₆₄ w1) ∗
       ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st_b s ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs_tail : List AllocEvent,
          FreeOnlyEvs evs_tail ∧
          (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            words6At outPtr 0x8000000000000018#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
            memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs_tail st_b) sf ∗
            stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  refine P3P4.SepWPp.weaken_frame (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG recSt) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun u_250 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  have hstep1 := p3_err_tail_nondup_a1_placed_wp A lim st_b ext s coroPtr errsPtr hpc hrun hsp_align hx19
  refine bind_sepWP_lscro_frame_err hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx21_1, hx22_1, hx23_1,
    hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hdropSpe := drop_spe2_placed_ok_at_of_dealloc ext hdealloc
  have hstack_drop : stackAt s.sp dropSessionStructure2Stack =
      memRegion (s.sp - 4192#64) 64 ∗ stackAt s.sp dropSpeStack :=
    stackAt_split_bottom s.sp dropSpeStack 64 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop) (by sep_focus) ?_
  refine call_lscl_ro_nopanic_err (spec := dropSpeSpec M A lim)
    (x := ((⟨errsPtr, utf8 "decrypt", e⟩ : DropSpeGhost), st_b))
    (T := speAt A.repAlloc (utf8 "decrypt") errsPtr e ∗ A.pool lim st_b s1 ∗ stackAt s.sp dropSpeStack)
    hcro1 hdropSpe hpc1 hrun1 hsp1_al hx30_1 (by dsimp only [dropSpeSpec]; rw [hsp1_s])
    (And.intro hx0_1 (show LsRetAddr624 (s1.readReg64 .x30) by
      rw [hx30_1]
      exact lsRetAddr624_blockPlacement_base_add 518 0x34f4#64 (by decide) (by decide)))
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSpeSpec]; rw [hsp1_s]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_spe => ?_
  refine P3P4.SepWPp.weaken_frame (P₁ := ⌜s2.trace = s1.trace⌝) (P₂ := ⌜s2.trace = s1.trace⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine P3P4.SepWPp.weaken_frame (P₁ := ⌜FreeOnlyEvs evs_spe⌝) (P₂ := ⌜FreeOnlyEvs evs_spe⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hevs_spe => ?_
  have hjoin192 : memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 ⊢ memRegion errsPtr 192 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144) (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hjoin192 (by sep_focus) ?_
  have hstack_alloc : stackAt s.sp dropSpeStack =
      memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 32 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = errsPtr := hx21_cs2.trans hx21_1
  have hx22_2 : s2.readReg64 .x22 = errsPtr := hx22_cs2.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = 1#64 := hx23_cs2.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_cs2, hx24_1, hx24, hsp2_s]
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2_s]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs2.trans (hx28_1.trans hx28)
  have hstep3 := p3_err_tail_nondup_a2_placed_wp ext hdealloc (M.stepEvents evs_spe st_b) s2
    coroPtr errsPtr recG.localIk.cap
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32) (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    w3 w4 u_250 u_258 u_370 u_378 u_384 u_38c (w0.extractLsb' 0 32) (w2.extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx28_2
  rw [hsp2_s] at hstep3
  refine bind_sepWP_lscro_frame_err hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx22_3, _, hx25_3, hx26_3, _, hx28_3, _, hx30_3, hvregs_3⟩
  have hstack_restore :
      memRegion (s.sp - 4192#64) 64 ∗ memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp dropSessionStructure2Stack := by rw [hstack_drop, hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore (by sep_focus) ?_
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A.repAlloc recG recSt ⊢ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG recSt hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000018#64 w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hfold250 : ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64) (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32) (w2.extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = s3.sp + 0x210#64 := by rw [hx25_3, hsp3_s]
  have hcommon := stageP3_err_tail_common_prevEmpty_placed_ok ext hdealloc hDropSS3
    (M.stepEvents (rustDeallocEvents 192 8) (M.stepEvents evs_spe st_b))
    s0 s3 coroPtr outPtr 0x8000000000000018#64 w0 w1 w2 w3 w4 b_2c0 g recG recSt
    hcro3 hpc3 hrun3 hsp3_align (htr3_2.trans (htr2_1.trans (htr1_s.trans htr)))
    hx0_3 hx19_3 hx22_3 hx25_3' (hx26_3.trans hx26_2) hx28_3 hx30_3
  rw [hsp3_s] at hcommon
  refine ret_sepWPp_frame_false hcommon (by sep_focus)
    fun sf _ _ _ ⟨evs_common, hevs_c, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hst_eq :
      M.stepEvents evs_common
        (M.stepEvents (rustDeallocEvents 192 8) (M.stepEvents evs_spe st_b)) =
      M.stepEvents (evs_spe ++ (rustDeallocEvents 192 8 ++ evs_common)) st_b := by
    rw [M.stepEvents_append, M.stepEvents_append]
  rw [hst_eq] at hPf
  exact ⟨evs_spe ++ (rustDeallocEvents 192 8 ++ evs_common),
    freeOnlyEvs_append hevs_spe (freeOnlyEvs_append (freeOnlyEvs_dealloc 192 8) hevs_c),
    entails_replace_sub hPf (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)),
    hspf, htrf, hcc, hcrof, by rw [hvregs_f, hvregs_3, hvregs_cs2, hvregs_1]⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_nondup_prevEmpty_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hLogClosure : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr initErrsPtr : BitVec 64)
    (hfits : FitsEnv M lim st_b FromVPostTdEnv)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8) (g : RecordGhost) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPrePrevEmptyM3Placed A lim st_b s0 s s coroPtr outPtr initErrsPtr g e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        ∃ evs_err : List AllocEvent,
          FromVPostTdEnv evs_err ∧
          (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_err st_b) s0 s sf coroPtr outPtr e) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  unfold stageP3ErrPrePrevEmptyM3Placed
  unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPrePrevEmptyM3Placed
  change SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
    (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ vecResultAt A.repAlloc (s.sp + 0x270#64) (.error e) ∗
     sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
     ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
     ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
     prevSessionsEmptyAt A.repAlloc coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
     FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
     memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
     decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st_b s ∗
     stackAt s.sp growOneSpeStack) _ _
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
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hdecomp (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A.repAlloc (utf8 "decrypt") c e⌝)
    (P₂ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A.repAlloc (utf8 "decrypt") c e⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hreassemble => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x930#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u930 => SepWPp.exists_elim fun u938 =>
    SepWPp.exists_elim fun u940 => SepWPp.exists_elim fun u948 =>
    SepWPp.exists_elim fun u950 => SepWPp.exists_elim fun u958 => ?_
  have hstep1 := p3_err_nondup_a_placed_wp A lim st_b ext s coroPtr outPtr (speTag e)
    w0 w1 w2 w3 w4 u930 u938 u940 u948 u950 u958
    (speTag_ne_ok_of_ne_panic he_npan) htag_ne23 hpc hrun hsp_align hx19 hx24
  refine bind_sepWP_lscro_frame_err hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, _, _, _, _, hx19_1, hx24_1, hx25_1, hx26_1, _, _, _, hx30_1, hvregs_1⟩
  refine P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x930#64) (speTag e) w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hstack_log : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_lscl_nopanic_err (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := FromRecordCallees.lsLogOff ∗ stackAt s.sp pqxdhClosureStack)
    hcro1 hLogClosure hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s]; rfl) trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr2_1, hvm2_1⟩ => ?_
  have hpool12 : A.pool lim st_b s1 = A.pool lim st_b s2 := (A.pool_of_vmPreserved hvm2_1).symm
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpool12) (by sep_focus) ?_
  have hstack_restore1 : memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack ⊢
      stackAt s.sp growOneSpeStack := by rw [hstack_log]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore1 (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx24_2 : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs2.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs2.trans hx25_1
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hstep3 := p3_err_nondup_b_placed_wp A lim st_b ext s2 coroPtr hpc2 hrun2 hsp2_align hx19_2
  rw [hsp2_s] at hstep3
  refine bind_sepWP_lscro_frame_err hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx25_3, hx26_3, _, _, _, hx30_3, hvregs_3⟩
  have hsp3_s : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_s] using hsp_align
  have htr3_0 : s3.trace = s0.trace := htr3_2.trans (htr2_1.trans (htr1_s.trans htr))
  have hfits_grow := fitsEnv_growOneSpe_of_fromVPostTd hfits
  refine call_lscl_nopanic_err
    (spec := growOneSpeSpec M A lim)
    (x := ((s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))), st_b))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool lim st_b s3 ∗ stackAt s.sp growOneSpeStack)
    hcro3 hGrow hpc3 hrun3 hsp3_al hx30_3
    (by
      rw [growOneSpe_pre_zero_eq M A lim st_b s3 (s.sp + 0x3c8#64) initErrsPtr hx0_3 hinit_ne hfits_grow,
        hsp3_s, pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus) (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  rw [growOneSpe_post_zero_eq M A lim st_b s3 s4 (s.sp + 0x3c8#64) initErrsPtr, hsp3_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine P3P4.SepWPp.weaken_frame (P₁ := ⌜s4.trace = s3.trace⌝) (P₂ := ⌜s4.trace = s3.trace⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun htr4_3 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜errsPtr ≠ 0 ∧ errsPtr.toNat % 8 = 0⌝)
    (P₂ := ⌜errsPtr ≠ 0 ∧ errsPtr.toNat % 8 = 0⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun _ => ?_
  have hsplit192 : memRegion errsPtr 192 = memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144) (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hsplit192) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq errsPtr)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  have hlog_eq : pqLogLevelCellPlaced = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp4_s : s4.sp = s.sp := hsp4_3.trans hsp3_s
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4_s]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, hvregs_cs4⟩
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = 0#64 := hx21_cs4.trans hx21_3
  have hx24_4 : s4.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs4.trans (hx24_3.trans hx24_2)
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by rw [hx25_cs4, hx25_3, hx25_2, hsp4_s]
  have hx26_4 : s4.readReg64 .x26 = outPtr := hx26_cs4.trans (hx26_3.trans hx26_2)
  have hstep5 := p3_err_nondup_c_placed_wp A lim (M.stepEvents (rustAllocEvents 192 8) st_b)
    ext hshim s4 coroPtr errsPtr (speTag e)
    w0 w1 w2 w3 w4 e0 e1 e2 e3 e4 e5 hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx25_4
  rw [hsp4_s] at hstep5
  refine bind_sepWP_lscro_frame_err hcro4 hstep5 (by sep_focus) fun s5 hpc5 hrun5 hcro5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hx0_5, hx1_5, hx19_5, hx24_5, hx25_5, hx26_5, _, _, _, hvregs_5⟩
  have hlog_eq2 : (lsLogFilterAddr ↦₆₄ 0#64) = FromRecordCallees.lsLogOff := rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq2) (by sep_focus) ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  have htr5_0 : s5.trace = s0.trace := htr5_4.trans (htr4_3.trans htr3_0)
  have hreasm_errs :
      ((errsPtr + 0x0#64) ↦₆₄ speTag e) ∗ ((errsPtr + 0x8#64) ↦₆₄ w0) ∗
      ((errsPtr + 0x10#64) ↦₆₄ w1) ∗ ((errsPtr + 0x18#64) ↦₆₄ w2) ∗
      ((errsPtr + 0x20#64) ↦₆₄ w3) ∗ ((errsPtr + 0x28#64) ↦₆₄ w4) ∗ H ⊢
      speAt A.repAlloc (utf8 "decrypt") errsPtr e := by
    simpa only [words6At, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hreassemble errsPtr
  refine P3P4.SepWPp.weaken_frame hreasm_errs (by sep_focus) ?_
  have hstack_alloc : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hfits17 := fitsEvents_alloc17_of_fromVPostTd hfits
  have halloc17 := p3_alloc_2eac_placed_ok (A := A) (lim := lim) ext halloc
    (M.stepEvents (rustAllocEvents 192 8) st_b) s5
    emp hfits17 hcro5 hpc5 hrun5 hsp5_align hx0_5 hx1_5
  rw [sepConj_emp, hsp5_s] at halloc17
  refine bind_sepWPp_frame_false halloc17 (by sep_focus)
    fun s6 P_m6 hpc6 hrun6 ⟨hP6, hdf_ne, hsp6_5, htr6_5, hcs6, hcro6⟩ => ?_
  rw [sepConj_emp] at hP6
  refine P3P4.SepWPp.weaken_frame hP6 (by sep_focus) ?_
  have hstack_restore2 : memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
      stackAt s.sp growOneSpeStack := by rw [hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore2 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion17_split_eq (s6.readReg64 .x0))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun df_10 => SepWPp.exists_elim fun df_8 => SepWPp.exists_elim fun df_0 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6_s]; exact hsp_align
  rcases hcs6 with ⟨hx19_cs6, _, _, _, _, hx24_cs6, hx25_cs6, hx26_cs6, _, _, _, hvregs_cs6⟩
  have hx19_6 : s6.readReg64 .x19 = coroPtr := hx19_cs6.trans hx19_5
  have hx24_6 : s6.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs6.trans (hx24_5.trans hx24_4)
  have hx25_6 : s6.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs6.trans hx25_5
  have hx26_6 : s6.readReg64 .x26 = outPtr := hx26_cs6.trans (hx26_5.trans hx26_4)
  have hstep7 := p3_err_nondup_d_placed_wp A lim
    (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b))
    ext s6 coroPtr (s6.readReg64 .x0)
    0x6974707972636564#64 0x656c696166206e6f#64 df_0 df_8 (speTag e) w0 w1 w2 df_10 (w3.extractLsb' 0 8)
    hdf_ne hpc6 hrun6 hsp6_align rfl hx19_6
  rw [hsp6_s] at hstep7
  refine bind_sepWP_lscro_frame_err hcro6 hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx19_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7, hvregs_7⟩
  have hsp7_s : s7.sp = s.sp := hsp7_6
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7_s] using hsp_align
  refine SepWPp.drop_frame
    (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s6.readReg64 .x0))) (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus) ?_
  have hstack_drop2 : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_lscl_nopanic_err
    (x := ((⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost),
           M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b)))
    (T := sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗
          A.pool lim (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b)) s7 ∗
          stackAt s.sp dropSessionStructure2Stack)
    hcro7 hDropSS3 hpc7 hrun7 hsp7_al hx30_7 (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_s])
    (And.intro hx0_7 (show LsRetAddr624 (s7.readReg64 .lr) by
      change LsRetAddr624 (s7.readReg64 .x30)
      rw [hx30_7]
      exact lsRetAddr624_blockPlacement_base_add 518 0x34dc#64 (by decide) (by decide)))
    (by sep_focus) (hnext := fun s8 hpc8 hrun8 hsp8_7 _ hcs8 hcro8 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_s]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_drop1 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜s8.trace = s7.trace ∧ FreeOnlyEvs evs_drop1⌝)
    (P₂ := ⌜s8.trace = s7.trace ∧ FreeOnlyEvs evs_drop1⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨htr8_7, hevs_drop1⟩ => ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7.trans hsp7_s
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8_s]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, hx28_cs8, _, hvregs_cs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx24_8 : s8.readReg64 .x24 = s8.sp + 0x370#64 := by rw [hx24_cs8, hx24_7, hx24_6, hsp8_s]
  have hx25_8 : s8.readReg64 .x25 = s8.sp + 0x210#64 := by rw [hx25_cs8, hx25_7, hx25_6, hsp8_s]
  have hx26_8 : s8.readReg64 .x26 = outPtr := hx26_cs8.trans (hx26_7.trans hx26_6)
  have hx28_8 : s8.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs8.trans hx28_7
  have htail := stageP3_err_tail_nondup_dec_prevEmpty_placed_ok ext hdealloc hDropSS3
    (M.stepEvents evs_drop1 (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b)))
    s0 s8 coroPtr outPtr errsPtr 17#64 (s6.readReg64 .x0) 17#64 w3' w4 e he_npan b_2c0 g recG recSt
    hcro8 hpc8 hrun8 hsp8_align (htr8_7.trans (htr7_6.trans (htr6_5.trans htr5_0)))
    hx19_8 hx24_8 hx25_8 hx26_8 hx28_8
  rw [hsp8_s] at htail
  refine ret_sepWPp_frame_false htail (by sep_focus)
    fun sf _ _ _ ⟨evs_tail, hevs_tail, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A.repAlloc
    outPtr (s6.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  rw [RustCliAllocBudget.repAlloc_live] at hrec
  have hstack_restore3 : memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
      stackAt s.sp growOneSpeStack := by rw [hstack_drop2]; exact Entails.refl _
  have hst_eq :
      M.stepEvents evs_tail
        (M.stepEvents evs_drop1
          (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b))) =
      M.stepEvents (rustAllocEvents 192 8 ++ (rustAllocEvents 17 1 ++ (evs_drop1 ++ evs_tail))) st_b := by
    rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
  rw [hst_eq] at hPf
  refine ⟨rustAllocEvents 192 8 ++ (rustAllocEvents 17 1 ++ (evs_drop1 ++ evs_tail)),
    fromVPostTdEnv_of_nondup hevs_drop1 hevs_tail, ?_, hspf, htrf, hcc, hcrof,
    by rw [hvregs_f, hvregs_cs8, hvregs_7, hvregs_cs6, hvregs_5, hvregs_cs4, hvregs_3, hvregs_cs2, hvregs_1]⟩
  unfold stageP3ErrPostPrevEmptyM3Placed
  unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPostPrevEmptyM3Placed
  rw [hrec_err]
  change _ ⊢
    (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
      ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
    ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
    memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
    FromRecordCallees.lsLogOff ∗
    recordResultAt A.repAlloc outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
    memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
    memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
    decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
    A.pool lim (M.stepEvents (rustAllocEvents 192 8 ++ (rustAllocEvents 17 1 ++ (evs_drop1 ++ evs_tail))) st_b) sf ∗
    stackAt s.sp growOneSpeStack
  have herrs : ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ⊢
      ∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
        ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
        ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
    Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr
      (Entails.sepExists_right 1#64 (Entails.refl _)))
  refine Entails.trans (entails_replace_sub hPf (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub herrs (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hrec (by sep_focus) rfl) ?_
  exact entails_replace_sub hstack_restore3 (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

/-! ## Combined Substage P3.5 error theorem and Stage P3 composition -/

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_prevEmpty_placed_ok [LibsignalPlacement] :
    StageP3Sub5ErrPrevEmptyPlacedStmt := by
  intro M A lim ext hshim halloc hdealloc _hmemcpy hGrow hDropSS3 hLogClosure _hpanic
    st_b s0 s coroPtr outPtr initErrsPtr hfits hinit_ne e he_npan b_2c0 g G₂ recG st₂ recSt
    hcro hpc hrun hsp_align htr hx19 hx24
  by_cases htag23 : speTag e = speWord 23
  · obtain ⟨ratVer, counter, rfl⟩ := speTag_eq_speWord23_iff.mp htag23
    unfold stageP3ErrPrePrevEmptyM3Placed
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPrePrevEmptyM3Placed
    change SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A.repAlloc (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st_b s ∗
       stackAt s.sp growOneSpeStack) _ _
    have hstack_drop2 : stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
      stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
    rw [hstack_drop2]
    have hdup := stageP3_sub5_err_dup_prevEmpty_placed_ok ext hdealloc hDropSS3 st_b
      s0 s coroPtr outPtr initErrsPtr ratVer counter b_2c0 g G₂ recG st₂ recSt
      hcro hpc hrun hsp_align htr hx19 hx24
    refine ret_sepWPp_frame_false hdup (by sep_focus)
      fun sf _ _ _ ⟨evs_dup, hevs_dup, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
    have herrs : ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
        ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ⊢
        ∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 0#64 (Entails.sepExists_right initErrsPtr
        (Entails.sepExists_right 0#64 (Entails.refl _)))
    have hstack_restore : memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
        stackAt s.sp growOneSpeStack := by rw [hstack_drop2]; exact Entails.refl _
    refine ⟨evs_dup, Or.inl hevs_dup, ?_, hspf, htrf, hcc, hcrof, hvregs_f⟩
    unfold stageP3ErrPostPrevEmptyM3Placed
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPostPrevEmptyM3Placed
    dsimp only [SessionState.recordError]
    change _ ⊢
      (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
        ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
        ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
      memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
      FromRecordCallees.lsLogOff ∗
      recordResultAt A.repAlloc outPtr (.error (.duplicatedMessage ratVer counter)) ∗
      memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
      memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
      decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
      A.pool lim (M.stepEvents evs_dup st_b) sf ∗
      stackAt s.sp growOneSpeStack
    refine Entails.trans (entails_replace_sub hPf (by sep_focus) rfl) ?_
    refine Entails.trans (entails_replace_sub herrs (by sep_focus) rfl) ?_
    exact entails_replace_sub hstack_restore (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))
  · exact stageP3_sub5_err_nondup_prevEmpty_placed_ok ext hshim halloc hdealloc
      hGrow hDropSS3 hLogClosure st_b
      s0 s coroPtr outPtr initErrsPtr hfits hinit_ne e he_npan htag23
      b_2c0 g G₂ recG st₂ recSt hcro hpc hrun hsp_align htr hx19 hx24

theorem stageP3Gen_prevEmpty_vregs_placed_ok_of_clone [LibsignalPlacement]
    (hClone : CloneGenVRegsPlacedStmt)
    (hVerNeSub : StageP3VerNePrevEmptyPlacedStmt) :
    StageP3PrevEmptyVRegsM3PlacedStmt :=
  stageP3Gen_prevEmpty_vregs_placed_ok_of_parts
    hClone stageP3_sub5_err_prevEmpty_placed_ok hVerNeSub

/-! ## `[LibsignalFullPlacement]` / `LibsignalFrozen` variants -/

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_nondup_prevEmpty_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr initErrsPtr : BitVec 64)
    (hfits : FitsEnv M lim st_b FromVPostTdEnv)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8) (g : RecordGhost) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPrePrevEmptyM3Placed A lim st_b s0 s s coroPtr outPtr initErrsPtr g e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        ∃ evs_err : List AllocEvent,
          FromVPostTdEnv evs_err ∧
          (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_err st_b) s0 s sf coroPtr outPtr e) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  unfold stageP3ErrPrePrevEmptyM3Placed
  unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPrePrevEmptyM3Placed
  change SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
    (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ vecResultAt A.repAlloc (s.sp + 0x270#64) (.error e) ∗
     sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
     ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
     ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
     prevSessionsEmptyAt A.repAlloc coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
     FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
     memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
     decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st_b s ∗
     stackAt s.sp growOneSpeStack) _ _
  have hrec_err : SessionState.recordError .preKey e = .invalidMessage .preKey .decryptionFailed :=
    recordError_preKey_of_speTag_ne_speWord23 he_npan htag_ne23
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux.lscro_of_frozen hfr
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
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hdecomp (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A.repAlloc (utf8 "decrypt") c e⌝)
    (P₂ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A.repAlloc (utf8 "decrypt") c e⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hreassemble => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x930#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u930 => SepWPp.exists_elim fun u938 =>
    SepWPp.exists_elim fun u940 => SepWPp.exists_elim fun u948 =>
    SepWPp.exists_elim fun u950 => SepWPp.exists_elim fun u958 => ?_
  have hstep1 := p3_err_nondup_a_placed_wp A lim st_b ext s coroPtr outPtr (speTag e)
    w0 w1 w2 w3 w4 u930 u938 u940 u948 u950 u958
    (speTag_ne_ok_of_ne_panic he_npan) htag_ne23 hpc hrun hsp_align hx19 hx24
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux.bind_sepWP_lsfr_frame_err hfr hstep1 (by sep_focus) fun s1 hpc1 hrun1 hfr1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, _, _, _, _, hx19_1, hx24_1, hx25_1, hx26_1, _, _, _, hx30_1, hvregs_1⟩
  refine P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x930#64) (speTag e) w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hstack_log : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux.call_lsfr_nopanic_err (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := FromRecordCallees.lsLogOff ∗ stackAt s.sp pqxdhClosureStack)
    hfr1 (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux.pqxdh_log_closure_frozen_placed_ok_of_block (callerProg := lsProg_518 ext)) hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s]; rfl) trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hfr2 => ?_)
  have hcro2 : StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem := LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux.lscro_of_frozen hfr2
  dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr2_1, hvm2_1⟩ => ?_
  have hpool12 : A.pool lim st_b s1 = A.pool lim st_b s2 := (A.pool_of_vmPreserved hvm2_1).symm
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpool12) (by sep_focus) ?_
  have hstack_restore1 : memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack ⊢
      stackAt s.sp growOneSpeStack := by rw [hstack_log]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore1 (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx24_2 : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs2.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs2.trans hx25_1
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hstep3 := p3_err_nondup_b_placed_wp A lim st_b ext s2 coroPtr hpc2 hrun2 hsp2_align hx19_2
  rw [hsp2_s] at hstep3
  refine bind_sepWP_lscro_frame_err hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx25_3, hx26_3, _, _, _, hx30_3, hvregs_3⟩
  have hsp3_s : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_s] using hsp_align
  have htr3_0 : s3.trace = s0.trace := htr3_2.trans (htr2_1.trans (htr1_s.trans htr))
  have hfits_grow := fitsEnv_growOneSpe_of_fromVPostTd hfits
  refine call_lscl_nopanic_err
    (spec := growOneSpeSpec M A lim)
    (x := ((s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))), st_b))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool lim st_b s3 ∗ stackAt s.sp growOneSpeStack)
    hcro3 hGrow hpc3 hrun3 hsp3_al hx30_3
    (by
      rw [growOneSpe_pre_zero_eq M A lim st_b s3 (s.sp + 0x3c8#64) initErrsPtr hx0_3 hinit_ne hfits_grow,
        hsp3_s, pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus) (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  rw [growOneSpe_post_zero_eq M A lim st_b s3 s4 (s.sp + 0x3c8#64) initErrsPtr, hsp3_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine P3P4.SepWPp.weaken_frame (P₁ := ⌜s4.trace = s3.trace⌝) (P₂ := ⌜s4.trace = s3.trace⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun htr4_3 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜errsPtr ≠ 0 ∧ errsPtr.toNat % 8 = 0⌝)
    (P₂ := ⌜errsPtr ≠ 0 ∧ errsPtr.toNat % 8 = 0⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun _ => ?_
  have hsplit192 : memRegion errsPtr 192 = memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144) (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hsplit192) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq errsPtr)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  have hlog_eq : pqLogLevelCellPlaced = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp4_s : s4.sp = s.sp := hsp4_3.trans hsp3_s
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4_s]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, hvregs_cs4⟩
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = 0#64 := hx21_cs4.trans hx21_3
  have hx24_4 : s4.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs4.trans (hx24_3.trans hx24_2)
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by rw [hx25_cs4, hx25_3, hx25_2, hsp4_s]
  have hx26_4 : s4.readReg64 .x26 = outPtr := hx26_cs4.trans (hx26_3.trans hx26_2)
  have hstep5 := p3_err_nondup_c_placed_wp A lim (M.stepEvents (rustAllocEvents 192 8) st_b)
    ext hshim s4 coroPtr errsPtr (speTag e)
    w0 w1 w2 w3 w4 e0 e1 e2 e3 e4 e5 hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx25_4
  rw [hsp4_s] at hstep5
  refine bind_sepWP_lscro_frame_err hcro4 hstep5 (by sep_focus) fun s5 hpc5 hrun5 hcro5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hx0_5, hx1_5, hx19_5, hx24_5, hx25_5, hx26_5, _, _, _, hvregs_5⟩
  have hlog_eq2 : (lsLogFilterAddr ↦₆₄ 0#64) = FromRecordCallees.lsLogOff := rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq2) (by sep_focus) ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  have htr5_0 : s5.trace = s0.trace := htr5_4.trans (htr4_3.trans htr3_0)
  have hreasm_errs :
      ((errsPtr + 0x0#64) ↦₆₄ speTag e) ∗ ((errsPtr + 0x8#64) ↦₆₄ w0) ∗
      ((errsPtr + 0x10#64) ↦₆₄ w1) ∗ ((errsPtr + 0x18#64) ↦₆₄ w2) ∗
      ((errsPtr + 0x20#64) ↦₆₄ w3) ∗ ((errsPtr + 0x28#64) ↦₆₄ w4) ∗ H ⊢
      speAt A.repAlloc (utf8 "decrypt") errsPtr e := by
    simpa only [words6At, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hreassemble errsPtr
  refine P3P4.SepWPp.weaken_frame hreasm_errs (by sep_focus) ?_
  have hstack_alloc : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hfits17 := fitsEvents_alloc17_of_fromVPostTd hfits
  have halloc17 := p3_alloc_2eac_placed_ok (A := A) (lim := lim) ext halloc
    (M.stepEvents (rustAllocEvents 192 8) st_b) s5
    emp hfits17 hcro5 hpc5 hrun5 hsp5_align hx0_5 hx1_5
  rw [sepConj_emp, hsp5_s] at halloc17
  refine bind_sepWPp_frame_false halloc17 (by sep_focus)
    fun s6 P_m6 hpc6 hrun6 ⟨hP6, hdf_ne, hsp6_5, htr6_5, hcs6, hcro6⟩ => ?_
  rw [sepConj_emp] at hP6
  refine P3P4.SepWPp.weaken_frame hP6 (by sep_focus) ?_
  have hstack_restore2 : memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
      stackAt s.sp growOneSpeStack := by rw [hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore2 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion17_split_eq (s6.readReg64 .x0))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun df_10 => SepWPp.exists_elim fun df_8 => SepWPp.exists_elim fun df_0 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6_s]; exact hsp_align
  rcases hcs6 with ⟨hx19_cs6, _, _, _, _, hx24_cs6, hx25_cs6, hx26_cs6, _, _, _, hvregs_cs6⟩
  have hx19_6 : s6.readReg64 .x19 = coroPtr := hx19_cs6.trans hx19_5
  have hx24_6 : s6.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs6.trans (hx24_5.trans hx24_4)
  have hx25_6 : s6.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs6.trans hx25_5
  have hx26_6 : s6.readReg64 .x26 = outPtr := hx26_cs6.trans (hx26_5.trans hx26_4)
  have hstep7 := p3_err_nondup_d_placed_wp A lim
    (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b))
    ext s6 coroPtr (s6.readReg64 .x0)
    0x6974707972636564#64 0x656c696166206e6f#64 df_0 df_8 (speTag e) w0 w1 w2 df_10 (w3.extractLsb' 0 8)
    hdf_ne hpc6 hrun6 hsp6_align rfl hx19_6
  rw [hsp6_s] at hstep7
  refine bind_sepWP_lscro_frame_err hcro6 hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx19_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7, hvregs_7⟩
  have hsp7_s : s7.sp = s.sp := hsp7_6
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7_s] using hsp_align
  refine SepWPp.drop_frame
    (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s6.readReg64 .x0))) (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus) ?_
  have hstack_drop2 : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_lscl_nopanic_err
    (x := ((⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost),
           M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b)))
    (T := sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗
          A.pool lim (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b)) s7 ∗
          stackAt s.sp dropSessionStructure2Stack)
    hcro7 hDropSS3 hpc7 hrun7 hsp7_al hx30_7 (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_s])
    (And.intro hx0_7 (show LsRetAddr624 (s7.readReg64 .lr) by
      change LsRetAddr624 (s7.readReg64 .x30)
      rw [hx30_7]
      exact lsRetAddr624_blockPlacement_base_add 518 0x34dc#64 (by decide) (by decide)))
    (by sep_focus) (hnext := fun s8 hpc8 hrun8 hsp8_7 _ hcs8 hcro8 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_s]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_drop1 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜s8.trace = s7.trace ∧ FreeOnlyEvs evs_drop1⌝)
    (P₂ := ⌜s8.trace = s7.trace ∧ FreeOnlyEvs evs_drop1⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨htr8_7, hevs_drop1⟩ => ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7.trans hsp7_s
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8_s]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, hx28_cs8, _, hvregs_cs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx24_8 : s8.readReg64 .x24 = s8.sp + 0x370#64 := by rw [hx24_cs8, hx24_7, hx24_6, hsp8_s]
  have hx25_8 : s8.readReg64 .x25 = s8.sp + 0x210#64 := by rw [hx25_cs8, hx25_7, hx25_6, hsp8_s]
  have hx26_8 : s8.readReg64 .x26 = outPtr := hx26_cs8.trans (hx26_7.trans hx26_6)
  have hx28_8 : s8.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs8.trans hx28_7
  have htail := stageP3_err_tail_nondup_dec_prevEmpty_placed_ok ext hdealloc hDropSS3
    (M.stepEvents evs_drop1 (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b)))
    s0 s8 coroPtr outPtr errsPtr 17#64 (s6.readReg64 .x0) 17#64 w3' w4 e he_npan b_2c0 g recG recSt
    hcro8 hpc8 hrun8 hsp8_align (htr8_7.trans (htr7_6.trans (htr6_5.trans htr5_0)))
    hx19_8 hx24_8 hx25_8 hx26_8 hx28_8
  rw [hsp8_s] at htail
  refine ret_sepWPp_frame_false htail (by sep_focus)
    fun sf _ _ _ ⟨evs_tail, hevs_tail, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A.repAlloc
    outPtr (s6.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  rw [RustCliAllocBudget.repAlloc_live] at hrec
  have hstack_restore3 : memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
      stackAt s.sp growOneSpeStack := by rw [hstack_drop2]; exact Entails.refl _
  have hst_eq :
      M.stepEvents evs_tail
        (M.stepEvents evs_drop1
          (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents (rustAllocEvents 192 8) st_b))) =
      M.stepEvents (rustAllocEvents 192 8 ++ (rustAllocEvents 17 1 ++ (evs_drop1 ++ evs_tail))) st_b := by
    rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
  rw [hst_eq] at hPf
  refine ⟨rustAllocEvents 192 8 ++ (rustAllocEvents 17 1 ++ (evs_drop1 ++ evs_tail)),
    fromVPostTdEnv_of_nondup hevs_drop1 hevs_tail, ?_, hspf, htrf, hcc, hcrof,
    by rw [hvregs_f, hvregs_cs8, hvregs_7, hvregs_cs6, hvregs_5, hvregs_cs4, hvregs_3, hvregs_cs2, hvregs_1]⟩
  unfold stageP3ErrPostPrevEmptyM3Placed
  unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPostPrevEmptyM3Placed
  rw [hrec_err]
  change _ ⊢
    (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
      ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
    ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
    memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
    FromRecordCallees.lsLogOff ∗
    recordResultAt A.repAlloc outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
    memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
    memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
    decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
    A.pool lim (M.stepEvents (rustAllocEvents 192 8 ++ (rustAllocEvents 17 1 ++ (evs_drop1 ++ evs_tail))) st_b) sf ∗
    stackAt s.sp growOneSpeStack
  have herrs : ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ⊢
      ∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
        ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
        ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
    Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr
      (Entails.sepExists_right 1#64 (Entails.refl _)))
  refine Entails.trans (entails_replace_sub hPf (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub herrs (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hrec (by sep_focus) rfl) ?_
  exact entails_replace_sub hstack_restore3 (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_prevEmpty_full_placed_ok [LibsignalFullPlacement] :
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget.StageP3Sub5ErrPrevEmptyFullPlacedStmt := by
  intro M A lim ext hshim halloc hdealloc _hmemcpy hGrow hDropSS3 _hpanic
    st_b s0 s coroPtr outPtr initErrsPtr hfits hinit_ne e he_npan b_2c0 g G₂ recG st₂ recSt
    hfr hpc hrun hsp_align htr hx19 hx24
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux.lscro_of_frozen hfr
  by_cases htag23 : speTag e = speWord 23
  · obtain ⟨ratVer, counter, rfl⟩ := speTag_eq_speWord23_iff.mp htag23
    unfold stageP3ErrPrePrevEmptyM3Placed
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPrePrevEmptyM3Placed
    change SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A.repAlloc (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st_b s ∗
       stackAt s.sp growOneSpeStack) _ _
    have hstack_drop2 : stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
      stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
    rw [hstack_drop2]
    have hdup := stageP3_sub5_err_dup_prevEmpty_placed_ok ext hdealloc hDropSS3 st_b
      s0 s coroPtr outPtr initErrsPtr ratVer counter b_2c0 g G₂ recG st₂ recSt
      hcro hpc hrun hsp_align htr hx19 hx24
    refine ret_sepWPp_frame_false hdup (by sep_focus)
      fun sf _ _ _ ⟨evs_dup, hevs_dup, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
    have herrs : ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
        ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ⊢
        ∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 0#64 (Entails.sepExists_right initErrsPtr
        (Entails.sepExists_right 0#64 (Entails.refl _)))
    have hstack_restore : memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
        stackAt s.sp growOneSpeStack := by rw [hstack_drop2]; exact Entails.refl _
    refine ⟨evs_dup, Or.inl hevs_dup, ?_, hspf, htrf, hcc, hcrof, hvregs_f⟩
    unfold stageP3ErrPostPrevEmptyM3Placed
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPostPrevEmptyM3Placed
    dsimp only [SessionState.recordError]
    change _ ⊢
      (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
        ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
        ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
      memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
      FromRecordCallees.lsLogOff ∗
      recordResultAt A.repAlloc outPtr (.error (.duplicatedMessage ratVer counter)) ∗
      memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
      memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
      decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
      A.pool lim (M.stepEvents evs_dup st_b) sf ∗
      stackAt s.sp growOneSpeStack
    refine Entails.trans (entails_replace_sub hPf (by sep_focus) rfl) ?_
    refine Entails.trans (entails_replace_sub herrs (by sep_focus) rfl) ?_
    exact entails_replace_sub hstack_restore (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))
  · exact stageP3_sub5_err_nondup_prevEmpty_full_placed_ok ext hshim halloc hdealloc
      hGrow hDropSS3 st_b
      s0 s coroPtr outPtr initErrsPtr hfits hinit_ne e he_npan htag23
      b_2c0 g G₂ recG st₂ recSt hfr hpc hrun hsp_align htr hx19 hx24

theorem stageP3Gen_prevEmpty_vregs_full_placed_ok_of_clone [LibsignalFullPlacement]
    (hClone : CloneGenVRegsPlacedStmt)
    (hVerNeSub :
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget.StageP3VerNePrevEmptyFullPlacedStmt) :
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget.StageP3PrevEmptyVRegsM3FullPlacedStmt :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget.stageP3Gen_prevEmpty_vregs_full_placed_ok_of_parts
    hClone stageP3_sub5_err_prevEmpty_full_placed_ok hVerNeSub

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudget
