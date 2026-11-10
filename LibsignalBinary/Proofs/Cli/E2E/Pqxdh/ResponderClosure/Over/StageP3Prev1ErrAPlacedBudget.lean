/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1ErrAPlaced
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Stage P3 Duplicate and Non-Duplicate Error Tails on 1-Element `previous_sessions`

Proves budget-threaded `[LibsignalPlacement]` duplicate-message and non-duplicate Stage P3 error
tails over a 1-element `prevVecAt [enc]`, advancing `A.pool` along `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1ErrAPlacedBudget

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
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  HdrP hdrP_coro_344_entails_368 prevVecAt
)
open CryptoVerification.CliHandshake.RespClosurePlaced CryptoVerification.CliHandshake.Placed
open CryptoVerification.LibsignalTripleRatchet.Getters hiding dropSpeSpec
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux (
  ret_sepWPp_frame_false sepWPp_lift_false_qp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux (
  bind_sepWP_lscro_frame_err call_lscl_nopanic_err call_lscl_ro_nopanic_err
  drop_spe2_placed_ok_at_of_dealloc freeOnlyEvs_append freeOnlyEvs_dealloc
  p3_err_dup_placed_wp p3_err_tail_dup_a_placed_wp
  p3_err_tail_nondup_a1_placed_wp p3_err_tail_nondup_a2_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsAPlacedBudget (
  dpClosureEntryP34Placed p3_err_tail_b_prev1_of_dealloc_placed_wp
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpec)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsAPlacedBudget (
  dpClosureEntryP34Placed
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## Common Error Epilogue (`lsmpl.base 512 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded 1-element `previous_sessions` common error epilogue
(`lsmpl.base 512 → s0.readReg64 .x30`) with `Qp := fun _ _ => False`, producing `FreeOnlyEvs`. -/
theorem stageP3_err_tail_common_prev1_false_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State)
    (coroPtr outPtr errTag prevCap prevPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 512) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 = dpClosureEntryP34Placed + 0x359c#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64) (w2.extractLsb' 32 32) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (P3P4.outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  have hstack_alloc :
      stackAt s.sp dropSessionStructure2Stack =
        memRegion (s.sp - 4192#64) 96 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 96 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
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
  have hstep2 := p3_err_tail_b_prev1_of_dealloc_placed_wp ext hdealloc (M.stepEvents evs_ss st_b)
    s1 coroPtr outPtr errTag prevCap prevPtr
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0 enc
    hpc1 hrun1 hsp1_align hx19_1 hx22_1 hx25_1 hx26_1 hx28_1
  rw [hsp1_s] at hstep2
  refine bind_sepWP_lscro_frame_err hcro1 hstep2 (by sep_focus)
    fun sf hpcf hrunf hcrof hregsf => ?_
  rcases hregsf with ⟨hspf_s, htrf_1, hvregs_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_prev => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜FreeOnlyEvs evs_prev⌝) (P₂ := ⌜FreeOnlyEvs evs_prev⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hfree_prev => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (hdrP_coro_344_entails_368 coroPtr prevCap prevPtr 1#64) (by sep_focus) ?_
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
  have hst_eq :
      M.stepEvents evs_prev (M.stepEvents evs_ss st_b) =
      M.stepEvents (evs_ss ++ evs_prev) st_b :=
    (M.stepEvents_append evs_ss evs_prev st_b).symm
  rw [hst_eq]
  exact SepWPp.done hpcf hrunf
    ⟨evs_ss ++ evs_prev, freeOnlyEvs_append hevs_ss hfree_prev,
     Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
     hspf_s, htrf_1.trans (htr1_s.trans htr),
     ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
      True.intro⟩,
     hcrof, hvregs_f.trans hvregs_cs1⟩

/-! ## Duplicate-Message Error Tail and Substage P3.5 (`FreeOnlyEvs`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded placed duplicate-message error tail (`+0x34dc → s0.readReg64 .x30`,
`errs.len = 0`) over a 1-element `prevVecAt [enc]`, producing `FreeOnlyEvs`. -/
theorem stageP3_err_tail_dup_prev1_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevCap prevPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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
  have hcommon := stageP3_err_tail_common_prev1_false_placed_ok ext hdealloc hDropSS3 st_b
    s0 s1 coroPtr outPtr 0x8000000000000017#64 prevCap prevPtr w0 w1 w2 w3 w4 b_2c0 enc recG recSt
    hcro1 hpc1 hrun1 hsp1_align (htr1_s.trans htr) hx0_1 hx19_1 hx22_1 hx25_1' (hx26_1.trans hx26) hx28_1 hx30_1
  rw [hsp1_s] at hcommon
  refine ret_sepWPp_frame_false hcommon (by sep_focus)
    fun sf _ _ _ ⟨evs_common, hevs_c, hPf, hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  exact ⟨evs_common, hevs_c,
    entails_replace_sub hPf (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)),
    hspf, htrf, hcc, hcrof, hvregs_f.trans hvregs_1⟩

set_option maxHeartbeats 1200000 in
/-- Budget-threaded placed Substage P3.5 duplicate-message error path (`+0x1cd8 → s0.readReg64 .x30`)
over a 1-element `prevVecAt [enc]`, producing `FreeOnlyEvs`. -/
theorem stageP3_sub5_err_dup_prev1_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevCap prevPtr : BitVec 64)
    (ratVer counter : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A.repAlloc (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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
  have htail := stageP3_err_tail_dup_prev1_placed_ok ext hdealloc hDropSS3
    (M.stepEvents evs_drop1 st_b) s0 s2 coroPtr outPtr errsPtr prevCap prevPtr w0 w1 w2 w3 w4 b_2c0 enc recG recSt
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

/-! ## Non-Duplicate Error Tail (`+0x34dc → s0.readReg64 .x30`, `errs.len = 1`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded placed non-duplicate error tail (`+0x34dc → s0.readReg64 .x30`, `errs.len = 1`)
over a 1-element `prevVecAt [enc]`, producing `FreeOnlyEvs`. -/
theorem stageP3_err_tail_nondup_dec_prev1_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevCap prevPtr w0 w1 w2 w3 w4 : BitVec 64)
    (e : SignalProtocolError) (_he_npan : e ≠ .panic) (b_2c0 : BitVec 8)
    (enc : List (BitVec 8)) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ A.live errsPtr 192 8 ∗
       speAt A.repAlloc (utf8 "decrypt") errsPtr e ∗ memRegion (errsPtr + 0x30#64) 144 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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
  have hcommon := stageP3_err_tail_common_prev1_false_placed_ok ext hdealloc hDropSS3
    (M.stepEvents (rustDeallocEvents 192 8) (M.stepEvents evs_spe st_b))
    s0 s3 coroPtr outPtr 0x8000000000000018#64 prevCap prevPtr w0 w1 w2 w3 w4 b_2c0 enc recG recSt
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

/-! ## Arbitrary-`Qp` and `Rust.withPanics` Corollaries -/

theorem stageP3_err_tail_dup_prev1_anyQp_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevCap prevPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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
      Qp :=
  sepWPp_lift_false_qp (stageP3_err_tail_dup_prev1_placed_ok ext hdealloc hDropSS3 st_b s0 s
    coroPtr outPtr errsPtr prevCap prevPtr w0 w1 w2 w3 w4 b_2c0 enc recG recSt
    hcro hpc hrun hsp_align htr hx19 hx24 hx25 hx26 hx28)

theorem stageP3_sub5_err_dup_prev1_anyQp_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevCap prevPtr : BitVec 64)
    (ratVer counter : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A.repAlloc (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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
      Qp :=
  sepWPp_lift_false_qp (stageP3_sub5_err_dup_prev1_placed_ok ext hdealloc hDropSS3 st_b s0 s
    coroPtr outPtr errsPtr prevCap prevPtr ratVer counter b_2c0 enc G₂ recG st₂ recSt
    hcro hpc hrun hsp_align htr hx19 hx24)

theorem stageP3_err_tail_nondup_dec_prev1_anyQp_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevCap prevPtr w0 w1 w2 w3 w4 : BitVec 64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (b_2c0 : BitVec 8)
    (enc : List (BitVec 8)) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ A.live errsPtr 192 8 ∗
       speAt A.repAlloc (utf8 "decrypt") errsPtr e ∗ memRegion (errsPtr + 0x30#64) 144 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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
      Qp :=
  sepWPp_lift_false_qp (stageP3_err_tail_nondup_dec_prev1_placed_ok ext hdealloc hDropSS3 st_b s0 s
    coroPtr outPtr errsPtr prevCap prevPtr w0 w1 w2 w3 w4 e he_npan b_2c0 enc recG recSt
    hcro hpc hrun hsp_align htr hx19 hx24 hx25 hx26 hx28)

theorem stageP3_err_tail_dup_prev1_withPanics_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevCap prevPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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
      (fun _ _ => False) :=
  stageP3_err_tail_dup_prev1_placed_ok (Rust.withPanics ext) hdealloc hDropSS3 st_b s0 s
    coroPtr outPtr errsPtr prevCap prevPtr w0 w1 w2 w3 w4 b_2c0 enc recG recSt
    hcro hpc hrun hsp_align htr hx19 hx24 hx25 hx26 hx28

theorem stageP3_sub5_err_dup_prev1_withPanics_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevCap prevPtr : BitVec 64)
    (ratVer counter : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A.repAlloc (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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
      (fun _ _ => False) :=
  stageP3_sub5_err_dup_prev1_placed_ok (Rust.withPanics ext) hdealloc hDropSS3 st_b s0 s
    coroPtr outPtr errsPtr prevCap prevPtr ratVer counter b_2c0 enc G₂ recG st₂ recSt
    hcro hpc hrun hsp_align htr hx19 hx24

theorem stageP3_err_tail_nondup_dec_prev1_withPanics_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevCap prevPtr w0 w1 w2 w3 w4 : BitVec 64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (b_2c0 : BitVec 8)
    (enc : List (BitVec 8)) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ A.live errsPtr 192 8 ∗
       speAt A.repAlloc (utf8 "decrypt") errsPtr e ∗ memRegion (errsPtr + 0x30#64) 144 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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
      (fun _ _ => False) :=
  stageP3_err_tail_nondup_dec_prev1_placed_ok (Rust.withPanics ext) hdealloc hDropSS3 st_b s0 s
    coroPtr outPtr errsPtr prevCap prevPtr w0 w1 w2 w3 w4 e he_npan b_2c0 enc recG recSt
    hcro hpc hrun hsp_align htr hx19 hx24 hx25 hx26 hx28

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1ErrAPlacedBudget
