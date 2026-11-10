/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4UnwindPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.FetchDecrypt
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwind
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Stage P3 and Stage P4 Error Epilogues on 1-Element `previous_sessions`

Threads `A.pool`, `rustCliDeallocBudgetSpec`, and `dropSessionStructureLocal2Spec` (`FreeOnlyEvs`)
across the `[LibsignalPlacement]` Stage P3 common error epilogue (`lsmpl.base 512 → s0.readReg64 .x30`)
and Stage P4 error unwinds (`+0x3588` and `+0x550 → s0.readReg64 .x30`) over `prevVecAt [enc]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrAPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (LibsignalPlacement lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost dropSessionStructureLocal2Stack
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts (words6At)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved decryptPrekeySavedRegsAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  ClosureCalleeSavedP4 PanicOomProp decryptPrekeySavedRegsAt_add_cd0
  dropSessionStructure2Stack eq_of_sep_emp outPtr48_split_eq
  repack20_32_64_64_to_64_64_32 sp370_36_err_fold words3_repack_w32_2w64_w32
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp (weaken_frame)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.SepWPp (bind_false_frame with_steps)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  coro280_words3_entails_memRegion24 memRegion36_eq_exists_stagingCells
  memRegion48_eq_exists_pollCells p4_sessionStateAt_expose_cap
  p4_sessionStateAt_expose_cap_ne pollCellsAt ptextBuf_dealloc_nonzero
  ptextBuf_dealloc_zero stageP4ErrUnwindStack stack_errUnwind_to_alloc
  stack_errUnwind_to_dropSS3 stagingCellsAt stagingCellsAt_entails_memRegion36
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  HdrP hdrP_coro_344_entails_368 prevVecAt
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4UnwindPlacedBudget (
  bind_sepWP_lscro_frame call_lscro_nopanic p4_err_3588_vregs_placed_wp
  p4_err_550_nonzero_vregs_placed_wp p4_err_550_zero_vregs_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsAPlacedBudget (
  dpClosureEntryP34Placed p3_err_tail_b_prev1_of_dealloc_placed_wp
)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsAPlacedBudget (
  dpClosureEntryP34Placed
)

/-! ## Stage P3 Common Error Epilogue (`lsmpl.base 512 → s0.readReg64 .x30`) -/

/-- Budget-threaded placed Stage P3 common error epilogue (`lsmpl.base 512 → s0.readReg64 .x30`)
dropping `sessionStateAt` and 1-element `prevVecAt [enc]` along `FreeOnlyEvs`. -/
theorem stageP3_err_tail_common_prev1_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (s0 s : State)
    (coroPtr outPtr errTag prevCap prevPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
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
       A.pool lim st0 s ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ words6At outPtr errTag w0 w1 w2 w3 w4 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0) := by
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  refine call_lscro_nopanic
    (x := ((⟨coroPtr + 0xf8#64, recG, recSt⟩ : DropSessionStructureGhost), st0))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ A.pool lim st0 s ∗
          stackAt s.sp dropSessionStructure2Stack)
    hcro (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hDropSS3)
    hpc hrun hsp_al hx30 (by dsimp only [dropSessionStructureLocal2Spec])
    (And.intro hx0 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s.readReg64 .lr) by
      simp (config := { decide := true }) [show s.readReg64 .lr = _ from hx30, wp_norm]))
    (by sep_focus)
    (hnext := fun s1 hpc1 hrun1 hsp1_s _ hcs1 hcro1 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_ss => SepWPp.pure_elim fun ⟨htr1_s, hfree_ss⟩ => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  rcases hcs1 with ⟨hx19_cs1, _, _, hx22_cs1, _, _, hx25_cs1, hx26_cs1, _, hx28_cs1, _, hvregs_cs1⟩
  have hx19_1 : s1.readReg64 .x19 = coroPtr := hx19_cs1.trans hx19
  have hx22_1 : s1.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64 := hx22_cs1.trans hx22
  have hx25_1 : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_cs1, hx25, hsp1_s]
  have hx26_1 : s1.readReg64 .x26 = outPtr := hx26_cs1.trans hx26
  have hx28_1 : s1.readReg64 .x28 = errTag := hx28_cs1.trans hx28
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64) (w2.extractLsb' 32 32) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine weaken_frame (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  have hstack_alloc :
      stackAt s.sp dropSessionStructureLocal2Stack =
        memRegion (s.sp - 4192#64) 96 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 96 (by decide)
  refine weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
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
  have hstep2 := p3_err_tail_b_prev1_of_dealloc_placed_wp ext hdealloc (M.stepEvents evs_ss st0)
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
  refine bind_sepWP_lscro_frame hcro1 hstep2 (by sep_focus)
    fun sf hpcf hrunf hcrof hregsf => ?_
  rcases hregsf with ⟨hspf_s, htrf_1, hvregs_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_prev =>
    weaken_frame (Entails.refl (⌜FreeOnlyEvs evs_prev⌝)) (by sep_focus)
      (SepWPp.pure_elim fun hfree_prev => ?_)
  refine weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
  refine weaken_frame
    (hdrP_coro_344_entails_368 coroPtr prevCap prevPtr 1#64) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
  refine weaken_frame
    (sp370_36_err_fold s.sp
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      w3 w4 (w2.extractLsb' 32 32))
    (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
  refine weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  refine weaken_frame hout_words (by sep_focus) ?_
  have hevs_eq :
      M.stepEvents evs_prev (M.stepEvents evs_ss st0) =
      M.stepEvents (evs_ss ++ evs_prev) st0 :=
    (M.stepEvents_append evs_ss evs_prev st0).symm
  exact SepWPp.done hpcf hrunf
    ⟨evs_ss ++ evs_prev, FreeOnlyEvs.append hfree_ss hfree_prev,
     by rw [← hevs_eq]; exact Entails.of_eq (eq_of_sep_emp (by sep_focus)),
     hspf_s, htrf_1.trans (htr1_s.trans htr),
     ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
      True.intro⟩,
     hcrof, hvregs_f.trans hvregs_cs1⟩

theorem stageP3_err_tail_common_prev1_withPanics_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ∀ (st0 : M.σ) (s0 s : State)
      (coroPtr outPtr errTag prevCap prevPtr w0 w1 w2 w3 w4 : BitVec 64)
      (b_2c0 : BitVec 8) (enc : List (BitVec 8))
      (recG : SessionGhost) (recSt : SessionState (List (BitVec 8))),
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = lsmpl.base 512 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.trace = s0.trace →
      s.readReg64 .x0 = coroPtr + 0xf8#64 →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64 →
      s.readReg64 .x25 = s.sp + 0x210#64 →
      s.readReg64 .x26 = outPtr →
      s.readReg64 .x28 = errTag →
      s.readReg64 .x30 = dpClosureEntryP34Placed + 0x359c#64 →
      SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
        (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
         prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
         ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
         ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
         ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
         ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
         ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
         A.pool lim st0 s ∗
         stackAt s.sp dropSessionStructure2Stack)
        (fun sf P_f =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (P_f ⊢
              memRegion (coroPtr + 0xe0#64) 368 ∗
              ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ words6At outPtr errTag w0 w1 w2 w3 w4 ∗
              memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
              A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
            sf.sp = s.sp + 0xcd0#64 ∧
            sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
            LibsignalCodeRoLoaded lsmpl sf.mem ∧
            calleeSavedVRegs sf = calleeSavedVRegs s)
        (PanicOomProp s0) :=
  stageP3_err_tail_common_prev1_placed_ok (Rust.withPanics ext)

/-! ## Stage P4 Error Unwind (`+0x3588` / `+0x550 → s0.readReg64 .x30`) -/

/-- Placed `+0x550 → +0x3588` step when `ptCap = 0#64`, preserving `A.pool lim st`. -/
theorem p4_err_550_zero_ext_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr slot ptPtr o2 o3 o4 o5 u_370 u_378 u_380 u_388 : BitVec 64)
    (o6 u_390 : BitVec 32)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x550#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = slot) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext) (dpClosureEntryP34Placed + 0x3588#64) s
      (((coroPtr + 0x280#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       stagingCellsAt slot o2 o3 o4 o5 o6 ∗
       stagingCellsAt (s.sp + 0x370#64) u_370 u_378 u_380 u_388 u_390 ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x280#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
          stagingCellsAt slot o2 o3 o4 o5 o6 ∗
          stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p4_err_550_zero_vregs_placed_wp (A := A) (lim := lim) ext st s coroPtr slot ptPtr
    o2 o3 o4 o5 u_370 u_378 u_380 u_388 o6 u_390 hpc hrun hsp_align hx8 hx19 hx24

/-- Placed `+0x550 → +0x3588` step when `ptCap ≠ 0#64`, deallocating the plaintext buffer via
`rustCliDeallocBudgetSpec`. -/
theorem p4_err_550_nonzero_ext_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr slot ptCap ptPtr o2 o3 o4 o5 u_370 u_378 u_380 u_388 : BitVec 64)
    (o6 u_390 : BitVec 32)
    (hcap_nz : ptCap ≠ 0#64)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x550#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = slot) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext) (dpClosureEntryP34Placed + 0x3588#64) s
      (((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗ ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       stagingCellsAt slot o2 o3 o4 o5 o6 ∗
       stagingCellsAt (s.sp + 0x370#64) u_370 u_378 u_380 u_388 u_390 ∗
       A.live ptPtr ptCap.toNat 1 ∗ memRegion ptPtr ptCap.toNat ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗ ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
          stagingCellsAt slot o2 o3 o4 o5 o6 ∗
          stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
          A.pool lim (M.stepEvents (rustDeallocEvents ptCap.toNat 1) st) s1 ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p4_err_550_nonzero_vregs_placed_wp (A := A) (lim := lim) ext hdealloc st s coroPtr slot ptCap ptPtr
    o2 o3 o4 o5 u_370 u_378 u_380 u_388 o6 u_390 hcap_nz hpc hrun hsp_align hx8 hx19 hx24

/-- Placed `+0x3588 → lsmpl.base 512` (`dropSessionStructure3`) step preserving `A.pool lim st`. -/
theorem p4_err_3588_ext_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr ssCap : BitVec 64)
    (hcap_ne : ssCap + 1#64 ≠ 0#64)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x3588#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryP34Placed + 0x359c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p4_err_3588_vregs_placed_wp (A := A) (lim := lim) ext st s coroPtr ssCap hcap_ne hpc hrun hx19

/-- Budget-threaded placed Stage P4 `+0x3588 → s0.readReg64 .x30` unwind on 1-element `prevVecAt [enc]`
producing `FreeOnlyEvs`. -/
theorem stageP4_err_unwind_3588_prev1_vregs_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (s0 s : State)
    (coroPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 : BitVec 64)
    (w_22 o6 : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hsp_ub : stageP4ErrUnwindStack ≤ 2 ^ 64)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G st ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st0 s ∗
       stackAt s.sp stageP4ErrUnwindStack)
      (fun sf P_f =>
        Steps (lsProg_518 ext) s sf ∧
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt s.sp stageP4ErrUnwindStack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s.trace ∧
          ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  refine with_steps ?_
  refine weaken_frame
    (p4_sessionStateAt_expose_cap_ne A.repAlloc (coroPtr + 0xf8#64) G st) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hcap_ne => ?_
  have hstep1 := p4_err_3588_ext_placed_wp (A := A) (lim := lim) ext st0 s coroPtr G.localIk.cap
    hcap_ne hpc hrun hx19
  refine bind_sepWP_lscro_frame hcro hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hlr1, hvregs1⟩
  refine weaken_frame
    (Entails.of_eq (p4_sessionStateAt_expose_cap A.repAlloc (coroPtr + 0xf8#64) G st).symm)
    (by sep_focus) ?_
  refine weaken_frame
    (Entails.of_eq (stack_errUnwind_to_dropSS3 s.sp hsp_ub)) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  simp only [sepConj_assoc]
  refine call_lscro_nopanic
    (x := ((⟨coroPtr + 0xf8#64, G, st⟩ : DropSessionStructureGhost), st0))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G st ∗ A.pool lim st0 s1 ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
    hcro1 (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hDropSS3)
    hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
    (And.intro hx0_1 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s1.readReg64 .lr) by
      simp (config := { decide := true }) [show s1.readReg64 .lr = _ from hlr1, wp_norm]))
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_ss => SepWPp.pure_elim fun ⟨htr2_1, hfree_ss⟩ => ?_
  refine weaken_frame
    (Entails.of_eq (stack_errUnwind_to_dropSS3 s.sp hsp_ub).symm) (by sep_focus) ?_
  refine weaken_frame
    (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub)) (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = w_22.zeroExtend 64 := hx22_cs2.trans (hx22_1.trans hx22)
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = errTag := hx28_cs2.trans (hx28_1.trans hx28)
  refine weaken_frame
    (Entails.of_eq (memRegion48_eq_exists_pollCells outPtr)) (by sep_focus) ?_
  refine weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun o6_u => SepWPp.exists_elim fun o5_u =>
    SepWPp.exists_elim fun o4_u => SepWPp.exists_elim fun o3_u =>
    SepWPp.exists_elim fun o2_u => SepWPp.exists_elim fun o1_u =>
    SepWPp.exists_elim fun w0_u => ?_
  have hstep3 := p3_err_tail_b_prev1_of_dealloc_placed_wp ext hdealloc
    (M.stepEvents evs_ss st0) s2 coroPtr outPtr errTag
    prevCap prevPtr o2 o3 o4 o5 w0_u o2_u o3_u o4_u o5_u
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    w_22 o6 o1_u o6_u b_2c0 enc
    hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
  rw [hsp2] at hstep3
  unfold pollCellsAt stagingCellsAt
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hstep3 ⊢
  refine bind_sepWP_lscro_frame hcro2 hstep3 (by sep_focus)
    fun sf hpcf hrunf hcrof hregsf => ?_
  rcases hregsf with ⟨hspf, htrf, hvregsf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f,
    hx27f, hx28f, hx29f, _⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_prev =>
    weaken_frame (Entails.refl (⌜FreeOnlyEvs evs_prev⌝)) (by sep_focus)
      (SepWPp.pure_elim fun hfree_prev => ?_)
  refine weaken_frame
    (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub).symm) (by sep_focus) ?_
  refine weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  have h370 := stagingCellsAt_entails_memRegion36 (s.sp + 0x370#64) o2 o3 o4 o5 o6
  unfold stagingCellsAt at h370
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h370
  refine weaken_frame h370 (by sep_focus) ?_
  refine weaken_frame
    (hdrP_coro_344_entails_368 coroPtr prevCap prevPtr 1#64) (by sep_focus) ?_
  have hevs_eq :
      M.stepEvents evs_prev (M.stepEvents evs_ss st0) =
      M.stepEvents (evs_ss ++ evs_prev) st0 :=
    (M.stepEvents_append evs_ss evs_prev st0).symm
  refine SepWPp.done hpcf hrunf
    ⟨evs_ss ++ evs_prev, FreeOnlyEvs.append hfree_ss hfree_prev,
     by rw [← hevs_eq]; exact Entails.of_eq (by sep_ac_rfl), ?_⟩
  refine ⟨hspf, by rw [htrf, htr2_1, htr1], ?_,
    hvregsf.trans (hvregs_cs2.trans (hvregs1.trans hvregs)), hcrof⟩
  exact ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, trivial⟩

theorem stageP4_err_unwind_3588_prev1_vregs_withPanics_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ∀ (st0 : M.σ) (s0 s : State)
      (coroPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 : BitVec 64)
      (w_22 o6 : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
      (G : SessionGhost) (st : SessionState (List (BitVec 8)))
      (Qp : State → SepProp → Prop),
      stageP4ErrUnwindStack ≤ 2 ^ 64 →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpClosureEntryP34Placed + 0x3588#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x22 = w_22.zeroExtend 64 →
      s.readReg64 .x25 = s.sp + 0x210#64 →
      s.readReg64 .x26 = outPtr →
      s.readReg64 .x28 = errTag →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
        (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G st ∗
         prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
         ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
         memRegion outPtr 48 ∗
         stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
         decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
         A.pool lim st0 s ∗
         stackAt s.sp stageP4ErrUnwindStack)
        (fun sf P_f =>
          Steps (lsProg_518 (Rust.withPanics ext)) s sf ∧
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (P_f ⊢
              pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
              memRegion (coroPtr + 0xe0#64) 368 ∗
              ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
              memRegion (s.sp + 0x370#64) 36 ∗
              decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
              A.pool lim (M.stepEvents evs st0) sf ∗
              stackAt s.sp stageP4ErrUnwindStack) ∧
            sf.sp = s.sp + 0xcd0#64 ∧
            sf.trace = s.trace ∧
            ClosureCalleeSavedP4 s0 sf ∧
            calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
            LibsignalCodeRoLoaded lsmpl sf.mem)
        Qp :=
  stageP4_err_unwind_3588_prev1_vregs_placed_ok (Rust.withPanics ext)

/-- Budget-threaded placed Stage P4 `+0x550 → s0.readReg64 .x30` unwind on 1-element `prevVecAt [enc]`
producing `FreeOnlyEvs`. -/
theorem stageP4_err_unwind_550_prev1_vregs_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (s0 s : State)
    (coroPtr slot ptCap ptPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 : BitVec 64)
    (w_22 o6 : BitVec 32) (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : stageP4ErrUnwindStack ≤ 2 ^ 64)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x550#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = slot)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (ptPtr ↦ₛ pt) ∗
       (if ptCap = 0#64 then emp
        else A.live ptPtr ptCap.toNat 1 ∗
          memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       stagingCellsAt slot o2 o3 o4 o5 o6 ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G st ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st0 s ∗
       stackAt s.sp stageP4ErrUnwindStack)
      (fun sf P_f =>
        Steps (lsProg_518 ext) s sf ∧
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            memRegion (coroPtr + 0x280#64) 24 ∗
            memRegion slot 36 ∗
            memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt s.sp stageP4ErrUnwindStack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s.trace ∧
          ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  refine with_steps ?_
  refine weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x370#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_390 => SepWPp.exists_elim fun u_388 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  by_cases hcap_z : ptCap = 0#64
  · subst hcap_z
    refine weaken_frame (ptextBuf_dealloc_zero A.repAlloc ptPtr pt hpt_le)
      (by sep_focus) ?_
    simp only [emp_sepConj, sepConj_emp, sepConj_assoc]
    have hstep0 := p4_err_550_zero_ext_placed_wp (A := A) (lim := lim) ext st0 s coroPtr slot ptPtr
      o2 o3 o4 o5 u_370 u_378 u_380 u_388 o6 u_390
      hpc hrun hsp_align hx8 hx19 hx24
    refine bind_sepWP_lscro_frame hcro hstep0 (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hvregs1⟩
    refine weaken_frame
      (coro280_words3_entails_memRegion24 coroPtr 0#64 ptPtr (BitVec.ofNat 64 pt.length))
      (by sep_focus) ?_
    refine weaken_frame
      (stagingCellsAt_entails_memRegion36 slot o2 o3 o4 o5 o6) (by sep_focus) ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hx22_1' : s1.readReg64 .x22 = w_22.zeroExtend 64 := hx22_1.trans hx22
    have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hx25, hsp1]
    have hx26_1' : s1.readReg64 .x26 = outPtr := hx26_1.trans hx26
    have hx28_1' : s1.readReg64 .x28 = errTag := hx28_1.trans hx28
    have htail := stageP4_err_unwind_3588_prev1_vregs_placed_ok ext hdealloc hDropSS3 st0 s0 s1
      coroPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 w_22 o6 b_2c0 enc G st (fun _ _ => False)
      hsp_ub hcro1 hpc1 hrun1 hsp1_align hx19_1 hx22_1' hx25_1' hx26_1' hx28_1'
      (hvregs1.trans hvregs)
    rw [hsp1] at htail
    refine bind_false_frame htail (by sep_focus)
      fun sf P_f hpcf hrunf ⟨_, evs_unw, hfree_unw, hentf, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hentf) ?_
    refine SepWPp.done hpcf hrunf ⟨evs_unw, hfree_unw, Entails.of_eq (by sep_ac_rfl), ?_⟩
    exact ⟨hspf, by rw [htrf, htr1], hcsf, hvregsf, hcrof⟩
  · have hpt_dealloc :
        (ptPtr ↦ₛ pt) ∗
          (if ptCap = 0#64 then emp
           else A.live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ⊢
        A.live ptPtr ptCap.toNat 1 ∗ memRegion ptPtr ptCap.toNat := by
      simpa only [RustCliAllocBudget.repAlloc_live] using
        ptextBuf_dealloc_nonzero A.repAlloc ptCap ptPtr pt hcap_z hpt_le
    refine weaken_frame hpt_dealloc (by sep_focus) ?_
    refine weaken_frame
      (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub)) (by sep_focus) ?_
    simp only [sepConj_assoc]
    have hstep0 := p4_err_550_nonzero_ext_placed_wp (A := A) (lim := lim) ext hdealloc st0 s
      coroPtr slot ptCap ptPtr
      o2 o3 o4 o5 u_370 u_378 u_380 u_388 o6 u_390
      hcap_z hpc hrun hsp_align hx8 hx19 hx24
    refine bind_sepWP_lscro_frame hcro hstep0 (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hvregs1⟩
    refine weaken_frame
      (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub).symm) (by sep_focus) ?_
    refine weaken_frame
      (coro280_words3_entails_memRegion24 coroPtr ptCap ptPtr (BitVec.ofNat 64 pt.length))
      (by sep_focus) ?_
    refine weaken_frame
      (stagingCellsAt_entails_memRegion36 slot o2 o3 o4 o5 o6) (by sep_focus) ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hx22_1' : s1.readReg64 .x22 = w_22.zeroExtend 64 := hx22_1.trans hx22
    have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hx25, hsp1]
    have hx26_1' : s1.readReg64 .x26 = outPtr := hx26_1.trans hx26
    have hx28_1' : s1.readReg64 .x28 = errTag := hx28_1.trans hx28
    have htail := stageP4_err_unwind_3588_prev1_vregs_placed_ok ext hdealloc hDropSS3
      (M.stepEvents (rustDeallocEvents ptCap.toNat 1) st0) s0 s1
      coroPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 w_22 o6 b_2c0 enc G st (fun _ _ => False)
      hsp_ub hcro1 hpc1 hrun1 hsp1_align hx19_1 hx22_1' hx25_1' hx26_1' hx28_1'
      (hvregs1.trans hvregs)
    rw [hsp1] at htail
    refine bind_false_frame htail (by sep_focus)
      fun sf P_f hpcf hrunf ⟨_, evs_unw, hfree_unw, hentf, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hentf) ?_
    have hevs_eq :
        M.stepEvents evs_unw (M.stepEvents (rustDeallocEvents ptCap.toNat 1) st0) =
        M.stepEvents (rustDeallocEvents ptCap.toNat 1 ++ evs_unw) st0 :=
      (M.stepEvents_append (rustDeallocEvents ptCap.toNat 1) evs_unw st0).symm
    refine SepWPp.done hpcf hrunf
      ⟨rustDeallocEvents ptCap.toNat 1 ++ evs_unw,
       FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 ptCap.toNat) hfree_unw,
       by rw [← hevs_eq]; exact Entails.of_eq (by sep_ac_rfl), ?_⟩
    exact ⟨hspf, by rw [htrf, htr1], hcsf, hvregsf, hcrof⟩

theorem stageP4_err_unwind_550_prev1_vregs_withPanics_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ∀ (st0 : M.σ) (s0 s : State)
      (coroPtr slot ptCap ptPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 : BitVec 64)
      (w_22 o6 : BitVec 32) (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
      (G : SessionGhost) (st : SessionState (List (BitVec 8)))
      (Qp : State → SepProp → Prop),
      pt.length ≤ ptCap.toNat →
      stageP4ErrUnwindStack ≤ 2 ^ 64 →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpClosureEntryP34Placed + 0x550#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x8 = slot →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x22 = w_22.zeroExtend 64 →
      s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 →
      s.readReg64 .x26 = outPtr →
      s.readReg64 .x28 = errTag →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
        (((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
         ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
         ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
         (ptPtr ↦ₛ pt) ∗
         (if ptCap = 0#64 then emp
          else A.live ptPtr ptCap.toNat 1 ∗
            memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
         stagingCellsAt slot o2 o3 o4 o5 o6 ∗
         memRegion (s.sp + 0x370#64) 36 ∗
         sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G st ∗
         prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
         ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
         memRegion outPtr 48 ∗
         decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
         A.pool lim st0 s ∗
         stackAt s.sp stageP4ErrUnwindStack)
        (fun sf P_f =>
          Steps (lsProg_518 (Rust.withPanics ext)) s sf ∧
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (P_f ⊢
              pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
              memRegion (coroPtr + 0xe0#64) 368 ∗
              ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
              memRegion (coroPtr + 0x280#64) 24 ∗
              memRegion slot 36 ∗
              memRegion (s.sp + 0x370#64) 36 ∗
              decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
              A.pool lim (M.stepEvents evs st0) sf ∗
              stackAt s.sp stageP4ErrUnwindStack) ∧
            sf.sp = s.sp + 0xcd0#64 ∧
            sf.trace = s.trace ∧
            ClosureCalleeSavedP4 s0 sf ∧
            calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
            LibsignalCodeRoLoaded lsmpl sf.mem)
        Qp :=
  stageP4_err_unwind_550_prev1_vregs_placed_ok (Rust.withPanics ext)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrAPlacedBudget
