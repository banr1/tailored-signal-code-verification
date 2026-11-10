/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5cPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5c
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 5 (`NoHeaderReceived`) — Part C

Relocatable Block-`333` `FreeOnlyEvs` cloned-`Authenticator` cleanup (`+6520 -> +6500`),
`<PolyDecoder>::from_pb` staging, and `Ok` epilogue (`+6132 -> +8180 -> ret`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5cPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (PolyDecoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (cap_add_one_beq_zero_false chunkedStatesSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (polyDecoderAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (encoderFromPbStack loByte loBytes7 unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved epilogueOutFull epilogueStackGaps epilogueStackSlots overlapWord7
   resultChunkedStatesAt statesFromPbSavedCells statesFromPbStack
   v5a_optProtoPolyDecoderWordsAt v5c_decCellsAt v5c_epilogueOutFull_entails_noHeaderReceived
   v5c_fsp_128_entails_32 v5c_fsp_1888_entails_epilogue v5c_memRegion_136_split
   v5c_memRegion_160_48_split v5c_memRegion_240_1648_split v5c_stagingSlotsPost
   v5c_stagingSlotsPre v9_midQ128 v9_quadAt v9_wordAt)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs
   seq_clean_st subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget v1_dealloc_ok_of_placedHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

@[local simp]
private theorem stripS_readReg32 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (ProofLib.stripS keep s).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

/-! ## Error Deallocation of Cloned `Authenticator` (`+6520..+6564 -> +10484 -> +6500`) -/

/-- `VmPreserved`-strengthened `+10484 -> +6500` step in Block `333`. -/
theorem v5c_step_10484_to_6500_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 10484#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6500#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧ sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x27 = 0#64 ∧
        TraceCalleeSaved sm s0 ∧ VmPreserved s sm) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v5c_step_10484_to_6500_placed (ext := vmTrapHooks)
      s0 (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out P (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx27_m, htr_m⟩ =>
      ⟨hPm, by simpa using hsp_m, by simpa using hx19_m, by simpa using hx27_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩, hvm⟩

theorem v5c_step_10484_to_6500_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 10484#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6500#64) s
      (Rest ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢ Rest ∗ A.pool lim st sm) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x27 = 0#64 ∧
        TraceCalleeSaved sm s0 ∧ VmPreserved s sm) := by
  refine SepWP.mono
    (v5c_step_10484_to_6500_placed (ext := ext) s0 s fsp out (Rest ∗ A.pool lim st s)
      hpc hrun hsp hx19 htrace) ?_
  intro sm Pm _ _ ⟨hPm, hsp_m, hx19_m, hx27_m, htr_m, hvm⟩
  rw [← A.pool_transport lim st s sm hvm] at hPm
  exact ⟨hPm, hsp_m, hx19_m, hx27_m, htr_m, hvm⟩

/-- Budget-threaded error deallocation of cloned `rootKey` (`l1, p1_new`) and `macKey`
    (`l2, p2_new`) at `+6520..+6564 -> +10484 -> +6500`, tracking `FreeOnlyEvs` and
    `AllocCallPreserved`. -/
theorem v5c_dealloc_cloned_auth_6520_to_6500_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (fsp out p1_new p2_new l1 l2 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6520#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = l1) (hx27_1 : s1.readReg64 .x27 = p1_new)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6500#64) s1
      (stackAt fsp allocHookStack ∗
        ((fsp + 136#64) ↦₆₄ p2_new) ∗
        ((fsp + 216#64) ↦₆₄ l2) ∗
        vecCapPtrDealloc A.repAlloc l1 p1_new ∗
        vecCapPtrDealloc A.repAlloc l2 p2_new ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt fsp allocHookStack ∗
            ((fsp + 136#64) ↦₆₄ p2_new) ∗
            ((fsp + 216#64) ↦₆₄ l2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = fsp ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x27 = 0#64 ∧
          TraceCalleeSaved sm s0 ∧
          AllocCallPreserved s1 sm) := by
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc
  dsimp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  change s1.pc = (blkPl_333).base + 6520#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6500#64) s1 _ _
  refine seq_clean_evs
    (mid := (blkPl_333).base + 6540#64)
    (P_evs := fun evs s2 =>
      stackAt fsp allocHookStack ∗
      ((fsp + 136#64) ↦₆₄ p2_new) ∗
      ((fsp + 216#64) ↦₆₄ l2) ∗
      vecCapPtrDealloc A.repAlloc l2 p2_new ∗
      A.pool lim (M.stepEvents evs st) s2 ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = fsp ∧
      s2.readReg64 .x19 = out ∧
      TraceCalleeSaved s2 s0 ∧
      AllocCallPreserved s1 s2)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    by_cases hl1 : (l1 == 0#64) = true
    · apply sepWP_evs_nil
      simp only [hl1, ↓reduceIte, sepConj_emp, emp_sepConj, sepConj_assoc,
        LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      refine align_pre_st
        (by first | rfl | sep_ac_rfl | (simp only [wp_norm, arm64_norm]; (try first | rfl | sep_ac_rfl))) ?_
      wp_done
    · have hl1_f : (l1 == 0#64) = false := Bool.eq_false_iff.mpr hl1
      apply sepWP_evs_dealloc l1.toNat 1
      simp only [hl1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      wp_steps; wp_apply
      have hacp_sf : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by rw [hsp1]; sep_ac_rfl) ?_
      wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, htr2, hacp2⟩
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
    by_cases hl2 : (l2 == 0#64) = true
    · simp only [hl2, ↓reduceIte, sepConj_emp, emp_sepConj, sepConj_assoc]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6500#64) s2
          (stackAt fsp allocHookStack ∗
            ((fsp + 136#64) ↦₆₄ p2_new) ∗
            ((fsp + 216#64) ↦₆₄ l2) ∗
            A.pool lim (M.stepEvents evs1 st) s2 ∗
            Rest)
          (fun sm Pm =>
            (Pm ⊢
              stackAt fsp allocHookStack ∗
              ((fsp + 136#64) ↦₆₄ p2_new) ∗
              ((fsp + 216#64) ↦₆₄ l2) ∗
              A.pool lim (M.stepEvents evs1 st) sm ∗
              Rest) ∧
            sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x27 = 0#64 ∧
            TraceCalleeSaved sm s0 ∧ AllocCallPreserved s2 sm) := by
        wp_steps
        refine align_pre_st
          (by first | rfl | sep_ac_rfl | (simp only [wp_norm, arm64_norm]; (try first | rfl | sep_ac_rfl))) ?_
        wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hsp_m, hx19_m, hx27_m, htr_m, hacp_m⟩ =>
        ⟨evs1, hevs1, hp, hsp_m, hx19_m, hx27_m, htr_m, hacp2.trans hacp_m⟩
    · have hl2_f : (l2 == 0#64) = false := Bool.eq_false_iff.mpr hl2
      simp only [hl2_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6500#64) s2
          (stackAt fsp allocHookStack ∗
            ((fsp + 136#64) ↦₆₄ p2_new) ∗
            ((fsp + 216#64) ↦₆₄ l2) ∗
            A.live p2_new l2.toNat 1 ∗
            memRegion p2_new l2.toNat ∗
            A.pool lim (M.stepEvents evs1 st) s2 ∗
            Rest)
          (fun sm Pm =>
            (Pm ⊢
              stackAt fsp allocHookStack ∗
              ((fsp + 136#64) ↦₆₄ p2_new) ∗
              ((fsp + 216#64) ↦₆₄ l2) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents l2.toNat 1) (M.stepEvents evs1 st)) sm ∗
              Rest) ∧
            sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x27 = 0#64 ∧
            TraceCalleeSaved sm s0 ∧ AllocCallPreserved s2 sm) := by
        wp_steps; wp_apply
        have hacp_sf : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
        wp_steps
        refine align_pre_st (by rw [hsp2]; simp only [wp_norm, arm64_norm]; (try sep_ac_rfl)) ?_
        wp_done
      refine SepWP.mono hfin fun sm _Pm _ _ ⟨hp, hsp_m, hx19_m, hx27_m, htr_m, hacp_m⟩ => ?_
      refine ⟨evs1 ++ rustDeallocEvents l2.toNat 1,
        hevs1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 l2.toNat),
        ?_, hsp_m, hx19_m, hx27_m, htr_m, hacp2.trans hacp_m⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact hp

theorem v5c_dealloc_cloned_auth_6520_to_6500_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (fsp out p1_new p2_new l1 l2 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6520#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = l1) (hx27_1 : s1.readReg64 .x27 = p1_new)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6500#64) s1
      (stackAt fsp allocHookStack ∗
        ((fsp + 136#64) ↦₆₄ p2_new) ∗
        ((fsp + 216#64) ↦₆₄ l2) ∗
        vecCapPtrDealloc A.repAlloc l1 p1_new ∗
        vecCapPtrDealloc A.repAlloc l2 p2_new ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt fsp allocHookStack ∗
            ((fsp + 136#64) ↦₆₄ p2_new) ∗
            ((fsp + 216#64) ↦₆₄ l2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = fsp ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x27 = 0#64 ∧
          TraceCalleeSaved sm s0 ∧
          AllocCallPreserved s1 sm) :=
  v5c_dealloc_cloned_auth_6520_to_6500_of_sub_placed (v1_dealloc_ok_of_placedHooks hA) st
    s0 s1 fsp out p1_new p2_new l1 l2 Rest hfsp_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx27_1 htr1

theorem v5c_dealloc_cloned_auth_6520_to_6500_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (fsp out p1_new p2_new l1 l2 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6520#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = l1) (hx27_1 : s1.readReg64 .x27 = p1_new)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6500#64) s1
      (stackAt fsp allocHookStack ∗
        ((fsp + 136#64) ↦₆₄ p2_new) ∗
        ((fsp + 216#64) ↦₆₄ l2) ∗
        vecCapPtrDealloc A.repAlloc l1 p1_new ∗
        vecCapPtrDealloc A.repAlloc l2 p2_new ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt fsp allocHookStack ∗
            ((fsp + 136#64) ↦₆₄ p2_new) ∗
            ((fsp + 216#64) ↦₆₄ l2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = fsp ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x27 = 0#64 ∧
          TraceCalleeSaved sm s0 ∧
          AllocCallPreserved s1 sm) :=
  v5c_dealloc_cloned_auth_6520_to_6500_of_placedHooks hA.toPlacedBudget st
    s0 s1 fsp out p1_new p2_new l1 l2 Rest hfsp_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx27_1 htr1

/-! ## `+6064 -> +6520` (`receivingHdr = none`), `+6064 -> +35448`, and `+6132 -> +6520` (`Err`) -/

/-- `VmPreserved`-strengthened `+6064 -> +6520` (`receivingHdr = none`) step in Block `333`. -/
theorem v5c_step_6064_none_to_6520_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out l1 p1_new : BitVec 64) (P : SepProp)
    (hl1_lt : l1.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6064#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = l1)
    (hx23 : s.readReg64 .x23 = noneCap) (hx27 : s.readReg64 .x27 = p1_new)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6520#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧ sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = l1 ∧
        sm.readReg64 .x27 = p1_new ∧ TraceCalleeSaved sm s0 ∧ VmPreserved s sm) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v5c_step_6064_none_to_6520_placed (ext := vmTrapHooks)
      s0 (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out l1 p1_new P hl1_lt (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx23) (by simpa using hx27)
      ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx21_m, hx27_m, htr_m⟩ =>
      ⟨hPm, by simpa using hsp_m, by simpa using hx19_m, by simpa using hx21_m,
       by simpa using hx27_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩, hvm⟩

theorem v5c_step_6064_none_to_6520_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out l1 p1_new : BitVec 64) (Rest : SepProp)
    (hl1_lt : l1.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6064#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = l1)
    (hx23 : s.readReg64 .x23 = noneCap) (hx27 : s.readReg64 .x27 = p1_new)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6520#64) s
      (Rest ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢ Rest ∗ A.pool lim st sm) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = l1 ∧
        sm.readReg64 .x27 = p1_new ∧ TraceCalleeSaved sm s0 ∧ VmPreserved s sm) := by
  refine SepWP.mono
    (v5c_step_6064_none_to_6520_placed (ext := ext) s0 s fsp out l1 p1_new (Rest ∗ A.pool lim st s)
      hl1_lt hpc hrun hsp hx19 hx20 hx23 hx27 htrace) ?_
  intro sm Pm _ _ ⟨hPm, hsp_m, hx19_m, hx21_m, hx27_m, htr_m, hvm⟩
  rw [← A.pool_transport lim st s sm hvm] at hPm
  exact ⟨hPm, hsp_m, hx19_m, hx21_m, hx27_m, htr_m, hvm⟩

/-- `VmPreserved`-strengthened `+6064 -> lsmpl.base 376` (`<PolyDecoder>::from_pb` call setup)
    step in Block `333`. -/
theorem v5c_step_6064_some_to_call_35448_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out l1 p1_new ptsCap ptsPtr ptsLen w40 : BitVec 64)
    (d36 : BitVec 32)
    (z0 z8 z16 : BitVec 64) (zd24 zd28 : BitVec 32) (z32 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hl1_lt : l1.toNat < 2 ^ 63) (hpts_lt : ptsCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6064#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = l1)
    (hx22 : s.readReg64 .x22 = ptsPtr) (hx23 : s.readReg64 .x23 = ptsCap)
    (hx25 : s.readReg64 .x25 = (48#32).zeroExtend 64) (hx27 : s.readReg64 .x27 = p1_new)
    (hx28 : s.readReg64 .x28 = ptsLen) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 376) s
      (((fsp + 224#64) ↦₆₄ w40) ∗
        ((fsp + 232#64) ↦₃₂ d36) ∗
        v5a_optProtoPolyDecoderWordsAt (fsp + 1392#64) z0 z8 z16 zd24 zd28 z32 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 224#64) ↦₆₄ w40) ∗
          ((fsp + 232#64) ↦₃₂ d36) ∗
          v5a_optProtoPolyDecoderWordsAt (fsp + 1392#64) ptsCap ptsPtr ptsLen 48#32 d36 w40 ∗
          Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1392#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = fsp + 1888#64 ∧
        sm.readReg64 .x21 = l1 ∧
        sm.readReg64 .x27 = p1_new ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 6132#64 ∧
        TraceCalleeSaved sm s0 ∧
        VmPreserved s sm) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v5c_step_6064_some_to_call_35448_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out l1 p1_new ptsCap ptsPtr ptsLen w40 d36 z0 z8 z16 zd24 zd28 z32 Rest
      hfsp_align hl1_lt hpts_lt (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx22) (by simpa using hx23)
      (by simpa using hx25) (by simpa using hx27) (by simpa using hx28)
      ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx27_m, hx30_m, htr_m⟩ =>
      ⟨hPm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx20_m, by simpa using hx21_m,
       by simpa using hx27_m, by simpa using hx30_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩, hvm⟩

theorem v5c_step_6064_some_to_call_35448_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out l1 p1_new ptsCap ptsPtr ptsLen w40 : BitVec 64)
    (d36 : BitVec 32)
    (z0 z8 z16 : BitVec 64) (zd24 zd28 : BitVec 32) (z32 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hl1_lt : l1.toNat < 2 ^ 63) (hpts_lt : ptsCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6064#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = l1)
    (hx22 : s.readReg64 .x22 = ptsPtr) (hx23 : s.readReg64 .x23 = ptsCap)
    (hx25 : s.readReg64 .x25 = (48#32).zeroExtend 64) (hx27 : s.readReg64 .x27 = p1_new)
    (hx28 : s.readReg64 .x28 = ptsLen) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 376) s
      (((fsp + 224#64) ↦₆₄ w40) ∗
        ((fsp + 232#64) ↦₃₂ d36) ∗
        v5a_optProtoPolyDecoderWordsAt (fsp + 1392#64) z0 z8 z16 zd24 zd28 z32 ∗
        Rest ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 224#64) ↦₆₄ w40) ∗
          ((fsp + 232#64) ↦₃₂ d36) ∗
          v5a_optProtoPolyDecoderWordsAt (fsp + 1392#64) ptsCap ptsPtr ptsLen 48#32 d36 w40 ∗
          Rest ∗ A.pool lim st sm) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1392#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = fsp + 1888#64 ∧
        sm.readReg64 .x21 = l1 ∧
        sm.readReg64 .x27 = p1_new ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 6132#64 ∧
        TraceCalleeSaved sm s0 ∧
        VmPreserved s sm) := by
  refine SepWP.mono
    (v5c_step_6064_some_to_call_35448_placed (ext := ext) s0 s fsp out l1 p1_new
      ptsCap ptsPtr ptsLen w40 d36 z0 z8 z16 zd24 zd28 z32 (Rest ∗ A.pool lim st s)
      hfsp_align hl1_lt hpts_lt hpc hrun hsp hx19 hx20 hx22 hx23 hx25 hx27 hx28 htrace) ?_
  intro sm Pm _ _ ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx27_m, hx30_m, htr_m, hvm⟩
  rw [← A.pool_transport lim st s sm hvm] at hPm
  exact ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx27_m, hx30_m, htr_m, hvm⟩

/-- `VmPreserved`-strengthened `+6132 -> +6520` (`<PolyDecoder>::from_pb` returned `Err`) step
    in Block `333`. -/
theorem v5c_step_6132_err_to_6520_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out l1 p1_new : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 6132#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = l1)
    (hx27 : s.readReg64 .x27 = p1_new) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6520#64) s
      (((fsp + 1888#64) ↦₆₄ noneCap) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1888#64) ↦₆₄ noneCap) ∗ Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = l1 ∧
        sm.readReg64 .x27 = p1_new ∧ TraceCalleeSaved sm s0 ∧ VmPreserved s sm) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v5c_step_6132_err_to_6520_placed (ext := vmTrapHooks)
      s0 (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out l1 p1_new Rest hfsp_align (by simpa using hpc) (by simpa using hrun)
      (by simpa using hsp) (by simpa using hx19) (by simpa using hx21) (by simpa using hx27)
      ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx21_m, hx27_m, htr_m⟩ =>
      ⟨hPm, by simpa using hsp_m, by simpa using hx19_m, by simpa using hx21_m,
       by simpa using hx27_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩, hvm⟩

theorem v5c_step_6132_err_to_6520_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out l1 p1_new : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 6132#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = l1)
    (hx27 : s.readReg64 .x27 = p1_new) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6520#64) s
      (((fsp + 1888#64) ↦₆₄ noneCap) ∗ Rest ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1888#64) ↦₆₄ noneCap) ∗ Rest ∗ A.pool lim st sm) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = l1 ∧
        sm.readReg64 .x27 = p1_new ∧ TraceCalleeSaved sm s0 ∧ VmPreserved s sm) := by
  refine SepWP.mono
    (v5c_step_6132_err_to_6520_placed (ext := ext) s0 s fsp out l1 p1_new (Rest ∗ A.pool lim st s)
      hfsp_align hpc hrun hsp hx19 hx21 hx27 htrace) ?_
  intro sm Pm _ _ ⟨hPm, hsp_m, hx19_m, hx21_m, hx27_m, htr_m, hvm⟩
  rw [← A.pool_transport lim st s sm hvm] at hPm
  exact ⟨hPm, hsp_m, hx19_m, hx21_m, hx27_m, htr_m, hvm⟩

/-! ## `+6132 -> +8180` (`Ok dec`) & `+6132 -> ret` -/

/-- `VmPreserved`-strengthened `+6132 -> +8180` (`Ok dec`, 72 instructions) step in Block `333`. -/
theorem v5c_step_6132_ok_to_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out p1_new p2_new l1 l2 ep w2272 w2280 : BitVec 64)
    (bs : List (BitVec 8))
    (u160 : BitVec 64) (d172 : BitVec 32) (u208 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u888 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_lt : (v9_wordAt bs 0).toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6132#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = fsp + 1888#64) (hx21 : s.readReg64 .x21 = l1)
    (hx27 : s.readReg64 .x27 = p1_new) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 8180#64) s
      (((fsp + 136#64) ↦₆₄ p2_new) ∗
        ((fsp + 152#64) ↦₆₄ ep) ∗
        ((fsp + 216#64) ↦₆₄ l2) ∗
        v5c_stagingSlotsPre fsp u160 d172 u208 u232
          uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
          u832 uq848 u864 u880 u888 ∗
        v5c_decCellsAt (fsp + 1888#64) bs ∗
        ((fsp + 2272#64) ↦₆₄ w2272) ∗
        ((fsp + 2280#64) ↦₆₄ w2280) ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((fsp + 136#64) ↦₆₄ p2_new) ∗
          ((fsp + 152#64) ↦₆₄ ep) ∗
          ((fsp + 216#64) ↦₆₄ l2) ∗
          v5c_stagingSlotsPost fsp bs p1_new w2272 ∗
          v5c_decCellsAt (fsp + 1888#64) bs ∗
          ((fsp + 2272#64) ↦₆₄ w2272) ∗
          ((fsp + 2280#64) ↦₆₄ w2280) ∗
          Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x8 = 7#64 ∧
        s2.readReg64 .x15 = l1 ∧
        s2.readReg64 .x20 = l1 ∧
        s2.readReg64 .x13 = l2 ∧
        s2.readReg64 .x25 = p2_new ∧
        s2.readReg64 .x30 = l2 ∧
        s2.readReg64 .x9 = ep ∧
        s2.readReg64 .x14 = v9_wordAt bs 0 ∧
        s2.readReg64 .x18 = v9_wordAt bs 8 ∧
        s2.readReg64 .x17 = v9_wordAt bs 16 ∧
        s2.readReg64 .x0 = v9_wordAt bs 24 ∧
        (s2.readReg32 .x3).setWidth 8 = (v9_wordAt bs 32).extractLsb' 0 8 ∧
        s2.readReg32 .x27 = (v9_wordAt bs 32).extractLsb' 8 32 ∧
        ((s2.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v9_wordAt bs 32).extractLsb' 40 16 ∧
        ((s2.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v9_wordAt bs 32).extractLsb' 56 8 ∧
        s2.readReg64 .x4 = v9_wordAt bs 40 ∧
        s2.readReg64 .x5 = v9_wordAt bs 48 ∧
        (s2.readReg32 .x21).setWidth 8 = loByte (v9_wordAt bs 56) ∧
        s2.readReg64 .x7 = v9_wordAt bs 72 ∧
        s2.readReg64 .x2 = v9_wordAt bs 336 ∧
        s2.readReg64 .x11 = v9_wordAt bs 344 ∧
        s2.readReg64 .x22 = v9_wordAt bs 352 ∧
        s2.readReg64 .x24 = v9_wordAt bs 360 ∧
        s2.readReg64 .x10 = v9_wordAt bs 376 ∧
        s2.readReg64 .x26 = w2280 ∧
        s2.readReg64 .x6 = fsp + 576#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x23 = fsp + 848#64 ∧
        TraceCalleeSaved s2 s0 ∧
        VmPreserved s s2) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v5c_step_6132_ok_to_8180_placed (ext := vmTrapHooks)
      s0 (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out p1_new p2_new l1 l2 ep w2272 w2280 bs
      u160 d172 u208 u232
      uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
      u832 uq848 u864 u880 u888 Rest
      hfsp_align hw0_lt (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx21) (by simpa using hx27)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s2 P2 hvm ⟨hP2, hsp2, hx8, hx15, hx20_2, hx13, hx25, hx30, hx9, hx14, hx18, hx17, hx0,
        hx3, hx27_lo, hx27_mid, hx27_hi, hx4, hx5, hx21_2, hx7, hx2, hx11, hx22, hx24, hx10,
        hx26, hx6, hx19_2, hx23, htr2⟩ =>
      ⟨hP2, by simpa using hsp2, by simpa using hx8, by simpa using hx15,
       by simpa using hx20_2, by simpa using hx13, by simpa using hx25, by simpa using hx30,
       by simpa using hx9, by simpa using hx14, by simpa using hx18, by simpa using hx17,
       by simpa using hx0, by simpa using hx3, by simpa using hx27_lo, by simpa using hx27_mid,
       by simpa using hx27_hi, by simpa using hx4, by simpa using hx5, by simpa using hx21_2,
       by simpa using hx7, by simpa using hx2, by simpa using hx11, by simpa using hx22,
       by simpa using hx24, by simpa using hx10, by simpa using hx26, by simpa using hx6,
       by simpa using hx19_2, by simpa using hx23,
       ⟨by simpa using htr2.1, by simpa using htr2.2⟩, hvm⟩

theorem v5c_step_6132_ok_to_8180_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out p1_new p2_new l1 l2 ep w2272 w2280 : BitVec 64)
    (bs : List (BitVec 8))
    (u160 : BitVec 64) (d172 : BitVec 32) (u208 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u888 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_lt : (v9_wordAt bs 0).toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6132#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = fsp + 1888#64) (hx21 : s.readReg64 .x21 = l1)
    (hx27 : s.readReg64 .x27 = p1_new) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 8180#64) s
      (((fsp + 136#64) ↦₆₄ p2_new) ∗
        ((fsp + 152#64) ↦₆₄ ep) ∗
        ((fsp + 216#64) ↦₆₄ l2) ∗
        v5c_stagingSlotsPre fsp u160 d172 u208 u232
          uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
          u832 uq848 u864 u880 u888 ∗
        v5c_decCellsAt (fsp + 1888#64) bs ∗
        ((fsp + 2272#64) ↦₆₄ w2272) ∗
        ((fsp + 2280#64) ↦₆₄ w2280) ∗
        Rest ∗ A.pool lim st s)
      (fun s2 P2 =>
        (P2 ⊢
          ((fsp + 136#64) ↦₆₄ p2_new) ∗
          ((fsp + 152#64) ↦₆₄ ep) ∗
          ((fsp + 216#64) ↦₆₄ l2) ∗
          v5c_stagingSlotsPost fsp bs p1_new w2272 ∗
          v5c_decCellsAt (fsp + 1888#64) bs ∗
          ((fsp + 2272#64) ↦₆₄ w2272) ∗
          ((fsp + 2280#64) ↦₆₄ w2280) ∗
          Rest ∗ A.pool lim st s2) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x8 = 7#64 ∧
        s2.readReg64 .x15 = l1 ∧
        s2.readReg64 .x20 = l1 ∧
        s2.readReg64 .x13 = l2 ∧
        s2.readReg64 .x25 = p2_new ∧
        s2.readReg64 .x30 = l2 ∧
        s2.readReg64 .x9 = ep ∧
        s2.readReg64 .x14 = v9_wordAt bs 0 ∧
        s2.readReg64 .x18 = v9_wordAt bs 8 ∧
        s2.readReg64 .x17 = v9_wordAt bs 16 ∧
        s2.readReg64 .x0 = v9_wordAt bs 24 ∧
        (s2.readReg32 .x3).setWidth 8 = (v9_wordAt bs 32).extractLsb' 0 8 ∧
        s2.readReg32 .x27 = (v9_wordAt bs 32).extractLsb' 8 32 ∧
        ((s2.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v9_wordAt bs 32).extractLsb' 40 16 ∧
        ((s2.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v9_wordAt bs 32).extractLsb' 56 8 ∧
        s2.readReg64 .x4 = v9_wordAt bs 40 ∧
        s2.readReg64 .x5 = v9_wordAt bs 48 ∧
        (s2.readReg32 .x21).setWidth 8 = loByte (v9_wordAt bs 56) ∧
        s2.readReg64 .x7 = v9_wordAt bs 72 ∧
        s2.readReg64 .x2 = v9_wordAt bs 336 ∧
        s2.readReg64 .x11 = v9_wordAt bs 344 ∧
        s2.readReg64 .x22 = v9_wordAt bs 352 ∧
        s2.readReg64 .x24 = v9_wordAt bs 360 ∧
        s2.readReg64 .x10 = v9_wordAt bs 376 ∧
        s2.readReg64 .x26 = w2280 ∧
        s2.readReg64 .x6 = fsp + 576#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x23 = fsp + 848#64 ∧
        TraceCalleeSaved s2 s0 ∧
        VmPreserved s s2) := by
  refine SepWP.mono
    (v5c_step_6132_ok_to_8180_placed (ext := ext) s0 s fsp out p1_new p2_new l1 l2 ep w2272 w2280 bs
      u160 d172 u208 u232
      uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
      u832 uq848 u864 u880 u888 (Rest ∗ A.pool lim st s)
      hfsp_align hw0_lt hpc hrun hsp hx19 hx20 hx21 hx27 htr) ?_
  intro s2 P2 _ _ ⟨hP2, hregs⟩
  have hvm : VmPreserved s s2 := hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [← A.pool_transport lim st s s2 hvm] at hP2
  exact ⟨hP2, hregs⟩

/-- Budget-threaded Variant 5 (`NoHeaderReceived`) `+6132 -> +8180 -> s0.x30` composition
    (parameterized by `hmemcpy_ok : subroutine_ok ... allocMemcpyVmSpec`), preserving `VmPreserved`
    and `A.pool lim st`. -/
theorem v5c_noHeaderReceived_6132_ok_to_ret_of_memcpy_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec)
    (st : M.σ)
    (s0 s : State) (fsp out ep pa1 l1 pa2 l2 w224 w232 w392 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hw0_lt : (v9_wordAt bs 0).toNat < 2 ^ 63)
    (dec : PolyDecoder) (P_heap : SepProp)
    (hreloc :
      ((out + 64#64) ↦ₛ bs) ∗
        (((out + 64#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        (((out + 64#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢
        polyDecoderAt A.repAlloc (out + 64#64) dec)
    (rootKey macKey : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length)
    (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 6132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = fsp + 1888#64)
    (hx21 : s.readReg64 .x21 = l1)
    (hx27 : s.readReg64 .x27 = pa1)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      ((memRegion fsp 136 ∗
        memRegion (fsp + 144#64) 8 ∗
        memRegion (fsp + 160#64) 48 ∗
        memRegion (fsp + 240#64) 1648) ∗
       stackAt fsp encoderFromPbStack ∗
       memRegion out chunkedStatesSize ∗
       ((fsp + 136#64) ↦₆₄ pa2) ∗
       ((fsp + 152#64) ↦₆₄ ep) ∗
       ((fsp + 208#64) ↦₆₄ pa1) ∗
       ((fsp + 216#64) ↦₆₄ l2) ∗
       ((fsp + 224#64) ↦₆₄ w224) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗
       v5c_decCellsAt (fsp + 1888#64) bs ∗
       ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
       ((fsp + 2280#64) ↦₆₄ w392) ∗
       memRegion (fsp + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗
       P_heap ∗
       vecU8Payload A.repAlloc l1 pa1 rootKey ∗
       vecU8Payload A.repAlloc l2 pa2 macKey ∗
       A.pool lim st s ∗
       Frame)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (.ok (.noHeaderReceived
              { uc := { auth := { rootKey := rootKey, macKey := macKey }, epoch := ep },
                receiving_hdr := dec })) ∗
          stackAt s0.sp statesFromPbStack ∗ A.pool lim st sf ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧ VmPreserved s sf) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    hfsp ▸ ProofLib.spAligned_sub s0.sp 2400#64 halign (by decide)
  refine SepWP.weaken_pre (sepConj_mono_left
    (sepConj_mono (v5c_memRegion_136_split fsp)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (v5c_memRegion_160_48_split fsp)
          (v5c_memRegion_240_1648_split fsp))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun u888 => ProofLib.SepWP.exists_left fun u880 =>
    ProofLib.SepWP.exists_left fun u864 => ProofLib.SepWP.exists_left fun uq848 =>
    ProofLib.SepWP.exists_left fun u832 => ProofLib.SepWP.exists_left fun uq816 =>
    ProofLib.SepWP.exists_left fun uq800 => ProofLib.SepWP.exists_left fun uq784 =>
    ProofLib.SepWP.exists_left fun uq768 => ProofLib.SepWP.exists_left fun uq752 =>
    ProofLib.SepWP.exists_left fun uq736 => ProofLib.SepWP.exists_left fun uq720 =>
    ProofLib.SepWP.exists_left fun uq704 => ProofLib.SepWP.exists_left fun uq688 =>
    ProofLib.SepWP.exists_left fun uq672 => ProofLib.SepWP.exists_left fun uq656 =>
    ProofLib.SepWP.exists_left fun uq640 => ProofLib.SepWP.exists_left fun uq624 =>
    ProofLib.SepWP.exists_left fun uq608 => ProofLib.SepWP.exists_left fun w592 =>
    ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun bs240 =>
    ProofLib.SepWP.exists_left fun w192 => ProofLib.SepWP.exists_left fun d172 =>
    ProofLib.SepWP.exists_left fun u160 => ProofLib.SepWP.exists_left fun w120 =>
    ProofLib.SepWP.exists_left fun w112 => ProofLib.SepWP.exists_left fun w104 =>
    ProofLib.SepWP.exists_left fun d92 => ?_
  have hstep := v5c_step_6132_ok_to_8180_placed (ext := ext) s0 s fsp out pa1 pa2 l1 l2 ep
    (BitVec.ofNat 64 dec.ptsNeeded) w392 bs
    u160 d172 pa1 w232
    uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
    u832 uq848 u864 u880 u888
    (stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
     memRegion fsp 92 ∗ ((fsp + 92#64) ↦₃₂ d92) ∗ memRegion (fsp + 96#64) 8 ∗
     ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
     memRegion (fsp + 128#64) 8 ∗ memRegion (fsp + 144#64) 8 ∗
     memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗
     ((fsp + 192#64) ↦₆₄ w192) ∗ memRegion (fsp + 200#64) 8 ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
     ((fsp + 240#64) ↦ₛ bs240.val) ∗ memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗
     ((fsp + 592#64) ↦ₛ loBytes7 w592) ∗ memRegion (fsp + 599#64) 9 ∗
     memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 993 ∗
     memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
     P_heap ∗ vecU8Payload A.repAlloc l1 pa1 rootKey ∗ vecU8Payload A.repAlloc l2 pa2 macKey ∗
     A.pool lim st s ∗ Frame)
    hfsp_align hw0_lt hpc hrun hsp hx19 hx20 hx21 hx27 htr
  refine SepWP.weaken_pre ?_ (SepWP.seq hstep ?_)
  · unfold v5c_stagingSlotsPre
    exact Entails.of_eq (by sep_ac_rfl)
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2,
    hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2,
    hx4_2, hx5_2, hx21_2, hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2,
    hx6_2, hx19_2, hx23_2, htr2, hvm1⟩
  subst hfsp
  have hpool_s2 : A.pool lim st s = A.pool lim st s2 :=
    (A.pool_transport lim st s s2 hvm1).symm
  have h128 := v5c_fsp_128_entails_32 (s0.sp - 2400#64) pa2 ep
  have h216 := ProofLib.pointsTo64_entails_memRegion ((s0.sp - 2400#64) + 216#64) l2
  have h1888 := v5c_fsp_1888_entails_epilogue (s0.sp - 2400#64)
    (BitVec.ofNat 64 dec.ptsNeeded) w392 bs hbs
  have hep := Variant1bPlacedBudgetAux.states_from_pb_epilogue_8180_placed A lim st hmemcpy_ok s0 s2 out
    d92 ((loByte (v9_wordAt bs 80)).zeroExtend 32)
    w104 w112 w120 (BitVec.ofNat 64 dec.ptsNeeded) w192 pa1 w224 (v9_wordAt bs 368)
    bs240.val bs240.property
    q576 w592
    (v9_quadAt bs 104) (v9_quadAt bs 120) (v9_quadAt bs 136) (v9_quadAt bs 152)
    (v9_quadAt bs 168) (v9_quadAt bs 184) (v9_quadAt bs 200) (v9_quadAt bs 216)
    (v9_quadAt bs 232) (v9_quadAt bs 248) (v9_quadAt bs 264) (v9_quadAt bs 280)
    (v9_quadAt bs 296) (v9_quadAt bs 312)
    (v9_wordAt bs 328)
    (v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96))
    (v9_wordAt bs 96 >>> 8)
    (unshiftWord (v9_wordAt bs 56) (loByte (v9_wordAt bs 64)))
    (v9_wordAt bs 64 >>> 8)
    (v9_wordAt bs 8 ++ v9_wordAt bs 0) (v9_wordAt bs 24 ++ v9_wordAt bs 16) (v9_wordAt bs 32)
    (P_heap ∗ vecU8Payload A.repAlloc l1 pa1 rootKey ∗ vecU8Payload A.repAlloc l2 pa2 macKey ∗ Frame)
    halign hpc2 hrun2 hsp2 hx6_2 hx19_2 hx23_2 htr2
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2,
      hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2, hx4_2, hx5_2, hx21_2, hx7_2,
      hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2] at hep
  refine SepWP.weaken_pre ?_ (SepWP.mono hep ?_)
  · refine Entails.trans hP2 ?_
    rw [hpool_s2]
    unfold v5c_stagingSlotsPost epilogueStackSlots epilogueStackGaps
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 2400#64) + 128#64) 8 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ pa2) ∗
       memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep)) ∗
      (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
      (v5c_decCellsAt ((s0.sp - 2400#64) + 1888#64) bs ∗
       (((s0.sp - 2400#64) + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
       (((s0.sp - 2400#64) + 2280#64) ↦₆₄ w392) ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion (s0.sp - 2400#64) 92 ∗ (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗
       memRegion ((s0.sp - 2400#64) + 96#64) 8 ∗
       (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112) ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120) ∗
       (((s0.sp - 2400#64) + 160#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
       memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗
       (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte (v9_wordAt bs 80)).zeroExtend 32) ∗
       memRegion ((s0.sp - 2400#64) + 176#64) 16 ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ w192) ∗
       memRegion ((s0.sp - 2400#64) + 200#64) 8 ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ pa1) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ v9_wordAt bs 368) ∗
       (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240.val) ∗
       memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗ (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
       (((s0.sp - 2400#64) + 592#64) ↦ₛ loBytes7 w592) ∗
       memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗
       (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ v9_quadAt bs 104) ∗
       (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ v9_quadAt bs 120) ∗
       (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ v9_quadAt bs 136) ∗
       (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ v9_quadAt bs 152) ∗
       (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ v9_quadAt bs 168) ∗
       (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ v9_quadAt bs 184) ∗
       (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ v9_quadAt bs 200) ∗
       (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ v9_quadAt bs 216) ∗
       (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ v9_quadAt bs 232) ∗
       (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ v9_quadAt bs 248) ∗
       (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ v9_quadAt bs 264) ∗
       (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ v9_quadAt bs 280) ∗
       (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ v9_quadAt bs 296) ∗
       (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ v9_quadAt bs 312) ∗
       (((s0.sp - 2400#64) + 832#64) ↦₆₄ v9_wordAt bs 328) ∗
       memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       (((s0.sp - 2400#64) + 848#64) ↦₁₂₈
         v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96)) ∗
       (((s0.sp - 2400#64) + 864#64) ↦ₛ loBytes7 (v9_wordAt bs 96 >>> 8)) ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗
       (((s0.sp - 2400#64) + 880#64) ↦₆₄
         unshiftWord (v9_wordAt bs 56) (loByte (v9_wordAt bs 64))) ∗
       (((s0.sp - 2400#64) + 888#64) ↦ₛ loBytes7 (v9_wordAt bs 64 >>> 8)) ∗
       memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗
       statesFromPbSavedCells s0 ∗ P_heap ∗
       vecU8Payload A.repAlloc l1 pa1 rootKey ∗ vecU8Payload A.repAlloc l2 pa2 macKey ∗
       A.pool lim st s2 ∗ Frame) by sep_ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono h128 (sepConj_mono h216 (sepConj_mono_left h1888))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f, hvm2⟩
    refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f, hvm1.trans hvm2⟩
    have hout := v5c_epilogueOutFull_entails_noHeaderReceived A.repAlloc (F := F)
      out l1 pa1 l2 pa2 ep bs hbs w392 dec P_heap hreloc rootKey macKey hl1 hl2
      (s2.readReg64 .x12) (s2.readReg64 .x1) w224 (s2.readReg64 .x28) w192 (s2.readReg64 .x16)
      w104 w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
      bs240.val bs240.property
      (v9_wordAt bs 8 ++ v9_wordAt bs 0) (v9_wordAt bs 24 ++ v9_wordAt bs 16) (v9_wordAt bs 32)
    refine Entails.trans (Entails.of_eq (show _ =
      (epilogueOutFull out
        7#64 l1 pa1 l1 l2 pa2 l2 ep
        (v9_wordAt bs 0) (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)
        ((v9_wordAt bs 32).extractLsb' 0 8) ((v9_wordAt bs 32).extractLsb' 8 32)
        ((v9_wordAt bs 32).extractLsb' 40 16) ((v9_wordAt bs 32).extractLsb' 56 8)
        (v9_wordAt bs 40) (v9_wordAt bs 48)
        (loByte (v9_wordAt bs 56))
        (unshiftWord (v9_wordAt bs 56) (loByte (v9_wordAt bs 64)))
        (overlapWord7
          (unshiftWord (v9_wordAt bs 56) (loByte (v9_wordAt bs 64)))
          (v9_wordAt bs 64 >>> 8))
        (v9_wordAt bs 72)
        (((loByte (v9_wordAt bs 80)).zeroExtend 32).setWidth 8)
        (v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96))
        (overlapWord7
          ((v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96)).extractLsb' 64 64)
          (v9_wordAt bs 96 >>> 8))
        (v9_quadAt bs 104) (v9_quadAt bs 120) (v9_quadAt bs 136) (v9_quadAt bs 152)
        (v9_quadAt bs 168) (v9_quadAt bs 184) (v9_quadAt bs 200) (v9_quadAt bs 216)
        (v9_quadAt bs 232) (v9_quadAt bs 248) (v9_quadAt bs 264) (v9_quadAt bs 280)
        (v9_quadAt bs 296) (v9_quadAt bs 312)
        (v9_wordAt bs 328) (v9_wordAt bs 336) (v9_wordAt bs 344) (v9_wordAt bs 352)
        (v9_wordAt bs 360) (v9_wordAt bs 368) (v9_wordAt bs 376)
        (BitVec.ofNat 64 dec.ptsNeeded) w392
        (s2.readReg64 .x12) (s2.readReg64 .x1) w224 (s2.readReg64 .x28) w192 (s2.readReg64 .x16)
        w104 w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
        bs240.val (v9_wordAt bs 8 ++ v9_wordAt bs 0) (v9_wordAt bs 24 ++ v9_wordAt bs 16) (v9_wordAt bs 32) ∗
       P_heap ∗ vecU8Payload A.repAlloc l1 pa1 rootKey ∗ vecU8Payload A.repAlloc l2 pa2 macKey) ∗
      stackAt s0.sp statesFromPbStack ∗ A.pool lim st sf ∗ Frame by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hout) (Entails.of_eq (by sep_ac_rfl))

theorem v5c_noHeaderReceived_6132_ok_to_ret_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ)
    (s0 s : State) (fsp out ep pa1 l1 pa2 l2 w224 w232 w392 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hw0_lt : (v9_wordAt bs 0).toNat < 2 ^ 63)
    (dec : PolyDecoder) (P_heap : SepProp)
    (hreloc :
      ((out + 64#64) ↦ₛ bs) ∗
        (((out + 64#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        (((out + 64#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢
        polyDecoderAt A.repAlloc (out + 64#64) dec)
    (rootKey macKey : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length)
    (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 6132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = fsp + 1888#64)
    (hx21 : s.readReg64 .x21 = l1)
    (hx27 : s.readReg64 .x27 = pa1)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      ((memRegion fsp 136 ∗
        memRegion (fsp + 144#64) 8 ∗
        memRegion (fsp + 160#64) 48 ∗
        memRegion (fsp + 240#64) 1648) ∗
       stackAt fsp encoderFromPbStack ∗
       memRegion out chunkedStatesSize ∗
       ((fsp + 136#64) ↦₆₄ pa2) ∗
       ((fsp + 152#64) ↦₆₄ ep) ∗
       ((fsp + 208#64) ↦₆₄ pa1) ∗
       ((fsp + 216#64) ↦₆₄ l2) ∗
       ((fsp + 224#64) ↦₆₄ w224) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗
       v5c_decCellsAt (fsp + 1888#64) bs ∗
       ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
       ((fsp + 2280#64) ↦₆₄ w392) ∗
       memRegion (fsp + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗
       P_heap ∗
       vecU8Payload A.repAlloc l1 pa1 rootKey ∗
       vecU8Payload A.repAlloc l2 pa2 macKey ∗
       A.pool lim st s ∗
       Frame)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (.ok (.noHeaderReceived
              { uc := { auth := { rootKey := rootKey, macKey := macKey }, epoch := ep },
                receiving_hdr := dec })) ∗
          stackAt s0.sp statesFromPbStack ∗ A.pool lim st sf ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧ VmPreserved s sf) :=
  v5c_noHeaderReceived_6132_ok_to_ret_of_memcpy_placed hA.memcpy_ok st
    s0 s fsp out ep pa1 l1 pa2 l2 w224 w232 w392 bs hbs hw0_lt dec P_heap hreloc
    rootKey macKey hl1 hl2 Frame halign hfsp hpc hrun hsp hx19 hx20 hx21 hx27 htr

theorem v5c_noHeaderReceived_6132_ok_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ)
    (s0 s : State) (fsp out ep pa1 l1 pa2 l2 w224 w232 w392 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hw0_lt : (v9_wordAt bs 0).toNat < 2 ^ 63)
    (dec : PolyDecoder) (P_heap : SepProp)
    (hreloc :
      ((out + 64#64) ↦ₛ bs) ∗
        (((out + 64#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        (((out + 64#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢
        polyDecoderAt A.repAlloc (out + 64#64) dec)
    (rootKey macKey : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length)
    (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 6132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = fsp + 1888#64)
    (hx21 : s.readReg64 .x21 = l1)
    (hx27 : s.readReg64 .x27 = pa1)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      ((memRegion fsp 136 ∗
        memRegion (fsp + 144#64) 8 ∗
        memRegion (fsp + 160#64) 48 ∗
        memRegion (fsp + 240#64) 1648) ∗
       stackAt fsp encoderFromPbStack ∗
       memRegion out chunkedStatesSize ∗
       ((fsp + 136#64) ↦₆₄ pa2) ∗
       ((fsp + 152#64) ↦₆₄ ep) ∗
       ((fsp + 208#64) ↦₆₄ pa1) ∗
       ((fsp + 216#64) ↦₆₄ l2) ∗
       ((fsp + 224#64) ↦₆₄ w224) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗
       v5c_decCellsAt (fsp + 1888#64) bs ∗
       ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
       ((fsp + 2280#64) ↦₆₄ w392) ∗
       memRegion (fsp + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗
       P_heap ∗
       vecU8Payload A.repAlloc l1 pa1 rootKey ∗
       vecU8Payload A.repAlloc l2 pa2 macKey ∗
       A.pool lim st s ∗
       Frame)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (.ok (.noHeaderReceived
              { uc := { auth := { rootKey := rootKey, macKey := macKey }, epoch := ep },
                receiving_hdr := dec })) ∗
          stackAt s0.sp statesFromPbStack ∗ A.pool lim st sf ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧ VmPreserved s sf) :=
  v5c_noHeaderReceived_6132_ok_to_ret_of_placedHooks hA.toPlacedBudget st
    s0 s fsp out ep pa1 l1 pa2 l2 w224 w232 w392 bs hbs hw0_lt dec P_heap hreloc
    rootKey macKey hl1 hl2 Frame halign hfsp hpc hrun hsp hx19 hx20 hx21 hx27 htr

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5cPlacedBudget
