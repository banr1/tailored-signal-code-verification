/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded `[LibsignalPlacement]` Error Exits for `spqr::decode_state` (Block `325`)

Proves the budget-threaded code-loaded shared epilogue (`+2500..+2528`), `DecodeError`
drop/unwind tail (`+2392..+2528`), and top-level `DecodeError::push` error-exit blocks.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitClPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (box72_entails_memRegion kindNoHeap_branch_false shl5_toNat)
open CryptoVerification.LibsignalSpqrV1 (PqRatchetState spqrDecodeState)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost DropProtoPqRatchetStateGhost TraceVRegs V1InnerHeapPred
   decodeErrorWith_unfold decodeStatePlacedEntry decodeStatePlacedProg decodeStateResultAt
   decodeStateSavedAt decodeState_stack_restore_1296 dropOptProtoInnerStateStack
   fold_decodeStateResultAt_err frame_4chunks_to_1296 memRegion_352_err_split
   protoPqRatchetStateAt protoPqRatchetState_of_memcpy protoPqRatchetState_to_memcpy
   scratch_688_fold_48 sp_sub_1392_aligned stackAt_of_callee stackAt_to_callee)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv DecodeErrorPushEnv decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec
   withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (deallocFreeOnlySpec freeOnlyEvs_rustDeallocEvents subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv sepWP_done_postEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced SepWPpIPlaced.of_sepWP)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (dropProtoPqRatchetStatePlacedSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Lift a `LibsignalCodeLoaded`-indexed return `SepWP` into `SepWPpIPlaced`. -/
theorem SepWPpIPlaced.of_sepWP_ret_lscl [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : LibsignalCodeLoaded lsmpl s.mem → SepWP prog ret s P Q) :
    SepWPpIPlaced prog ret s P Q Q_err :=
  fun hinv => SepWPp.of_sepWP_ret (h hinv.1)

/-! ## 1. Error Drop (`0x53e0c..0x53e7c`) & Error Tail (`0x53df4..0x53e7c`) -/

set_option maxHeartbeats 800000 in
/-- Envelope-parameterized inlined `drop_glue::<DecodeError>` + `Err(Error::StateDecode)` write +
epilogue (`0x53e0c..0x53e7c`, `+2416..+2528`, 29 instructions), using
`DecodeStateCalleeContractsClPlaced`. -/
theorem decodeState_err_drop_53e0c_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (n : Nat) (s0 s : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (henv : ∀ evs_f, FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_f st)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc (s.readReg64 .x20) n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 1296 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hdealloc := subroutine_ok_deallocFreeOnly hc.dealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP hpost
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hdealloc ⊢
  refine SepWP.weaken_pre (sepConj_mono_left (decodeErrorWith_unfold A.repAlloc (s.readReg64 .x20) n)) ?_
  simp only [RustCliAllocBudget.repAlloc_live, sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro ptr
  apply ProofLib.SepWP.exists_left; intro w
  wp_focus_pure; rintro ⟨hn_cap, hcap_lt, hptr, hw⟩
  have hbr := kindNoHeap_branch_false hw
  refine SepWP.fold (memRegion_352_err_split x.outPtr) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
  unfold decodeStateSavedAt
  by_cases hcap0 : cap = 0
  · have hcap_beq : (cap == 0#64) = true := beq_iff_eq.mpr hcap0
    have hite :
        (if cap = 0 then emp else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) =
          emp := by
      simp [hcap0]
    rw [hite, emp_sepConj]
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    simp only [State.setMem_setMem]
    refine SepWP.fold (box72_entails_memRegion (s.readReg64 .x20) cap ptr (BitVec.ofNat 64 n) w)
      (by sep_focus) ?_
    wp_call hdealloc (s.readReg64 .x20, 72, 8, st)
    have htr_sf : sf.trace = s0.trace := by
      have h1 : sf.trace = _ := ‹Heap.AllocCallPreserved _ sf›.2.1
      simpa only [wp_norm, arm64_norm, htr] using h1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      simp only [wp_norm, arm64_norm, *]
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
      (by sep_focus) ?_
    wp_steps_sync_pool (s0.readReg64 .x30)
    simp only [State.setMem_setMem]
    refine SepWP.fold (fold_decodeStateResultAt_err H_inner A.repAlloc x.outPtr herr)
      (by sep_focus) ?_
    refine SepWP.fold (decodeState_stack_restore_1296 s0.sp
      (s0.readReg64 .x29) (s0.readReg64 .x30)
      (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
      (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
      unfold decodeStateSavedAt
      sep_focus) ?_
    exact sepWP_done_postEnv
      (by simp only [wp_norm, arm64_norm, Reg.x30])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm])
      (by unfold CalleeSavedPreserved; simp only [wp_norm, arm64_norm, hvregs_sf, and_self])
      (by simp only [wp_norm, arm64_norm, htr_sf])
      (henv (rustDeallocEvents 72 8) (freeOnlyEvs_rustDeallocEvents 72 8))
      (by sep_focus)
      (by sep_ac_rfl)
  · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hshl : (cap <<< 5).toNat = cap.toNat * 32 := shl5_toNat hcap_lt
    have hite :
        (if cap = 0 then emp else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) =
          (A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) :=
      ite_eq_right_iff.mpr fun h => absurd h hcap0
    rw [hite]
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    simp only [State.setMem_setMem]
    wp_call hdealloc (ptr, cap.toNat * 32, 8, st)
    have htr_sf : sf.trace = s0.trace := by
      have h1 : sf.trace = _ := ‹Heap.AllocCallPreserved _ sf›.2.1
      simpa only [wp_norm, arm64_norm, htr] using h1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      simp only [wp_norm, arm64_norm, *]
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    simp only [State.setMem_setMem]
    refine SepWP.fold (box72_entails_memRegion (s.readReg64 .x20) cap ptr (BitVec.ofNat 64 n) w)
      (by sep_focus) ?_
    wp_call hdealloc (s.readReg64 .x20, 72, 8,
      M.stepEvents (rustDeallocEvents (cap.toNat * 32) 8) st)
    have htr_sf1 : sf_1.trace = s0.trace := by
      have h2 : sf_1.trace = _ := ‹Heap.AllocCallPreserved _ sf_1›.2.1
      simpa only [wp_norm, arm64_norm, htr_sf] using h2
    have hvregs_sf1 : calleeSavedVRegs sf_1 = calleeSavedVRegs s0 := by
      simp only [wp_norm, arm64_norm, *]
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
      (by sep_focus) ?_
    wp_steps_sync_pool (s0.readReg64 .x30)
    simp only [State.setMem_setMem]
    refine SepWP.fold (fold_decodeStateResultAt_err H_inner A.repAlloc x.outPtr herr)
      (by sep_focus) ?_
    refine SepWP.fold (decodeState_stack_restore_1296 s0.sp
      (s0.readReg64 .x29) (s0.readReg64 .x30)
      (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
      (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
      unfold decodeStateSavedAt
      sep_focus) ?_
    have henv2 : ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents (rustDeallocEvents 72 8)
            (M.stepEvents (rustDeallocEvents (cap.toNat * 32) 8) st) := by
      rw [← M.stepEvents_append]
      exact henv (rustDeallocEvents (cap.toNat * 32) 8 ++ rustDeallocEvents 72 8)
        ((freeOnlyEvs_rustDeallocEvents (cap.toNat * 32) 8).append
          (freeOnlyEvs_rustDeallocEvents 72 8))
    exact sepWP_done_postEnv
      (by simp only [wp_norm, arm64_norm, Reg.x30])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm])
      (by unfold CalleeSavedPreserved; simp only [wp_norm, arm64_norm, hvregs_sf1, and_self])
      (by simp only [wp_norm, arm64_norm, htr_sf1])
      henv2
      (by sep_focus)
      (by sep_ac_rfl)

theorem decodeState_err_drop_53e0c_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (n : Nat) (s0 s : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (henv : ∀ evs_f, FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_f st)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc (s.readReg64 .x20) n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 1296 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post :=
  decodeState_err_drop_53e0c_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st n s0 s P R post hpost henv herr hpc hrun hsp hs0A htr hx19 hP

set_option maxHeartbeats 800000 in
/-- Envelope-parameterized code-loaded error tail (`0x53df4..0x53e7c`, offsets `2392..2532`):
copies the partially-decoded `proto::PqRatchetState` at `[sp + 0x160]` (`s0.sp - 1040#64`) into
`[sp + 0x2c0]` (`s0.sp - 688#64`) via `memcpy(..., 352)`, drops it via code-loaded
`drop_in_place<proto::PqRatchetState>` (Block `270`), and executes
`decodeState_err_drop_53e0c_cl_placed_ofEnv` on the boxed `DecodeError` in `x20`. -/
theorem decodeState_err_tail_53df4_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (n : Nat)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (henv : ∀ evs_f, FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_f st)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2392#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc (s.readReg64 .x20) n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 688#64) 352 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy := hc.session_memcpy allocHookStack (by decide) (by decide)
  simp only [withVmPreserved, sessionMemcpySpec] at hmemcpy
  have hdrop := hc.dropProtoPqRatchetState
  simp only [withLsCl, dropProtoPqRatchetStatePlacedSpec] at hdrop
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hmemcpy hdrop ⊢
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 270)
  refine SepWP.fold (protoPqRatchetState_to_memcpy H_inner A.repAlloc
    (s0.sp - 1040#64) (s0.sp - 688#64) curSt) (by sep_focus) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro srcBs
  wp_focus_pure; intro hsrc_len
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide))
    (by sep_focus) ?_
  wp_steps_sync_pool (lsρ "memcpy")
  simp only [State.setMem_setMem]
  wp_apply
  wp_conv_pre => simp only [*]
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  refine SepWP.fold (protoPqRatchetState_of_memcpy H_inner A.repAlloc
    (s0.sp - 1040#64) (s0.sp - 688#64) curSt hsrc_len) (by sep_focus) ?_
  refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
    (by sep_focus) ?_
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) dropOptProtoInnerStateStack (by decide))
    (by sep_focus) ?_
  wp_steps_sync_pool (lsmpl.base 270)
  simp only [State.setMem_setMem]
  apply SepWP.done
  · wp_norm_lhs
  · simp only [wp_norm, arm64_norm, *]
  intro _hcl_call
  wp_call hdrop (({ a := s0.sp - 688#64, st := curSt } : DropProtoPqRatchetStateGhost), st)
  have hstk_sf :
      stackAt sf.sp dropOptProtoInnerStateStack =
        stackAt (s0.sp - 1392#64) dropOptProtoInnerStateStack := by
    rw [hsp_sf, hsp]
  refine SepWP.fold (Entails.of_eq hstk_sf) (by sep_focus) ?_
  refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) dropOptProtoInnerStateStack (by decide))
    (by sep_focus) ?_
  refine SepWP.fold (frame_4chunks_to_1296 s0.sp) (by sep_focus) ?_
  exact decodeState_err_drop_53e0c_cl_placed_ofEnv hc x st0 (M.stepEvents w st) n s0 _ _ R post
    hpost
    (fun evs_f hfree_f => by
      rw [← M.stepEvents_append]
      exact henv (w ++ evs_f) (‹FreeOnlyEvs w›.append hfree_f))
    herr
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    hs0A
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by
      dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30]
      simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_tail_53df4_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (n : Nat)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (henv : ∀ evs_f, FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_f st)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2392#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc (s.readReg64 .x20) n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 688#64) 352 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post :=
  decodeState_err_tail_53df4_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt n s0 s hcl P R post hpost henv herr hpc hrun hsp hs0A htr hx19 hP

/-! ## 2. Panic-Aware Call Helpers (`DecodeError::push`, `DecodeError::from`) in `SepWPpIPlaced` -/

theorem SepWPpIPlaced.call_decodeErrorPush_cl_gen [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (d e : BitVec 64) (n : Nat) (st : M.σ) {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = d)
    (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hP : P = ((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      DecodeErrorPushEnv n evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      SepWPpIPlaced prog ret sf
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - decodeErrorHookStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hpre : s.mem ⊨
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)).pre (d, e, n, st) s ∗
        (F_ext ∗ R') := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv.1, ?_⟩
    dsimp only [decodeErrorPushBudgetSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hn, hfits⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur decodeErrorHookStack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (d, e, n, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (decodeErrorPushBudgetSpec M A lim).post (d, e, n, st) s sm ∗ (F_ext ∗ R')
      at hpost
    dsimp only [decodeErrorPushBudgetSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    have hpost_env : sm.mem ⊨ ⌜DecodeErrorPushEnv n evs⌝ ∗
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - decodeErrorHookStack) ∗
            stackAt sp_cur decodeErrorHookStack)) ∗ F) ∗ R' := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; sep_ac_rfl
    rw [satisfies_pure_sepConj] at hpost_env
    rcases hpost_env with ⟨hevs, hpost1⟩
    rw [hlr] at hpcm; rw [hsp] at hspm
    have hpost2 : sm.mem ⊨
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt sp_cur v1StateMergeStack) ∗ F) ∗ R' :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur decodeErrorHookStack (by decide))))))) hpost1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm evs hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm
        (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [decodeErrorPushBudgetSpec, withLsCodeLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [decodeErrorPushBudgetSpec, withLsCodeLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [decodeErrorPushBudgetSpec, withLsCodeLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_decodeErrorPush_cl_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (d e : BitVec 64) (n : Nat) (st : M.σ) {x_outer : DecodeStateGhost × M.σ} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = d)
    (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hP : P = ((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      DecodeErrorPushEnv n evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      SepWPpIPlaced prog ret sf
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv x_outer s0 R) :=
  SepWPpIPlaced.call_decodeErrorPush_cl_gen hcall d e n st hpc hrun hsp hs0A hlr htr hx0 hn
    hfits hP hnext

theorem SepWPpIPlaced.call_decodeErrorPush_cl [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (d e : BitVec 64) (n : Nat) (st : M.σ) {x_outer : DecodeStateGhost × M.σ} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = d)
    (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hP : P = ((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      DecodeErrorPushEnv n evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      SepWPpIPlaced prog ret sf
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A lim x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A lim x_outer s0 R) :=
  SepWPpIPlaced.call_decodeErrorPush_cl_gen hcall d e n st hpc hrun hsp hs0A hlr htr hx0 hn
    hfits hP hnext

theorem SepWPpIPlaced.call_decodeErrorFrom_cl_gen [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (k w : BitVec 64) (st : M.σ) {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = k)
    (hw : KindNoHeap w)
    (hfits : FitsEnv M lim st DecodeErrorFromEnv)
    (hP : P = ((k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (v_k : BitVec 64) (evs : List AllocEvent),
      DecodeErrorFromEnv evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        ((decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗
          memRegion (k + 8#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - decodeErrorHookStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hpre : s.mem ⊨
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)).pre (k, w, st) s ∗
        (F_ext ∗ R') := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv.1, ?_⟩
    dsimp only [decodeErrorFromBudgetSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hw, hfits⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur decodeErrorHookStack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (k, w, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (decodeErrorFromBudgetSpec M A lim).post (k, w, st) s sm ∗ (F_ext ∗ R')
      at hpost
    dsimp only [decodeErrorFromBudgetSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_ne, htrm⟩, hpost⟩
    rw [hlr] at hpcm; rw [hsp] at hspm
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [ProofLib.memRegion_split' (b := k) (n := 8) (k := 40)
        (b' := k + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight k] at hpost
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨v_k, hpost⟩
    have hpost_env : sm.mem ⊨ ⌜DecodeErrorFromEnv evs⌝ ∗
        ((decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗
          memRegion (k + 8#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - decodeErrorHookStack) ∗
            stackAt sp_cur decodeErrorHookStack)) ∗ F) ∗ R' := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; sep_ac_rfl
    rw [satisfies_pure_sepConj] at hpost_env
    rcases hpost_env with ⟨hevs, hpost1⟩
    have hpost2 : sm.mem ⊨
        ((decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗
          memRegion (k + 8#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt sp_cur v1StateMergeStack) ∗ F) ∗ R' :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur decodeErrorHookStack (by decide)))))))) hpost1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm v_k evs hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne
        (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [decodeErrorFromBudgetSpec, withLsCodeLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [decodeErrorFromBudgetSpec, withLsCodeLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [decodeErrorFromBudgetSpec, withLsCodeLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_decodeErrorFrom_cl_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (k w : BitVec 64) (st : M.σ) {x_outer : DecodeStateGhost × M.σ} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = k)
    (hw : KindNoHeap w)
    (hfits : FitsEnv M lim st DecodeErrorFromEnv)
    (hP : P = ((k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (v_k : BitVec 64) (evs : List AllocEvent),
      DecodeErrorFromEnv evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        ((decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗
          memRegion (k + 8#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv x_outer s0 R) :=
  SepWPpIPlaced.call_decodeErrorFrom_cl_gen hcall k w st hpc hrun hsp hs0A hlr htr hx0 hw
    hfits hP hnext

theorem SepWPpIPlaced.call_decodeErrorFrom_cl [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (k w : BitVec 64) (st : M.σ) {x_outer : DecodeStateGhost × M.σ} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = k)
    (hw : KindNoHeap w)
    (hfits : FitsEnv M lim st DecodeErrorFromEnv)
    (hP : P = ((k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (v_k : BitVec 64) (evs : List AllocEvent),
      DecodeErrorFromEnv evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        ((decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗
          memRegion (k + 8#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A lim x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A lim x_outer s0 R) :=
  SepWPpIPlaced.call_decodeErrorFrom_cl_gen hcall k w st hpc hrun hsp hs0A hlr htr hx0 hw
    hfits hP hnext

/-! ## 3. Code-Loaded Error Push Blocks (`0x53dec`, `0x53dcc`, `0x53cdc`) -/

/-- Envelope-parameterized code-loaded error push at `0x53dec..0x53df0` (`+2384..+2388`, 2 instructions)
followed by `decodeState_err_tail_53df4_cl_placed_ofEnv`. -/
theorem decodeState_err_push_53dec_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState)
    (errBox : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushEnv n))
    (henv : ∀ evs_p evs_f, DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 = M.stepEvents evs_f (M.stepEvents evs_p st))
    (hpc : s.pc = decodeStatePlacedEntry + 2384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 688#64)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ errBox) ∗
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hpush := hc.decodeErrorPush
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hpush ⊢
  refine SepWPpIPlaced.of_sepWP (mid := lsmpl.base 257) ?_
  wp_steps_sync_pool (lsmpl.base 257)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine SepWPpIPlaced.call_decodeErrorPush_cl_ofEnv hpush (s0.sp - 688#64) errBox n st
    (ret_pc := (blkPl_325).base + 2388#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx0])
    (hn := hn)
    (hfits := hfits)
    (hP := by sep_focus) ?_
  intro s1 evs_p hevs_p hpc1 hrun1 hsp1 htr1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
  refine SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2392#64) ?_
  wp_steps_sync_pool ((blkPl_325).base + 2392#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (scratch_688_fold_48 s0.sp errBox) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPpIPlaced.of_sepWP_ret_lscl fun hcl => ?_
  exact decodeState_err_tail_53df4_cl_placed_ofEnv hc x st0 (M.stepEvents evs_p st) curSt (n + 1)
    s0 _ hcl _ R post hpost
    (fun evs_f hfree_f => henv evs_p evs_f hevs_p hfree_f)
    herr
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    hs0A
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by
      dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, Reg.fp]
      simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_push_53dec_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState)
    (errBox : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushEnv n))
    (henv : ∀ evs_p evs_f, DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 = M.stepEvents evs_f (M.stepEvents evs_p st))
    (hpc : s.pc = decodeStatePlacedEntry + 2384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 688#64)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ errBox) ∗
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_push_53dec_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt errBox n s0 s P R post hpost herr hn hfits henv hpc hrun hsp hs0A htr hx0 hx19 hP

/-- Envelope-parameterized code-loaded error push at `0x53dcc..0x53df0` (`+2352..+2388`, 10 instructions):
sets `("PqRatchetState", "version_negotiation")` and delegates to
`decodeState_err_push_53dec_cl_placed_ofEnv`. -/
theorem decodeState_err_push_53dcc_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState)
    (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushEnv n))
    (henv : ∀ evs_p evs_f, DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 = M.stepEvents evs_f (M.stepEvents evs_p st))
    (hpc : s.pc = decodeStatePlacedEntry + 2352#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeErrorAtStackLen A.repAlloc (s.readReg64 .x1) n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  refine SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2384#64) ?_
  wp_steps_sync_pool ((blkPl_325).base + 2384#64)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  exact decodeState_err_push_53dec_cl_placed_ofEnv hc x st0 st curSt (s.readReg64 .x1) n
    s0 _ _ R post hpost herr hn hfits henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
        Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_push_53dcc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState)
    (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushEnv n))
    (henv : ∀ evs_p evs_f, DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 = M.stepEvents evs_f (M.stepEvents evs_p st))
    (hpc : s.pc = decodeStatePlacedEntry + 2352#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeErrorAtStackLen A.repAlloc (s.readReg64 .x1) n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_push_53dcc_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 n s0 s P R post hpost herr hn hfits henv hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized code-loaded error push at `0x53cdc..0x53cfc` (`+2112..+2144`, 9 instructions):
sets `("PqRatchetState", "chain")` and jumps to `0x53dec`
(`decodeState_err_push_53dec_cl_placed_ofEnv`). -/
theorem decodeState_err_push_53cdc_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState)
    (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushEnv n))
    (henv : ∀ evs_p evs_f, DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 = M.stepEvents evs_f (M.stepEvents evs_p st))
    (hpc : s.pc = decodeStatePlacedEntry + 2112#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeErrorAtStackLen A.repAlloc (s.readReg64 .x1) n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  refine SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2384#64) ?_
  wp_steps_sync_pool ((blkPl_325).base + 2384#64)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  exact decodeState_err_push_53dec_cl_placed_ofEnv hc x st0 st curSt (s.readReg64 .x1) n
    s0 _ _ R post hpost herr hn hfits henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
        Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_push_53cdc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState)
    (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushEnv n))
    (henv : ∀ evs_p evs_f, DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 = M.stepEvents evs_f (M.stepEvents evs_p st))
    (hpc : s.pc = decodeStatePlacedEntry + 2112#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeErrorAtStackLen A.repAlloc (s.readReg64 .x1) n ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_push_53cdc_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 n s0 s P R post hpost herr hn hfits henv hpc hrun hsp hs0A htr hx19 hP

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitClPlacedBudget
