/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Stack Frame & Error Exits for `spqr::decode_state` (Block `325`)

Proves the budget-threaded relocatable shared epilogue (`+2500..+2528`), `DecodeError`
drop/unwind tail (`+2392..+2528`), and top-level `DecodeError::push` error-exit blocks.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (box72_entails_memRegion kindNoHeap_branch_false shl5_toNat)
open CryptoVerification.LibsignalSpqrV1 (PqRatchetState spqrDecodeState)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost DropProtoPqRatchetStateGhost TraceVRegs V1InnerHeapPred
   decodeErrorWith_unfold decodeStatePlacedEntry decodeStatePlacedProg decodeStateResultAt
   decodeStateSavedAt decodeStateStackX decodeState_stack_restore_1296
   dropOptProtoInnerStateStack fold_decodeStateResultAt_err frame_4chunks_to_1296
   memRegion_352_err_split protoPqRatchetStateAt protoPqRatchetState_of_memcpy
   protoPqRatchetState_to_memcpy scratch_688_fold_48 sp_sub_1392_aligned
   stackAt_of_callee stackAt_to_callee)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv DecodeErrorPushEnv decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec
   withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (deallocFreeOnlySpec freeOnlyEvs_rustDeallocEvents subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitBudget
  (SepWPp.call_decodeErrorFrom_gen SepWPp.call_decodeErrorPush_gen)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlaced decodeStatePlacedSpecX dropProtoPqRatchetStatePlacedSpec
   spqrDecodeStatePlacedSpec spqrDecodeStatePlacedSpecOfEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Relocatable Budget-Threaded Postcondition & Envelope Helpers -/

abbrev decodeStatePostPlacedOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop)
    (x : DecodeStateGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (spqrDecodeStatePlacedSpecOfEnv H_inner A lim PreEnv PostEnv).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev decodeStatePanicPostPlacedOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop)
    (x : DecodeStateGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (spqrDecodeStatePlacedSpecOfEnv H_inner A lim PreEnv PostEnv).onPanic x s0 sf ∗ R)

abbrev decodeStatePostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DecodeStateGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStatePlacedSpecX H_inner A lim).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev decodeStatePanicPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DecodeStateGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStatePlacedSpecX H_inner A lim).onPanic x s0 sf ∗ R)

theorem pool_fold_postEnv {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {x : DecodeStateGhost} {st0 st : M.σ} {s0 sf : State}
    (htr : sf.trace = s0.trace)
    (henv : ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = st) :
    A.pool lim st sf ⊢
      (∃∗ evs : List AllocEvent,
        ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st0) sf) := by
  rcases henv with ⟨evs, hpostEnv, hst⟩
  rw [← hst]
  exact Arm64.Entails.trans
    (Entails.pure_right ⟨htr, hpostEnv⟩ (Entails.of_eq rfl))
    (@Entails.sepExists_intro (List AllocEvent)
      (fun evs' => ⌜sf.trace = s0.trace ∧ PostEnv x evs'⌝ ∗
        A.pool lim (M.stepEvents evs' st0) sf) evs)

theorem sepWP_done_postEnv [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {prog : Program} {s0 sf : State} {P F R : SepProp}
    {x : DecodeStateGhost} {st0 st : M.σ}
    (hpc : sf.pc = s0.readReg64 .x30)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s0.sp)
    (hcs : CalleeSavedPreserved s0 sf)
    (htr : sf.trace = s0.trace)
    (henv : ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = st)
    (hf : P = A.pool lim st sf ∗ F)
    (hF : F = v1StateJumpTablesPlacedAt ∗ x.st.at A.repAlloc ∗
        decodeStateResultAt H_inner A.repAlloc x.outPtr (spqrDecodeState x.st.bytes) ∗
        stackAt s0.sp decodeStateStackX) :
    SepWP prog (s0.readReg64 .x30) sf P
      (decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  apply SepWP.done hpc hrun
  refine ⟨fun hm => ?_, hsp, hcs⟩
  dsimp only [spqrDecodeStatePlacedSpecOfEnv]
  rw [hf, hF] at hm
  exact Satisfies.mono (sepConj_mono_left (sepConj_mono_left (pool_fold_postEnv htr henv))) hm

theorem decodeStateEnv_of_loop {M : AllocCostModel} {x : DecodeStateGhost}
    {st0 st : M.σ} {f : Nat} {evs_acc : List AllocEvent}
    (hf : f ≤ 16 * x.st.bytes.length + 32)
    (hloop : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st) :
    ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = st :=
  ⟨evs_acc, hloop.mono_fuel hf, hst⟩

theorem decodeStateEnv_of_loop_free {M : AllocCostModel} {x : DecodeStateGhost}
    {st0 st : M.σ} {f : Nat} {evs_acc : List AllocEvent}
    (hf : f + 1 ≤ 16 * x.st.bytes.length + 32)
    (hloop : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st) :
    ∀ evs_f, FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_f st := by
  intro evs_f hfree
  refine ⟨evs_acc ++ evs_f,
    (hloop.append (DecodeStateLoopEnv.single (fuel := 0) (.deallocs hfree))).mono_fuel hf, ?_⟩
  rw [M.stepEvents_append, hst]

theorem decodeStateEnv_of_loop_push_free {M : AllocCostModel} {x : DecodeStateGhost}
    {st0 st : M.σ} {f n : Nat} {evs_acc : List AllocEvent}
    (hn : n ≤ 4)
    (hf : f + 2 ≤ 16 * x.st.bytes.length + 32)
    (hloop : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st) :
    ∀ evs_p evs_f, DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 = M.stepEvents evs_f (M.stepEvents evs_p st) := by
  intro evs_p evs_f hpush hfree
  have hp1 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr hn hpush)
  have hf1 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_f :=
    DecodeStateLoopEnv.single (fuel := 0) (.deallocs hfree)
  refine ⟨(evs_acc ++ evs_p) ++ evs_f, ((hloop.append hp1).append hf1).mono_fuel hf, ?_⟩
  rw [M.stepEvents_append, M.stepEvents_append, hst]

/-! ## 2. Shared Epilogue `0x53e60..0x53e7c` and Error Tail `0x53df4..0x53e5c` -/

/-- Envelope-parameterized shared epilogue `0x53e60..0x53e7c` (`+2500..+2528`, 8 instructions):
restores `sp := sp + 0x510`, pops `x20, x19, ..., x29, x30`, `sp := sp + 0x60`, and returns. -/
theorem decodeState_epilogue_53e60_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 st : M.σ) (s0 s : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (henv : ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = st)
    (hpc : s.pc = decodeStatePlacedEntry + 2500#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      decodeStateResultAt H_inner A.repAlloc x.outPtr (spqrDecodeState x.st.bytes) ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 1296 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP hpost
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  unfold decodeStateSavedAt
  wp_steps_sync_pool (s0.readReg64 .x30)
  simp only [State.setMem_setMem]
  refine SepWP.fold (decodeState_stack_restore_1296 s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
    unfold decodeStateSavedAt
    sep_focus) ?_
  exact sepWP_done_postEnv
    (by simp only [wp_norm, arm64_norm, Reg.x30])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm])
    (by unfold CalleeSavedPreserved; simp only [wp_norm, arm64_norm, hvregs, and_self])
    (by simp only [wp_norm, arm64_norm, htr])
    henv
    (by sep_focus)
    (by sep_ac_rfl)

theorem decodeState_epilogue_53e60_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 st : M.σ) (s0 s : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (henv : ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = st)
    (hpc : s.pc = decodeStatePlacedEntry + 2500#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      decodeStateResultAt H_inner A.repAlloc x.outPtr (spqrDecodeState x.st.bytes) ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 1296 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post :=
  decodeState_epilogue_53e60_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    x st0 st s0 s P R post hpost henv hpc hrun hsp hs0A htr hP

set_option maxHeartbeats 800000 in
/-- Envelope-parameterized inlined `drop_glue::<DecodeError>` + `Err(Error::StateDecode)` write +
epilogue (`0x53e0c..0x53e7c`, `+2416..+2528`, 29 instructions). -/
theorem decodeState_err_drop_53e0c_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
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

theorem decodeState_err_drop_53e0c_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
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
  decodeState_err_drop_53e0c_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st n s0 s P R post hpost henv herr hpc hrun hsp hs0A htr hx19 hP

set_option maxHeartbeats 800000 in
/-- Envelope-parameterized error tail (`0x53df4..0x53e7c`, offsets `2392..2532`):
copies the partially-decoded `proto::PqRatchetState` at `[sp + 0x160]` (`s0.sp - 1040#64`) into
`[sp + 0x2c0]` (`s0.sp - 688#64`) via `memcpy(..., 352)`, drops it via
`drop_in_place<proto::PqRatchetState>`, and executes `decodeState_err_drop_53e0c_placed_ofEnv` on the
boxed `DecodeError` in `x20`. -/
theorem decodeState_err_tail_53df4_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
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
  simp only [dropProtoPqRatchetStatePlacedSpec] at hdrop
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hmemcpy hdrop ⊢
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
  wp_call hdrop (({ a := s0.sp - 688#64, st := curSt } : DropProtoPqRatchetStateGhost), st)
  have hstk_sf :
      stackAt sf.sp dropOptProtoInnerStateStack =
        stackAt (s0.sp - 1392#64) dropOptProtoInnerStateStack := by
    rw [hsp_sf, hsp]
  refine SepWP.fold (Entails.of_eq hstk_sf) (by sep_focus) ?_
  refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) dropOptProtoInnerStateStack (by decide))
    (by sep_focus) ?_
  refine SepWP.fold (frame_4chunks_to_1296 s0.sp) (by sep_focus) ?_
  exact decodeState_err_drop_53e0c_placed_ofEnv hc x st0 (M.stepEvents w st) n s0 _ _ R post hpost
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

theorem decodeState_err_tail_53df4_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
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
  decodeState_err_tail_53df4_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt n s0 s P R post hpost henv herr hpc hrun hsp hs0A htr hx19 hP

/-! ## 3. Panic-Aware Call Helpers (`DecodeError::push`, `DecodeError::from`) & `0x53cdc..0x53df0` -/

theorem SepWPp.call_decodeErrorPush_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorPushBudgetSpec M A lim))
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
      SepWPp prog ret sf
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv x_outer s0 R)) :
    SepWPp prog ret s P Q
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv x_outer s0 R) :=
  SepWPp.call_decodeErrorPush_gen hcall d e n st hpc hrun hsp hs0A hlr htr hx0 hn hfits hP hnext
    (fun _ _ h hm => False.elim (h R hm))

theorem SepWPp.call_decodeErrorPush_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorPushBudgetSpec M A lim))
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
      SepWPp prog ret sf
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A lim x_outer s0 R)) :
    SepWPp prog ret s P Q (decodeStatePanicPostPlaced H_inner A lim x_outer s0 R) :=
  SepWPp.call_decodeErrorPush_gen hcall d e n st hpc hrun hsp hs0A hlr htr hx0 hn hfits hP hnext
    (fun _ _ h hm => False.elim (h R hm))

theorem SepWPp.call_decodeErrorFrom_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorFromBudgetSpec M A lim))
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
      SepWPp prog ret sf
        ((decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗
          memRegion (k + 8#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv x_outer s0 R)) :
    SepWPp prog ret s P Q
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv x_outer s0 R) :=
  SepWPp.call_decodeErrorFrom_gen hcall k w st hpc hrun hsp hs0A hlr htr hx0 hw hfits hP hnext
    (fun _ _ h hm => False.elim (h R hm))

theorem SepWPp.call_decodeErrorFrom_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorFromBudgetSpec M A lim))
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
      SepWPp prog ret sf
        ((decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗
          memRegion (k + 8#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A lim x_outer s0 R)) :
    SepWPp prog ret s P Q (decodeStatePanicPostPlaced H_inner A lim x_outer s0 R) :=
  SepWPp.call_decodeErrorFrom_gen hcall k w st hpc hrun hsp hs0A hlr htr hx0 hw hfits hP hnext
    (fun _ _ h hm => False.elim (h R hm))

/-- Envelope-parameterized error push at `0x53dec..0x53df0` (`+2384..+2388`, 2 instructions)
followed by `decodeState_err_tail_53df4_placed_ofEnv`: calls `DecodeError::push` on
`x0 = s0.sp - 688#64` holding `errBox`, loads `x20 := [sp + 0x2c0]`, and drops `curSt` and
`errBox`. -/
theorem decodeState_err_push_53dec_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
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
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hpush := hc.decodeErrorPush
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hpush ⊢
  wp_steps_sync_pool (lsmpl.base 257)
  simp only [State.setMem_setMem]
  refine SepWPp.call_decodeErrorPush_placed_ofEnv hpush (s0.sp - 688#64) errBox n st
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
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool ((blkPl_325).base + 2392#64)
  simp only [State.setMem_setMem]
  refine SepWP.fold (scratch_688_fold_48 s0.sp errBox) (by sep_focus) ?_
  exact decodeState_err_tail_53df4_placed_ofEnv hc x st0 (M.stepEvents evs_p st) curSt (n + 1)
    s0 _ _ R post hpost
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

theorem decodeState_err_push_53dec_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
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
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_push_53dec_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt errBox n s0 s P R post hpost herr hn hfits henv hpc hrun hsp hs0A htr hx0 hx19 hP

/-- Envelope-parameterized error push at `0x53dcc..0x53df0` (`+2352..+2388`, 10 instructions):
stores `x1` (`errBox`) at `[sp + 0x2c0]` (`s0.sp - 688#64`), sets
`("PqRatchetState", "version_negotiation")`, and delegates to
`decodeState_err_push_53dec_placed_ofEnv`. -/
theorem decodeState_err_push_53dcc_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
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
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  wp_steps_sync_pool ((blkPl_325).base + 2384#64)
  simp only [State.setMem_setMem]
  exact decodeState_err_push_53dec_placed_ofEnv hc x st0 st curSt (s.readReg64 .x1) n
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
      sep_ac_rfl)

theorem decodeState_err_push_53dcc_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
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
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_push_53dcc_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 n s0 s P R post hpost herr hn hfits henv hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized error push at `0x53cdc..0x53cfc` (`+2112..+2144`, 9 instructions):
stores `x1` (`errBox`) at `[sp + 0x2c0]` (`s0.sp - 688#64`), sets `("PqRatchetState", "chain")`,
and jumps to `0x53dec` (`decodeState_err_push_53dec_placed_ofEnv`). -/
theorem decodeState_err_push_53cdc_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
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
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  wp_steps_sync_pool ((blkPl_325).base + 2384#64)
  simp only [State.setMem_setMem]
  exact decodeState_err_push_53dec_placed_ofEnv hc x st0 st curSt (s.readReg64 .x1) n
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
      sep_ac_rfl)

theorem decodeState_err_push_53cdc_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
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
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_push_53cdc_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 n s0 s P R post hpost herr hn hfits henv hpc hrun hsp hs0A htr hx19 hP

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
