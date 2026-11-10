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
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErr
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Budget Code-Loaded `ChainEpochPB` Drop Helpers

Budget-threaded code-loaded `[LibsignalPlacement]` proofs of the `ChainEpochPB` drop helpers
(`+1976`, `+1924`, `+1908`, `+2936`) and shared `DecodeError::from` block (`+1900`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (ChainEpochPB EpochDirectionPB PqRatchetState spqrDecodeState)
open CryptoVerification.SpqrV1.ProtoRepr
  (chainEpochPBAt epochDirectionPBAt optEpochDirectionPBAt rustBytesVecAt)
open CryptoVerification.SpqrV1.Drop (cap_add_one_beq_zero_false)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg
   decodeStateSavedAt epochDirection_recv_none_to_56 epochDirection_recv_raw_to_56
   epochDirection_send_raw_to_48 epoch_regions_to_err_frame optEpochDirectionPBAt_none
   optEpochDirectionPBAt_some protoPqRatchetStateAt rustBytesVecAt_unfold_drop
   sp_sub_1392_aligned stackAt_of_callee stackAt_to_callee)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (deallocFreeOnlySpec freeOnlyEvs_rustDeallocEvents subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget
  (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubClPlacedBudgetAux
  (decodeState_err_push_53c9c_cl_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced SepWPpIPlaced.of_sepWP)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudgetAux
  (decodeStateEpochErrTailFramePlaced decodeStateEpochErrFramePlaced
   fitsEnv_epochDrop_push1_of_loop fitsEnv_epochDrop_push2_of_loop
   decodeStateEnv_of_loop_epochDrop_push2_free)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudgetAux
  (decodeStateEnv_of_loop_from_epochDrop_push2_free
   decodeStateEnv_of_loop_push_epochDrop_push2_free)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem shift_hfits1 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {n : Nat}
    {evs_s : List AllocEvent} (hs : FreeOnlyEvs evs_s)
    (hfits1 : ∀ evs_d, FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d st) (DecodeErrorPushEnv n)) :
    ∀ evs_r, FreeOnlyEvs evs_r →
      FitsEnv M lim (M.stepEvents evs_r (M.stepEvents evs_s st)) (DecodeErrorPushEnv n) := by
  intro evs_r hr
  rw [← M.stepEvents_append evs_s evs_r st]
  exact hfits1 (evs_s ++ evs_r) (hs.append hr)

private theorem shift_hfits2 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {n : Nat}
    {evs_s : List AllocEvent} (hs : FreeOnlyEvs evs_s)
    (hfits2 : ∀ evs_d evs_p1, FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d st)) (DecodeErrorPushEnv (n + 1))) :
    ∀ evs_r evs_p1, FreeOnlyEvs evs_r → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_r (M.stepEvents evs_s st)))
        (DecodeErrorPushEnv (n + 1)) := by
  intro evs_r evs_p1 hr hp1
  rw [← M.stepEvents_append evs_s evs_r st]
  exact hfits2 (evs_s ++ evs_r) evs_p1 (hs.append hr) hp1

private theorem shift_henv {M : AllocCostModel} {PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {x : DecodeStateGhost} {st0 st : M.σ} {n : Nat}
    {evs_s : List AllocEvent} (hs : FreeOnlyEvs evs_s)
    (henv : ∀ evs_d evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d st)))) :
    ∀ evs_r evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_r → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_r (M.stepEvents evs_s st)))) := by
  intro evs_r evs_p1 evs_p2 evs_f hr hp1 hp2 hfree
  rw [← M.stepEvents_append evs_s evs_r st]
  exact henv (evs_s ++ evs_r) evs_p1 evs_p2 evs_f (hs.append hr) hp1 hp2 hfree

/-! ## `ChainEpochPB` Inlined Drop & Push Paths (`0x53c5c`, `0x53c28`, `0x53c18`, `0x54014`) -/

set_option maxHeartbeats 1600000 in
/-- Envelope-parameterized drop of `curEpoch.recv : Option EpochDirectionPB` at `[sp + 0x2f8]`
(`s0.sp - 632#64`), continuing to `decodeState_err_push_53c9c_cl_placed_ofEnv` (`+1984`, 16 instructions). -/
theorem decodeState_err_drop_epoch_recv_53c5c_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState)
    (optRecv : Option EpochDirectionPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : ∀ evs_d, FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d st) (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_d evs_p1, FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d st)) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_d evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d st))))
    (hpc : s.pc = decodeStatePlacedEntry + 1984#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx1 : s.readReg64 .x1 = errBox)
    (hx20 : s.readReg64 .x20 = errBox)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      memRegion (s0.sp - 680#64) 48 ∗
      optEpochDirectionPBAt A.repAlloc (s0.sp - 632#64) optRecv ∗
      decodeStateEpochErrTailFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have htr_full := htr
  rcases htr with ⟨htr_eq, hvregs⟩
  have hdealloc := subroutine_ok_deallocFreeOnly hc.dealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry,
    decodeStateEpochErrTailFramePlaced] at hpc hdealloc ⊢
  dsimp only [Reg.x1, Reg.x19, Reg.x20] at hx1 hx19 hx20
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2048#64)
  cases optRecv with
  | none =>
    rw [optEpochDirectionPBAt_none]
    have ha624 : (s0.sp - 632#64) + 8#64 = s0.sp - 624#64 := by bv_omega
    rw [ha624]
    wp_steps_sync_pool ((blkPl_325).base + 2048#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (epochDirection_recv_none_to_56 s0.sp noneCap) (by sep_focus) ?_
    refine SepWP.fold (epoch_regions_to_err_frame s0.sp) (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
    exact decodeState_err_push_53c9c_cl_placed_ofEnv hc x st0 st curSt w0 n s0 _ _ R post hpost herr hn
      (hfits1 [] .nil)
      (fun evs_p1 hp1 => hfits2 [] evs_p1 .nil hp1)
      (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree => henv [] evs_p1 evs_p2 evs_f .nil hp1 hp2 hfree)
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm, hsp])
      hs0A
      (by simp only [wp_norm, arm64_norm, htr_full])
      (by dsimp only [Reg.x19]; simp only [wp_norm, arm64_norm, hx19])
      (by
        dsimp only [decodeStateErrFramePlaced, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
          Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        simp only [wp_norm, arm64_norm, *]
        sep_ac_rfl)
  | some d =>
    rw [optEpochDirectionPBAt_some]
    unfold epochDirectionPBAt
    have ha608 : (s0.sp - 632#64) + 0x18#64 = s0.sp - 608#64 := by bv_omega
    have ha584 : (s0.sp - 632#64) + 0x30#64 = s0.sp - 584#64 := by bv_omega
    have ha580 : (s0.sp - 632#64) + 0x34#64 = s0.sp - 580#64 := by bv_omega
    rw [ha608, ha584, ha580]
    refine SepWP.fold (rustBytesVecAt_unfold_drop A.repAlloc (s0.sp - 632#64) d.next)
      (by sep_focus) ?_
    simp only [RustCliAllocBudget.repAlloc_live]
    wp_pull_exists
    rename_i cap1 ptr1
    wp_focus_pure; rintro ⟨_, hlt1, hptr1⟩
    refine SepWP.fold (rustBytesVecAt_unfold_drop A.repAlloc (s0.sp - 608#64) d.prev)
      (by sep_focus) ?_
    simp only [RustCliAllocBudget.repAlloc_live]
    wp_pull_exists
    rename_i cap2 ptr2
    wp_focus_pure; rintro ⟨_, hlt2, hptr2⟩
    have hcmn1 : ¬((cap1 + 1#64 == 0#64) = true) := cap_add_one_beq_zero_false hlt1
    refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide))
      (by sep_focus) ?_
    by_cases hc1 : cap1 = 0#64 <;> by_cases hc2 : cap2 = 0#64
    · have hb1 : (cap1 == 0#64) = true := beq_iff_eq.mpr hc1
      have hb2 : (cap2 == 0#64) = true := beq_iff_eq.mpr hc2
      simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps_sync_pool ((blkPl_325).base + 2048#64)
      try simp only [State.setMem_setMem]
      refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
        (by sep_focus) ?_
      refine SepWP.fold (epochDirection_recv_raw_to_56 s0.sp 0#64 ptr1
        (BitVec.ofNat 64 d.next.length) 0#64 ptr2 (BitVec.ofNat 64 d.prev.length) d.ctr)
        (by sep_focus) ?_
      refine SepWP.fold (epoch_regions_to_err_frame s0.sp) (by sep_focus) ?_
      apply SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
      exact decodeState_err_push_53c9c_cl_placed_ofEnv hc x st0 st curSt w0 n s0 _ _ R post hpost herr
        hn (hfits1 [] .nil)
        (fun evs_p1 hp1 => hfits2 [] evs_p1 .nil hp1)
        (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree => henv [] evs_p1 evs_p2 evs_f .nil hp1 hp2 hfree)
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        (by simp only [wp_norm, arm64_norm, hsp])
        hs0A
        (by simp only [wp_norm, arm64_norm, htr_full])
        (by dsimp only [Reg.x19]; simp only [wp_norm, arm64_norm, hx19])
        (by
          dsimp only [decodeStateErrFramePlaced, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
            Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm, *]
          sep_ac_rfl)
    · have hb1 : (cap1 == 0#64) = true := beq_iff_eq.mpr hc1
      have hb2 : (cap2 == 0#64) = false := beq_eq_false_iff_ne.mpr hc2
      simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      try simp only [State.setMem_setMem]
      wp_call hdealloc (ptr2, cap2.toNat, 1, st)
      have htr_sf : sf.trace = s0.trace := by
        have h1 : sf.trace = _ := ‹Heap.AllocCallPreserved _ sf›.2.1
        simpa only [wp_norm, arm64_norm, htr_eq] using h1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
        simp only [wp_norm, arm64_norm, *]
      wp_steps_sync_pool ((blkPl_325).base + 2048#64)
      try simp only [State.setMem_setMem]
      refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
        (by sep_focus) ?_
      refine SepWP.fold (epochDirection_recv_raw_to_56 s0.sp 0#64 ptr1
        (BitVec.ofNat 64 d.next.length) cap2 ptr2 (BitVec.ofNat 64 d.prev.length) d.ctr)
        (by sep_focus) ?_
      refine SepWP.fold (epoch_regions_to_err_frame s0.sp) (by sep_focus) ?_
      apply SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, *])
      have hd : FreeOnlyEvs (rustDeallocEvents cap2.toNat 1) :=
        freeOnlyEvs_rustDeallocEvents cap2.toNat 1
      exact decodeState_err_push_53c9c_cl_placed_ofEnv hc x st0
        (M.stepEvents (rustDeallocEvents cap2.toNat 1) st) curSt w0 n s0 _ _ R post hpost herr hn
        (hfits1 _ hd)
        (fun evs_p1 hp1 => hfits2 _ evs_p1 hd hp1)
        (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree => henv _ evs_p1 evs_p2 evs_f hd hp1 hp2 hfree)
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hs0A
        ⟨by simp only [wp_norm, arm64_norm, htr_sf],
         by simp only [wp_norm, arm64_norm, hvregs_sf]⟩
        (by dsimp only [Reg.x19]; simp only [wp_norm, arm64_norm, *])
        (by
          dsimp only [decodeStateErrFramePlaced, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
            Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm, *]
          sep_ac_rfl)
    · have hb1 : (cap1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc1
      have hb2 : (cap2 == 0#64) = true := beq_iff_eq.mpr hc2
      simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      try simp only [State.setMem_setMem]
      wp_call hdealloc (ptr1, cap1.toNat, 1, st)
      have htr_sf : sf.trace = s0.trace := by
        have h1 : sf.trace = _ := ‹Heap.AllocCallPreserved _ sf›.2.1
        simpa only [wp_norm, arm64_norm, htr_eq] using h1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
        simp only [wp_norm, arm64_norm, *]
      wp_steps_sync_pool ((blkPl_325).base + 2048#64)
      try simp only [State.setMem_setMem]
      refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
        (by sep_focus) ?_
      refine SepWP.fold (epochDirection_recv_raw_to_56 s0.sp cap1 ptr1
        (BitVec.ofNat 64 d.next.length) 0#64 ptr2 (BitVec.ofNat 64 d.prev.length) d.ctr)
        (by sep_focus) ?_
      refine SepWP.fold (epoch_regions_to_err_frame s0.sp) (by sep_focus) ?_
      apply SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, *])
      have hd : FreeOnlyEvs (rustDeallocEvents cap1.toNat 1) :=
        freeOnlyEvs_rustDeallocEvents cap1.toNat 1
      exact decodeState_err_push_53c9c_cl_placed_ofEnv hc x st0
        (M.stepEvents (rustDeallocEvents cap1.toNat 1) st) curSt w0 n s0 _ _ R post hpost herr hn
        (hfits1 _ hd)
        (fun evs_p1 hp1 => hfits2 _ evs_p1 hd hp1)
        (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree => henv _ evs_p1 evs_p2 evs_f hd hp1 hp2 hfree)
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hs0A
        ⟨by simp only [wp_norm, arm64_norm, htr_sf],
         by simp only [wp_norm, arm64_norm, hvregs_sf]⟩
        (by dsimp only [Reg.x19]; simp only [wp_norm, arm64_norm, *])
        (by
          dsimp only [decodeStateErrFramePlaced, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
            Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm, *]
          sep_ac_rfl)
    · have hb1 : (cap1 == 0#64) = false := beq_eq_false_iff_ne.mpr hc1
      have hb2 : (cap2 == 0#64) = false := beq_eq_false_iff_ne.mpr hc2
      simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      try simp only [State.setMem_setMem]
      wp_call hdealloc (ptr1, cap1.toNat, 1, st)
      have htr_sf : sf.trace = s0.trace := by
        have h1 : sf.trace = _ := ‹Heap.AllocCallPreserved _ sf›.2.1
        simpa only [wp_norm, arm64_norm, htr_eq] using h1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
        simp only [wp_norm, arm64_norm, *]
      wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      try simp only [State.setMem_setMem]
      wp_call hdealloc (ptr2, cap2.toNat, 1,
        M.stepEvents (rustDeallocEvents cap1.toNat 1) st)
      have htr_sf1 : sf_1.trace = s0.trace := by
        have h2 : sf_1.trace = _ := ‹Heap.AllocCallPreserved _ sf_1›.2.1
        simpa only [wp_norm, arm64_norm, htr_sf] using h2
      have hvregs_sf1 : calleeSavedVRegs sf_1 = calleeSavedVRegs s0 := by
        simp only [wp_norm, arm64_norm, *]
      wp_steps_sync_pool ((blkPl_325).base + 2048#64)
      try simp only [State.setMem_setMem]
      refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
        (by sep_focus) ?_
      refine SepWP.fold (epochDirection_recv_raw_to_56 s0.sp cap1 ptr1
        (BitVec.ofNat 64 d.next.length) cap2 ptr2 (BitVec.ofNat 64 d.prev.length) d.ctr)
        (by sep_focus) ?_
      refine SepWP.fold (epoch_regions_to_err_frame s0.sp) (by sep_focus) ?_
      apply SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, *])
      have hs1 : FreeOnlyEvs (rustDeallocEvents cap1.toNat 1) :=
        freeOnlyEvs_rustDeallocEvents cap1.toNat 1
      have hs2 : FreeOnlyEvs (rustDeallocEvents cap2.toNat 1) :=
        freeOnlyEvs_rustDeallocEvents cap2.toNat 1
      exact decodeState_err_push_53c9c_cl_placed_ofEnv hc x st0
        (M.stepEvents (rustDeallocEvents cap2.toNat 1)
          (M.stepEvents (rustDeallocEvents cap1.toNat 1) st))
        curSt w0 n s0 _ _ R post hpost herr hn
        (shift_hfits1 hs1 hfits1 _ hs2)
        (fun evs_p1 hp1 => shift_hfits2 hs1 hfits2 _ evs_p1 hs2 hp1)
        (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree =>
          shift_henv hs1 henv _ evs_p1 evs_p2 evs_f hs2 hp1 hp2 hfree)
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hs0A
        ⟨by simp only [wp_norm, arm64_norm, htr_sf1],
         by simp only [wp_norm, arm64_norm, hvregs_sf1]⟩
        (by dsimp only [Reg.x19]; simp only [wp_norm, arm64_norm, *])
        (by
          dsimp only [decodeStateErrFramePlaced, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
            Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          try simp only [wp_norm, arm64_norm, *]
          sep_ac_rfl)

theorem decodeState_err_drop_epoch_recv_53c5c_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState)
    (optRecv : Option EpochDirectionPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : ∀ evs_d, FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d st) (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_d evs_p1, FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d st)) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_d evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d st))))
    (hpc : s.pc = decodeStatePlacedEntry + 1984#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx1 : s.readReg64 .x1 = errBox)
    (hx20 : s.readReg64 .x20 = errBox)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      memRegion (s0.sp - 680#64) 48 ∗
      optEpochDirectionPBAt A.repAlloc (s0.sp - 632#64) optRecv ∗
      decodeStateEpochErrTailFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_drop_epoch_recv_53c5c_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt optRecv n hn errBox w0 s0 s P R post hpost herr
    hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hx1 hx20 hP

set_option maxHeartbeats 1200000 in
/-- Envelope-parameterized drop of `d : EpochDirectionPB` (`curEpoch.send = some d`) at
`[sp + 0x2c0]` (`s0.sp - 688#64`) after `x8 = cap1` has been loaded and checked `≠ -1`, continuing
to `decodeState_err_drop_epoch_recv_53c5c_cl_placed_ofEnv` (`+1932`, 13 instructions). -/
theorem decodeState_err_drop_epoch_send_some_53c28_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState)
    (optRecv : Option EpochDirectionPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox cap1 ptr1 : BitVec 64)
    (nextBs prevBs : List (BitVec 8)) (ctr : BitVec 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : ∀ evs_d, FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d st) (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_d evs_p1, FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d st)) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_d evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d st))))
    (hpc : s.pc = decodeStatePlacedEntry + 1932#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx8 : s.readReg64 .x8 = cap1)
    (hx1 : s.readReg64 .x1 = errBox)
    (hx20 : s.readReg64 .x20 = errBox)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      ((s0.sp - 688#64) ↦₆₄ cap1) ∗
      ((s0.sp - 680#64) ↦₆₄ ptr1) ∗
      ((s0.sp - 672#64) ↦₆₄ BitVec.ofNat 64 nextBs.length) ∗
      (if cap1 = 0#64 then emp else A.live ptr1 cap1.toNat 1 ∗ memRegion ptr1 cap1.toNat) ∗
      rustBytesVecAt A.repAlloc (s0.sp - 664#64) prevBs ∗
      ((s0.sp - 640#64) ↦₃₂ ctr) ∗
      memRegion (s0.sp - 636#64) 4 ∗
      optEpochDirectionPBAt A.repAlloc (s0.sp - 632#64) optRecv ∗
      decodeStateEpochErrTailFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have htr_full := htr
  rcases htr with ⟨htr_eq, hvregs⟩
  have hdealloc := subroutine_ok_deallocFreeOnly hc.dealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hx8
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry,
    decodeStateEpochErrTailFramePlaced] at hpc hdealloc ⊢
  dsimp only [Reg.x1, Reg.x8, Reg.x19, Reg.x20] at hx1 hx19 hx20 ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1984#64)
  refine SepWP.fold (rustBytesVecAt_unfold_drop A.repAlloc (s0.sp - 664#64) prevBs)
    (by sep_focus) ?_
  simp only [RustCliAllocBudget.repAlloc_live]
  wp_pull_exists
  rename_i cap2 ptr2
  wp_focus_pure; rintro ⟨_, hlt2, hptr2⟩
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide))
    (by sep_focus) ?_
  by_cases hc1 : s.readReg64 (Reg.gpr 8#5) = 0#64 <;> by_cases hc2 : cap2 = 0#64
  · have hb1 : (s.readReg64 (Reg.gpr 8#5) == 0#64) = true := beq_iff_eq.mpr hc1
    have hb2 : (cap2 == 0#64) = true := beq_iff_eq.mpr hc2
    simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
    wp_steps_sync_pool ((blkPl_325).base + 1984#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
      (by sep_focus) ?_
    refine SepWP.fold (epochDirection_send_raw_to_48 s0.sp ptr1
      (BitVec.ofNat 64 nextBs.length) 0#64 ptr2 (BitVec.ofNat 64 prevBs.length) ctr)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
    exact decodeState_err_drop_epoch_recv_53c5c_cl_placed_ofEnv hc x st0 st curSt optRecv n hn
      errBox 0#64 s0 _ _ R post hpost herr hfits1 hfits2 henv
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm, hsp])
      hs0A
      (by simp only [wp_norm, arm64_norm, htr_full])
      (by dsimp only [Reg.x19]; simp only [wp_norm, arm64_norm, hx19])
      (by dsimp only [Reg.x1]; simp only [wp_norm, arm64_norm, hx1])
      (by dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm, hx20])
      (by
        dsimp only [decodeStateEpochErrTailFramePlaced, Reg.x1, Reg.x19, Reg.x20, Reg.x21,
          Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        try simp only [wp_norm, arm64_norm, *]
        sep_ac_rfl)
  · have hb1 : (s.readReg64 (Reg.gpr 8#5) == 0#64) = true := beq_iff_eq.mpr hc1
    have hb2 : (cap2 == 0#64) = false := beq_eq_false_iff_ne.mpr hc2
    simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    try simp only [State.setMem_setMem]
    wp_call hdealloc (ptr2, cap2.toNat, 1, st)
    have htr_sf : sf.trace = s0.trace := by
      have h1 : sf.trace = _ := ‹Heap.AllocCallPreserved _ sf›.2.1
      simpa only [wp_norm, arm64_norm, htr_eq] using h1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      simp only [wp_norm, arm64_norm, *]
    wp_steps_sync_pool ((blkPl_325).base + 1984#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
      (by sep_focus) ?_
    refine SepWP.fold (epochDirection_send_raw_to_48 s0.sp ptr1
      (BitVec.ofNat 64 nextBs.length) cap2 ptr2 (BitVec.ofNat 64 prevBs.length) ctr)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, *])
    have hs : FreeOnlyEvs (rustDeallocEvents cap2.toNat 1) :=
      freeOnlyEvs_rustDeallocEvents cap2.toNat 1
    exact decodeState_err_drop_epoch_recv_53c5c_cl_placed_ofEnv hc x st0
      (M.stepEvents (rustDeallocEvents cap2.toNat 1) st) curSt optRecv n hn
      errBox 0#64 s0 _ _ R post hpost herr
      (shift_hfits1 hs hfits1) (shift_hfits2 hs hfits2) (shift_henv hs henv)
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hs0A
      ⟨by simp only [wp_norm, arm64_norm, htr_sf],
       by simp only [wp_norm, arm64_norm, hvregs_sf]⟩
      (by dsimp only [Reg.x19]; simp only [wp_norm, arm64_norm, *])
      (by dsimp only [Reg.x1]; simp only [wp_norm, arm64_norm, *])
      (by dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm, *])
      (by
        dsimp only [decodeStateEpochErrTailFramePlaced, Reg.x1, Reg.x19, Reg.x20, Reg.x21,
          Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        try simp only [wp_norm, arm64_norm, *]
        sep_ac_rfl)
  · have hb1 : (s.readReg64 (Reg.gpr 8#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hc1
    have hb2 : (cap2 == 0#64) = true := beq_iff_eq.mpr hc2
    simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    try simp only [State.setMem_setMem]
    wp_call hdealloc (ptr1, (s.readReg64 (Reg.gpr 8#5)).toNat, 1, st)
    have htr_sf : sf.trace = s0.trace := by
      have h1 : sf.trace = _ := ‹Heap.AllocCallPreserved _ sf›.2.1
      simpa only [wp_norm, arm64_norm, htr_eq] using h1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      simp only [wp_norm, arm64_norm, *]
    wp_steps_sync_pool ((blkPl_325).base + 1984#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
      (by sep_focus) ?_
    refine SepWP.fold (epochDirection_send_raw_to_48 s0.sp ptr1
      (BitVec.ofNat 64 nextBs.length) 0#64 ptr2 (BitVec.ofNat 64 prevBs.length) ctr)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, *])
    have hs : FreeOnlyEvs (rustDeallocEvents (s.readReg64 (Reg.gpr 8#5)).toNat 1) :=
      freeOnlyEvs_rustDeallocEvents _ 1
    exact decodeState_err_drop_epoch_recv_53c5c_cl_placed_ofEnv hc x st0
      (M.stepEvents (rustDeallocEvents (s.readReg64 (Reg.gpr 8#5)).toNat 1) st)
      curSt optRecv n hn errBox (s.readReg64 (Reg.gpr 8#5)) s0 _ _ R post hpost herr
      (shift_hfits1 hs hfits1) (shift_hfits2 hs hfits2) (shift_henv hs henv)
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hs0A
      ⟨by simp only [wp_norm, arm64_norm, htr_sf],
       by simp only [wp_norm, arm64_norm, hvregs_sf]⟩
      (by dsimp only [Reg.x19]; simp only [wp_norm, arm64_norm, *])
      (by dsimp only [Reg.x1]; simp only [wp_norm, arm64_norm, *])
      (by dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm, *])
      (by
        dsimp only [decodeStateEpochErrTailFramePlaced, Reg.x1, Reg.x19, Reg.x20, Reg.x21,
          Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        try simp only [wp_norm, arm64_norm, *]
        sep_ac_rfl)
  · have hb1 : (s.readReg64 (Reg.gpr 8#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hc1
    have hb2 : (cap2 == 0#64) = false := beq_eq_false_iff_ne.mpr hc2
    simp only [hc1, hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    try simp only [State.setMem_setMem]
    wp_call hdealloc (ptr1, (s.readReg64 (Reg.gpr 8#5)).toNat, 1, st)
    have htr_sf : sf.trace = s0.trace := by
      have h1 : sf.trace = _ := ‹Heap.AllocCallPreserved _ sf›.2.1
      simpa only [wp_norm, arm64_norm, htr_eq] using h1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      simp only [wp_norm, arm64_norm, *]
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    try simp only [State.setMem_setMem]
    wp_call hdealloc (ptr2, cap2.toNat, 1,
      M.stepEvents (rustDeallocEvents (s.readReg64 (Reg.gpr 8#5)).toNat 1) st)
    have htr_sf1 : sf_1.trace = s0.trace := by
      have h2 : sf_1.trace = _ := ‹Heap.AllocCallPreserved _ sf_1›.2.1
      simpa only [wp_norm, arm64_norm, htr_sf] using h2
    have hvregs_sf1 : calleeSavedVRegs sf_1 = calleeSavedVRegs s0 := by
      simp only [wp_norm, arm64_norm, *]
    wp_steps_sync_pool ((blkPl_325).base + 1984#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
      (by sep_focus) ?_
    refine SepWP.fold (epochDirection_send_raw_to_48 s0.sp ptr1
      (BitVec.ofNat 64 nextBs.length) cap2 ptr2 (BitVec.ofNat 64 prevBs.length) ctr)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, *])
    have hs1 : FreeOnlyEvs (rustDeallocEvents (s.readReg64 (Reg.gpr 8#5)).toNat 1) :=
      freeOnlyEvs_rustDeallocEvents _ 1
    have hs2 : FreeOnlyEvs (rustDeallocEvents cap2.toNat 1) :=
      freeOnlyEvs_rustDeallocEvents cap2.toNat 1
    exact decodeState_err_drop_epoch_recv_53c5c_cl_placed_ofEnv hc x st0
      (M.stepEvents (rustDeallocEvents cap2.toNat 1)
        (M.stepEvents (rustDeallocEvents (s.readReg64 (Reg.gpr 8#5)).toNat 1) st))
      curSt optRecv n hn errBox (s.readReg64 (Reg.gpr 8#5)) s0 _ _ R post hpost herr
      (shift_hfits1 hs2 (shift_hfits1 hs1 hfits1))
      (shift_hfits2 hs2 (shift_hfits2 hs1 hfits2))
      (shift_henv hs2 (shift_henv hs1 henv))
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hs0A
      ⟨by simp only [wp_norm, arm64_norm, htr_sf1],
       by simp only [wp_norm, arm64_norm, hvregs_sf1]⟩
      (by dsimp only [Reg.x19]; simp only [wp_norm, arm64_norm, *])
      (by dsimp only [Reg.x1]; simp only [wp_norm, arm64_norm, *])
      (by dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm, *])
      (by
        dsimp only [decodeStateEpochErrTailFramePlaced, Reg.x1, Reg.x19, Reg.x20, Reg.x21,
          Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        try simp only [wp_norm, arm64_norm, *]
        sep_ac_rfl)

theorem decodeState_err_drop_epoch_send_some_53c28_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState)
    (optRecv : Option EpochDirectionPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox cap1 ptr1 : BitVec 64)
    (nextBs prevBs : List (BitVec 8)) (ctr : BitVec 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : ∀ evs_d, FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d st) (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_d evs_p1, FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d st)) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_d evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d st))))
    (hpc : s.pc = decodeStatePlacedEntry + 1932#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx8 : s.readReg64 .x8 = cap1)
    (hx1 : s.readReg64 .x1 = errBox)
    (hx20 : s.readReg64 .x20 = errBox)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      ((s0.sp - 688#64) ↦₆₄ cap1) ∗
      ((s0.sp - 680#64) ↦₆₄ ptr1) ∗
      ((s0.sp - 672#64) ↦₆₄ BitVec.ofNat 64 nextBs.length) ∗
      (if cap1 = 0#64 then emp else A.live ptr1 cap1.toNat 1 ∗ memRegion ptr1 cap1.toNat) ∗
      rustBytesVecAt A.repAlloc (s0.sp - 664#64) prevBs ∗
      ((s0.sp - 640#64) ↦₃₂ ctr) ∗
      memRegion (s0.sp - 636#64) 4 ∗
      optEpochDirectionPBAt A.repAlloc (s0.sp - 632#64) optRecv ∗
      decodeStateEpochErrTailFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_drop_epoch_send_some_53c28_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt optRecv n hn errBox cap1 ptr1 nextBs prevBs ctr s0 s P R post hpost herr
    hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hx8 hx1 hx20 hP

/-- Envelope-parameterized drop of `curEpoch : ChainEpochPB` at `[sp + 0x2c0]` (`s0.sp - 688#64`)
with `errBox` in `x1`, continuing to `decodeState_err_push_53c9c_cl_placed_ofEnv` (`+1916`). -/
theorem decodeState_err_drop_epoch_53c18_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : ∀ evs_d, FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d st) (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_d evs_p1, FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d st)) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_d evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d st))))
    (hpc : s.pc = decodeStatePlacedEntry + 1916#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx1 : s.readReg64 .x1 = errBox)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  unfold chainEpochPBAt
  have ha632 : (s0.sp - 688#64) + 0x38#64 = s0.sp - 632#64 := by bv_omega
  rw [ha632]
  rcases hsend : curEpoch.send with _ | d
  · rw [optEpochDirectionPBAt_none]
    have ha680 : (s0.sp - 688#64) + 8#64 = s0.sp - 680#64 := by bv_omega
    rw [ha680]
    refine SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1984#64) ?_
    wp_steps_sync_pool ((blkPl_325).base + 1984#64)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    exact decodeState_err_drop_epoch_recv_53c5c_cl_placed_ofEnv hc x st0 st curSt curEpoch.recv n hn
      errBox noneCap s0 _ _ R post hpost herr hfits1 hfits2 henv
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm, hsp])
      hs0A
      (by simp only [wp_norm, arm64_norm, htr])
      (by simp only [wp_norm, arm64_norm, hx19])
      (by simp only [wp_norm, arm64_norm, hx1])
      (by simp only [wp_norm, arm64_norm, hx1])
      (by
        dsimp only [decodeStateEpochErrTailFramePlaced, Reg.x1, Reg.x19, Reg.x20, Reg.x21,
          Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        try simp only [wp_norm, arm64_norm]
        sep_ac_rfl)
  · rw [optEpochDirectionPBAt_some]
    unfold epochDirectionPBAt
    have ha664 : (s0.sp - 688#64) + 0x18#64 = s0.sp - 664#64 := by bv_omega
    have ha640 : (s0.sp - 688#64) + 0x30#64 = s0.sp - 640#64 := by bv_omega
    have ha636 : (s0.sp - 688#64) + 0x34#64 = s0.sp - 636#64 := by bv_omega
    rw [ha664, ha640, ha636]
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1932#64)
    refine SepWP.fold (rustBytesVecAt_unfold_drop A.repAlloc (s0.sp - 688#64) d.next)
      (by sep_focus) ?_
    simp only [RustCliAllocBudget.repAlloc_live]
    wp_pull_exists
    rename_i cap1 ptr1
    wp_focus_pure; rintro ⟨_, hlt1, _⟩
    have hcmn1 : ¬((cap1 + 1#64 == 0#64) = true) := cap_add_one_beq_zero_false hlt1
    wp_steps_sync_pool ((blkPl_325).base + 1932#64)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
    exact decodeState_err_drop_epoch_send_some_53c28_cl_placed_ofEnv hc x st0 st curSt curEpoch.recv
      n hn errBox cap1 ptr1 d.next d.prev d.ctr s0 _ _ R post hpost herr hfits1 hfits2 henv
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm, hsp])
      hs0A
      (by simp only [wp_norm, arm64_norm, htr])
      (by simp only [wp_norm, arm64_norm, hx19])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hx1])
      (by simp only [wp_norm, arm64_norm, hx1])
      (by
        dsimp only [decodeStateEpochErrTailFramePlaced, Reg.x1, Reg.x8, Reg.x19, Reg.x20,
          Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        try simp only [wp_norm, arm64_norm]
        sep_ac_rfl)

theorem decodeState_err_drop_epoch_53c18_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : ∀ evs_d, FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d st) (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_d evs_p1, FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d st)) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_d evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d st))))
    (hpc : s.pc = decodeStatePlacedEntry + 1916#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx1 : s.readReg64 .x1 = errBox)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_drop_epoch_53c18_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch n hn errBox s0 s P R post hpost herr
    hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hx1 hP

/-- Envelope-parameterized alternate entry (`+2936`, 5 instructions) to drop
`curEpoch : ChainEpochPB` at `[sp + 0x2c0]` (`s0.sp - 688#64`) with `errBox` in `x1`. -/
theorem decodeState_err_drop_epoch_54014_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : ∀ evs_d, FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d st) (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_d evs_p1, FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d st)) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_d evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d st))))
    (hpc : s.pc = decodeStatePlacedEntry + 2936#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx1 : s.readReg64 .x1 = errBox)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  unfold chainEpochPBAt
  have ha632 : (s0.sp - 688#64) + 0x38#64 = s0.sp - 632#64 := by bv_omega
  rw [ha632]
  rcases hsend : curEpoch.send with _ | d
  · rw [optEpochDirectionPBAt_none]
    have ha680 : (s0.sp - 688#64) + 8#64 = s0.sp - 680#64 := by bv_omega
    have hcmn_ne : (noneCap + 1#64 != 0#64) = false := rfl
    rw [ha680]
    refine SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1984#64) ?_
    wp_steps_sync_pool ((blkPl_325).base + 1984#64)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    exact decodeState_err_drop_epoch_recv_53c5c_cl_placed_ofEnv hc x st0 st curSt curEpoch.recv n hn
      errBox noneCap s0 _ _ R post hpost herr hfits1 hfits2 henv
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm, hsp])
      hs0A
      (by simp only [wp_norm, arm64_norm, htr])
      (by simp only [wp_norm, arm64_norm, hx19])
      (by simp only [wp_norm, arm64_norm, hx1])
      (by simp only [wp_norm, arm64_norm, hx1])
      (by
        dsimp only [decodeStateEpochErrTailFramePlaced, Reg.x1, Reg.x19, Reg.x20, Reg.x21,
          Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        try simp only [wp_norm, arm64_norm]
        sep_ac_rfl)
  · rw [optEpochDirectionPBAt_some]; unfold epochDirectionPBAt
    have ha664 : (s0.sp - 688#64) + 0x18#64 = s0.sp - 664#64 := by bv_omega
    have ha640 : (s0.sp - 688#64) + 0x30#64 = s0.sp - 640#64 := by bv_omega
    have ha636 : (s0.sp - 688#64) + 0x34#64 = s0.sp - 636#64 := by bv_omega
    rw [ha664, ha640, ha636]
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1932#64)
    refine SepWP.fold (rustBytesVecAt_unfold_drop A.repAlloc (s0.sp - 688#64) d.next)
      (by sep_focus) ?_
    simp only [RustCliAllocBudget.repAlloc_live]
    wp_pull_exists; rename_i cap1 ptr1; wp_focus_pure; rintro ⟨_, hlt1, _⟩
    have hcmn1 : ¬((cap1 + 1#64 == 0#64) = true) := cap_add_one_beq_zero_false hlt1
    have hcmn1_ne : (cap1 + 1#64 != 0#64) = true := by
      rw [bne_iff_ne]; exact fun h => hcmn1 (beq_iff_eq.mpr h)
    wp_steps_sync_pool ((blkPl_325).base + 1932#64)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, hrun])
    exact decodeState_err_drop_epoch_send_some_53c28_cl_placed_ofEnv hc x st0 st curSt curEpoch.recv
      n hn errBox cap1 ptr1 d.next d.prev d.ctr s0 _ _ R post hpost herr hfits1 hfits2 henv
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm, hsp])
      hs0A
      (by simp only [wp_norm, arm64_norm, htr])
      (by simp only [wp_norm, arm64_norm, hx19])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hx1])
      (by simp only [wp_norm, arm64_norm, hx1])
      (by
        dsimp only [decodeStateEpochErrTailFramePlaced, Reg.x1, Reg.x8, Reg.x19, Reg.x20,
          Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        try simp only [wp_norm, arm64_norm]
        sep_ac_rfl)

theorem decodeState_err_drop_epoch_54014_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 1) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : ∀ evs_d, FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d st) (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_d evs_p1, FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d st)) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_d evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d st))))
    (hpc : s.pc = decodeStatePlacedEntry + 2936#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx1 : s.readReg64 .x1 = errBox)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_drop_epoch_54014_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch n hn errBox s0 s P R post hpost herr
    hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hx1 hP

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudgetAux
