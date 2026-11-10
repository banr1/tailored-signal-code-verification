/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErr
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Budget Code-Loaded `ChainEpochPB` Error Drop Blocks

Budget-threaded code-loaded `[LibsignalPlacement]` proofs of the `DecodeError::push("Chain", ...)`
exits (`+2708`, `+2956`, `+2972`) and re-exports of all `ChainEpochPB` error-drop blocks.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen)
open CryptoVerification.LibsignalSpqrV1 (ChainEpochPB PqRatchetState spqrDecodeState)
open CryptoVerification.SpqrV1.ProtoRepr (chainEpochPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg
   decodeStateSavedAt protoPqRatchetStateAt scratch_320_fold_1_1 scratch_320_split_1_1
   scratch_336_fold_e8_40 scratch_336_split_e8_40 sp_sub_1392_aligned)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget
  (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitClPlacedBudget
  (SepWPpIPlaced.call_decodeErrorFrom_cl_ofEnv SepWPpIPlaced.call_decodeErrorPush_cl_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubClPlacedBudgetAux
  (decodeState_err_push_53c9c_cl_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudgetAux
  (decodeStateEpochErrFramePlaced decodeStateEpochErrTailFramePlaced
   decodeState_err_drop_epoch_54014_cl_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced SepWPpIPlaced.of_sepWP)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudgetAux
  (decodeStateEpochErrTailFramePlaced decodeStateEpochErrFramePlaced
   fitsEnv_epochDrop_push1_of_loop fitsEnv_epochDrop_push2_of_loop
   decodeStateEnv_of_loop_epochDrop_push2_free)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudgetAux
  (decodeStateEnv_of_loop_from_epochDrop_push2_free
   decodeStateEnv_of_loop_push_epochDrop_push2_free
   decodeState_err_drop_epoch_recv_53c5c_cl_placed_ofEnv
   decodeState_err_drop_epoch_recv_53c5c_cl_placed
   decodeState_err_drop_epoch_send_some_53c28_cl_placed_ofEnv)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudgetAux
  (decodeState_err_drop_epoch_send_some_53c28_cl_placed
   decodeState_err_drop_epoch_53c18_cl_placed_ofEnv
   decodeState_err_drop_epoch_53c18_cl_placed
   decodeState_err_drop_epoch_54014_cl_placed_ofEnv
   decodeState_err_drop_epoch_54014_cl_placed)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudgetAux2
  (decodeState_err_from_epoch_53c08_cl_placed_ofEnv
   decodeState_err_from_epoch_53c08_cl_placed
   decodeState_err_epoch_key_overflow_53bec_cl_placed_ofEnv
   decodeState_err_epoch_key_overflow_53bec_cl_placed)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudgetAux2
  (decodeState_err_epoch_invalid_wt_53bf8_cl_placed_ofEnv
   decodeState_err_epoch_invalid_wt_53bf8_cl_placed
   decodeState_err_epoch_zero_tag_53c04_cl_placed_ofEnv
   decodeState_err_epoch_zero_tag_53c04_cl_placed)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudgetAux2
  (decodeState_err_epoch_truncated_54028_cl_placed_ofEnv
   decodeState_err_epoch_truncated_54028_cl_placed
   decodeState_err_epoch_corrupt_54038_cl_placed_ofEnv
   decodeState_err_epoch_corrupt_54038_cl_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `ChainEpochPB` Field-Merge Error Push (`0x54000`, `0x53fd4`, `0x53fec`) & `ChainPB::epoch` Wire-Type Error (`0x53f30`) -/

/-- Envelope-parameterized shared `DecodeError::push` call (`+2916`, 5 instructions) for
`ChainEpochPB` field merge errors (`send` / `recv`), continuing to
`decodeState_err_drop_epoch_54014_cl_placed_ofEnv`. -/
theorem decodeState_err_push_epoch_54000_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 2) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p0 evs_d, DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 st)) (DecodeErrorPushEnv (n + 1)))
    (hfits3 : ∀ evs_p0 evs_d evs_p1,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))
        (DecodeErrorPushEnv (n + 2)))
    (henv : ∀ evs_p0 evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 2916#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      ((s0.sp - 328#64) ↦₆₄ errBox) ∗
      memRegion (s0.sp - 320#64) 40 ∗
      memRegion (s0.sp - 336#64) 8 ∗
      memRegion (s0.sp - 280#64) 184 ∗
      chainEpochPBAt A.repAlloc (s0.sp - 688#64) curEpoch ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 576#64) 240 ∗
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
  refine SepWPpIPlaced.of_sepWP (mid := (lsmpl.base 257)) ?_
  wp_steps_sync_pool (lsmpl.base 257)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPpIPlaced.call_decodeErrorPush_cl_ofEnv hpush (s0.sp - 328#64) errBox n st
    (ret_pc := (blkPl_325).base + 2932#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29])
    (hn := by omega)
    (hfits := hfits1)
    (hP := by sep_focus) ?_
  intro s1 evs_p0 hevs_p0 hpc1 hrun1 hsp1 htr1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  try simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
  try simp only [arm64_norm, wp_norm] at hx27_1 hx28_1 hx29_1 hvregs_1
  refine SepWPpIPlaced.of_sepWP (mid := ((blkPl_325).base + 2936#64)) ?_
  wp_steps_sync_pool ((blkPl_325).base + 2936#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (scratch_336_fold_e8_40 s0.sp errBox) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  exact decodeState_err_drop_epoch_54014_cl_placed_ofEnv hc x st0 (M.stepEvents evs_p0 st) curSt
    curEpoch (n + 1) (by omega) errBox s0 _ _ R post hpost herr
    (fun evs_d hd => hfits2 evs_p0 evs_d hevs_p0 hd)
    (fun evs_d evs_p1 hd hp1 => hfits3 evs_p0 evs_d evs_p1 hevs_p0 hd hp1)
    (fun evs_d evs_p1 evs_p2 evs_f hd hp1 hp2 hfree =>
      henv evs_p0 evs_d evs_p1 evs_p2 evs_f hevs_p0 hd hp1 hp2 hfree)
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [wp_norm, arm64_norm, hsp1])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm])
    (by
      dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced,
        Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
        Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_push_epoch_54000_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 2) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p0 evs_d, DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 st)) (DecodeErrorPushEnv (n + 1)))
    (hfits3 : ∀ evs_p0 evs_d evs_p1,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))
        (DecodeErrorPushEnv (n + 2)))
    (henv : ∀ evs_p0 evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 2916#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      ((s0.sp - 328#64) ↦₆₄ errBox) ∗
      memRegion (s0.sp - 320#64) 40 ∗
      memRegion (s0.sp - 336#64) 8 ∗
      memRegion (s0.sp - 280#64) 184 ∗
      chainEpochPBAt A.repAlloc (s0.sp - 688#64) curEpoch ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_push_epoch_54000_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch n hn errBox s0 s P R post hpost herr
    hfits1 hfits2 hfits3 henv hpc hrun hsp hs0A htr hx19 hx29 hP

/-- Envelope-parameterized `ChainEpochPB::send` (`EpochDirection::merge`) error exit
(`+2872`, 6 instructions, placed). -/
theorem decodeState_err_epoch_send_merge_53fd4_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 2) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p0 evs_d, DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 st)) (DecodeErrorPushEnv (n + 1)))
    (hfits3 : ∀ evs_p0 evs_d evs_p1,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))
        (DecodeErrorPushEnv (n + 2)))
    (henv : ∀ evs_p0 evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 2872#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = errBox)
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
  refine SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2916#64) ?_
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro _w_e8
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_325).rebase (blkPl_325).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
    blkLib_eq_325 (mid := (blkPl_325).base + 2916#64)
  intro _m_strip
  have _hpc_s : (s.setMem _m_strip).pc = (blkPl_325).base + 2872#64 := by simp [hpc]
  have _hrun_s : (s.setMem _m_strip).status = .Running := by simp [hrun]
  wp_steps
  refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun]) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  exact decodeState_err_push_epoch_54000_cl_placed_ofEnv hc x st0 st curSt curEpoch n hn errBox
    s0 _ _ R post hpost herr hfits1 hfits2 hfits3 henv
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by
      dsimp only [Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
        Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_epoch_send_merge_53fd4_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 2) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p0 evs_d, DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 st)) (DecodeErrorPushEnv (n + 1)))
    (hfits3 : ∀ evs_p0 evs_d evs_p1,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))
        (DecodeErrorPushEnv (n + 2)))
    (henv : ∀ evs_p0 evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 2872#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = errBox)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_epoch_send_merge_53fd4_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch n hn errBox s0 s P R post hpost herr
    hfits1 hfits2 hfits3 henv hpc hrun hsp hs0A htr hx19 hx29 hx0 hP

/-- Envelope-parameterized `ChainEpochPB::recv` (`EpochDirection::merge`) error exit
(`+2896`, 5 instructions, placed). -/
theorem decodeState_err_epoch_recv_merge_53fec_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 2) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p0 evs_d, DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 st)) (DecodeErrorPushEnv (n + 1)))
    (hfits3 : ∀ evs_p0 evs_d evs_p1,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))
        (DecodeErrorPushEnv (n + 2)))
    (henv : ∀ evs_p0 evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 2896#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = errBox)
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
  refine SepWPpIPlaced.of_sepWP (mid := ((blkPl_325).base + 2916#64)) ?_
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro _w_e8
  wp_steps_sync_pool ((blkPl_325).base + 2916#64)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  exact decodeState_err_push_epoch_54000_cl_placed_ofEnv hc x st0 st curSt curEpoch n hn errBox
    s0 _ _ R post hpost herr hfits1 hfits2 hfits3 henv
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by
      dsimp only [Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
        Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_epoch_recv_merge_53fec_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (n : Nat) (hn : n < 2 ^ 32 - 2) (errBox : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p0 evs_d, DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 st)) (DecodeErrorPushEnv (n + 1)))
    (hfits3 : ∀ evs_p0 evs_d evs_p1,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))
        (DecodeErrorPushEnv (n + 2)))
    (henv : ∀ evs_p0 evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 2896#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = errBox)
    (hP : P =
      decodeErrorAtStackLen A.repAlloc errBox n ∗
      decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_epoch_recv_merge_53fec_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch n hn errBox s0 s P R post hpost herr
    hfits1 hfits2 hfits3 henv hpc hrun hsp hs0A htr hx19 hx29 hx0 hP

/-- Envelope-parameterized `ChainPB::epoch` tag-3 wire-type mismatch (`x0 ≠ 2`, before
`ChainEpochPB` initialization, `+2708`, 8 instructions, placed). -/
theorem decodeState_err_chain_epoch_wt_53f30_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_p1, DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_fr st))))
    (hpc : s.pc = decodeStatePlacedEntry + 2708#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hfrom := hc.decodeErrorFrom
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry,
    decodeStateErrFramePlaced] at hpc hfrom ⊢
  refine SepWPpIPlaced.of_sepWP (mid := (lsmpl.base 261)) ?_
  refine SepWP.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro _w_e8
  refine SepWP.fold (scratch_320_split_1_1 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro _b1
  apply ProofLib.SepWP.exists_left; intro _b0
  wp_steps_sync_pool (lsmpl.base 261)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (scratch_320_fold_1_1 s0.sp (BitVec.zeroExtend 8 (s.readReg64 .x0)) 2#8)
    (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  have ha320 : (s0.sp - 328#64) + 8#64 = s0.sp - 320#64 := by bv_omega
  rw [← ha320]
  refine SepWPpIPlaced.call_decodeErrorFrom_cl_ofEnv hfrom (s0.sp - 328#64) 0x8000000000000006#64 st
    (F := memRegion (s0.sp - 336#64) 8 ∗
      memRegion (s0.sp - 280#64) 184 ∗
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19))
    (ret_pc := (blkPl_325).base + 2732#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29])
    (hw := by decide)
    (hfits := hfits1)
    (hP := by
      dsimp only [Reg.x21] at hx21
      simp only [wp_norm, arm64_norm, hx21]
      sep_ac_rfl) ?_
  intro s1 w_e8' evs_fr hevs_fr hpc1 hrun1 hsp1 htr1 hcs1 _hx0_ne
  rw [ha320]
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  try simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
  try simp only [arm64_norm, wp_norm] at hx27_1 hx28_1 hx29_1 hvregs_1
  refine SepWPpIPlaced.of_sepWP (mid := ((blkPl_325).base + 2048#64)) ?_
  wp_steps_sync_pool ((blkPl_325).base + 2048#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (scratch_336_fold_e8_40 s0.sp w_e8') (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  exact decodeState_err_push_53c9c_cl_placed_ofEnv hc x st0 (M.stepEvents evs_fr st) curSt w0 0
    s0 _ _ R post hpost herr (by decide)
    (hfits2 evs_fr hevs_fr)
    (fun evs_p1 hp1 => hfits3 evs_fr evs_p1 hevs_fr hp1)
    (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree => henv evs_fr evs_p1 evs_p2 evs_f hevs_fr hp1 hp2 hfree)
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [wp_norm, arm64_norm, hsp1])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_chain_epoch_wt_53f30_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_p1, DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_fr st))))
    (hpc : s.pc = decodeStatePlacedEntry + 2708#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_chain_epoch_wt_53f30_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr
    hfits1 hfits2 hfits3 henv hpc hrun hsp hs0A htr hx19 hx21 hx29 hP

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudget
