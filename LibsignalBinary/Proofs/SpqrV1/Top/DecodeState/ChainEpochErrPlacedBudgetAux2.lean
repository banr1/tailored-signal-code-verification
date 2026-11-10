/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErr
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainEpochPB` `DecodeError::from` Exits

Budget-threaded relocatable `[LibsignalPlacement]` proofs of the 6 `DecodeError::from` + `ChainEpochPB`
drop exit blocks (`+1872`, `+1884`, `+1896`, `+2872`, `+2892`, `+2912`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudgetAux2

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalTripleRatchet (KindNoHeap)
open CryptoVerification.LibsignalSpqrV1 (ChainEpochPB PqRatchetState spqrDecodeState)
open CryptoVerification.SpqrV1.ProtoRepr (chainEpochPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg
   decodeStateSavedAt protoPqRatchetStateAt scratch_320_fold_8 scratch_320_split_8
   scratch_336_fold_e8_40 scratch_336_split_e8_40 sp_sub_1392_aligned)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (SepWPp.call_decodeErrorFrom_placed_ofEnv decodeStatePanicPostPlaced
   decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
  (SepWPp.exists_left)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudgetAux
  (decodeStateEpochErrFramePlaced decodeStateEpochErrTailFramePlaced
   decodeState_err_drop_epoch_53c18_placed_ofEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `ChainEpochPB` `DecodeError::from` + Drop Error Exits (`0x53c08`, `0x53bec`, `0x53bf8`, `0x53c04`, `0x54028`, `0x54038`) -/

/-- Envelope-parameterized shared `DecodeError::from` call at `+1900` (4 instructions)
using `[x29 - 0xe8]` (`s0.sp - 328#64`), followed by `decodeState_err_drop_epoch_53c18_placed_ofEnv`. -/
theorem decodeState_err_from_epoch_53c08_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (w_e8 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 1900#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      ((s0.sp - 328#64) ↦₆₄ w_e8) ∗
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
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hfrom := hc.decodeErrorFrom
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc hfrom ⊢
  wp_steps_sync_pool (lsmpl.base 261)
  try simp only [State.setMem_setMem]
  have ha320 : (s0.sp - 328#64) + 8#64 = s0.sp - 320#64 := by bv_omega
  rw [← ha320]
  refine SepWPp.call_decodeErrorFrom_placed_ofEnv hfrom (s0.sp - 328#64) (s.readReg64 .x8) st
    (ret_pc := (blkPl_325).base + 1912#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29])
    (hw := hw)
    (hfits := hfits1)
    (hP := by sep_focus) ?_
  intro s1 w_e8' evs_fr hevs_fr hpc1 hrun1 hsp1 htr1 hcs1 _hx0_ne
  rw [ha320]
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  try simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
  try simp only [arm64_norm, wp_norm] at hx27_1 hx28_1 hx29_1 hvregs_1
  wp_steps_sync_pool ((blkPl_325).base + 1916#64)
  try simp only [State.setMem_setMem]
  refine SepWPp.fold (scratch_336_fold_e8_40 s0.sp w_e8') (by sep_focus) ?_
  exact decodeState_err_drop_epoch_53c18_placed_ofEnv hc x st0 (M.stepEvents evs_fr st) curSt
    curEpoch 0 (by decide) (s1.readReg64 .x0) s0 _ _ R post hpost herr
    (fun evs_d hd => hfits2 evs_fr evs_d hevs_fr hd)
    (fun evs_d evs_p1 hd hp1 => hfits3 evs_fr evs_d evs_p1 hevs_fr hd hp1)
    (fun evs_d evs_p1 evs_p2 evs_f hd hp1 hp2 hfree =>
      henv evs_fr evs_d evs_p1 evs_p2 evs_f hevs_fr hd hp1 hp2 hfree)
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [wp_norm, arm64_norm, hsp1])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm])
    (by
      dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced,
        Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
        Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_from_epoch_53c08_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (w_e8 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 1900#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      ((s0.sp - 328#64) ↦₆₄ w_e8) ∗
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
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_from_epoch_53c08_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch w_e8 s0 s P R post hpost herr hw
    hfits1 hfits2 hfits3 henv hpc hrun hsp hs0A htr hx19 hx29 hP

/-- Envelope-parameterized `ChainEpochPB` key overflow error (`+1872`, 3 instructions, placed). -/
theorem decodeState_err_epoch_key_overflow_53bec_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 1872#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  refine SepWPp.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWPp.exists_left; intro w_e8
  refine SepWPp.fold (scratch_320_split_8 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWPp.exists_left; intro _w_320
  wp_steps_sync_pool ((blkPl_325).base + 1900#64)
  try simp only [State.setMem_setMem]
  refine SepWPp.fold (scratch_320_fold_8 s0.sp (s.readReg64 .x1)) (by sep_focus) ?_
  exact decodeState_err_from_epoch_53c08_placed_ofEnv hc x st0 st curSt curEpoch w_e8 s0 _ _ R
    post hpost herr
    (by simp only [wp_norm, arm64_norm, hx21]; decide)
    hfits1 hfits2 hfits3 henv
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by
      dsimp only [Reg.x1, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
        Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_epoch_key_overflow_53bec_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 1872#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_epoch_key_overflow_53bec_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch s0 s P R post hpost herr
    hfits1 hfits2 hfits3 henv hpc hrun hsp hs0A htr hx19 hx21 hx29 hP

/-- Envelope-parameterized `ChainEpochPB` invalid wire type error (`+1884`, 3 instructions, placed). -/
theorem decodeState_err_epoch_invalid_wt_53bf8_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 1884#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  refine SepWPp.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWPp.exists_left; intro w_e8
  refine SepWPp.fold (scratch_320_split_8 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWPp.exists_left; intro _w_320
  wp_steps_sync_pool ((blkPl_325).base + 1900#64)
  try simp only [State.setMem_setMem]
  refine SepWPp.fold (scratch_320_fold_8 s0.sp (s.readReg64 .x0)) (by sep_focus) ?_
  exact decodeState_err_from_epoch_53c08_placed_ofEnv hc x st0 st curSt curEpoch w_e8 s0 _ _ R
    post hpost herr
    (by simp only [wp_norm, arm64_norm]; decide)
    hfits1 hfits2 hfits3 henv
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by
      dsimp only [Reg.x0, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
        Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_epoch_invalid_wt_53bf8_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 1884#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_epoch_invalid_wt_53bf8_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch s0 s P R post hpost herr
    hfits1 hfits2 hfits3 henv hpc hrun hsp hs0A htr hx19 hx29 hP

/-- Envelope-parameterized `ChainEpochPB` zero tag error (`+1896`, 1 instruction, placed). -/
theorem decodeState_err_epoch_zero_tag_53c04_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 1896#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  refine SepWPp.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWPp.exists_left; intro w_e8
  wp_steps_sync_pool ((blkPl_325).base + 1900#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_from_epoch_53c08_placed_ofEnv hc x st0 st curSt curEpoch w_e8 s0 _ _ R
    post hpost herr
    (by simp only [wp_norm, arm64_norm, hx21]; decide)
    hfits1 hfits2 hfits3 henv
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by
      dsimp only [Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
        Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_epoch_zero_tag_53c04_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 1896#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_epoch_zero_tag_53c04_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch s0 s P R post hpost herr
    hfits1 hfits2 hfits3 henv hpc hrun hsp hs0A htr hx19 hx21 hx29 hP

/-- Envelope-parameterized `ChainEpochPB` truncated length error (`+2956`, 2 instructions, placed). -/
theorem decodeState_err_epoch_truncated_54028_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 2956#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  refine SepWPp.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWPp.exists_left; intro w_e8
  wp_steps_sync_pool ((blkPl_325).base + 1900#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_from_epoch_53c08_placed_ofEnv hc x st0 st curSt curEpoch w_e8 s0 _ _ R
    post hpost herr
    (by simp only [wp_norm, arm64_norm]; decide)
    hfits1 hfits2 hfits3 henv
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by
      dsimp only [Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
        Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_epoch_truncated_54028_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 2956#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_epoch_truncated_54028_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch s0 s P R post hpost herr
    hfits1 hfits2 hfits3 henv hpc hrun hsp hs0A htr hx19 hx29 hP

/-- Envelope-parameterized `ChainEpochPB` corrupt length limit error (`+2972`, 2 instructions, placed). -/
theorem decodeState_err_epoch_corrupt_54038_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 2972#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced] at hpc ⊢
  refine SepWPp.fold (scratch_336_split_e8_40 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWPp.exists_left; intro w_e8
  wp_steps_sync_pool ((blkPl_325).base + 1900#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_from_epoch_53c08_placed_ofEnv hc x st0 st curSt curEpoch w_e8 s0 _ _ R
    post hpost herr
    (by simp only [wp_norm, arm64_norm, hx21]; decide)
    hfits1 hfits2 hfits3 henv
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by
      dsimp only [Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
        Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_epoch_corrupt_54038_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 2972#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_epoch_corrupt_54038_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch s0 s P R post hpost herr
    hfits1 hfits2 hfits3 henv hpc hrun hsp hs0A htr hx19 hx21 hx29 hP

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudgetAux2
