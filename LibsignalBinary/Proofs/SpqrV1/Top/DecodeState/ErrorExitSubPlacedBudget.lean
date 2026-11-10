/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Outer Loop & `ChainPB` Error Exit Paths for `spqr::decode_state` (Block `325`)

Re-exports `ErrorExitSubPlacedBudgetAux` and proves the remaining budget-threaded relocatable
`ChainPB` error-exit paths (`+1596`, `+1776..+1824`, `+2092..+2108`, `+2660..+2868`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalTripleRatchet (KindNoHeap decodeErrorAtStackLen)
open CryptoVerification.LibsignalSpqrV1 (PqRatchetState spqrDecodeState)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg
   decodeStateSavedAt protoPqRatchetStateAt sp_sub_1392_aligned)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget
  (bv_sub_688_add_8 decodeStateErrFramePlaced scratch_680_fold_1_1 scratch_680_fold_8
   scratch_680_split_1_1 scratch_680_split_8)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (SepWPp.call_decodeErrorFrom_placed_ofEnv decodeStatePanicPostPlaced
   decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv
   decodeState_err_push_53cdc_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
  (SepWPp.exists_left decodeState_err_push_53cbc_placed_ofEnv
   decodeState_err_push_53fa0_placed_ofEnv)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
  (decodeStateErrFramePlaced
   decodeStateIterEnv_of_decodeErrorFrom
   fitsEnv_decodeErrorFrom_of_loop fitsEnv_decodeErrorPush_of_loop
   decodeStateEnv_of_loop_from_free decodeStateEnv_of_loop_push2_free
   decodeStateEnv_of_loop_from_push_free decodeStateEnv_of_loop_from_push2_free
   decodeState_err_push_53bc0_placed_ofEnv decodeState_err_push_53bc0_placed
   decodeState_err_53b20_placed_ofEnv decodeState_err_53b20_placed
   decodeState_err_from_53b14_placed_ofEnv decodeState_err_from_53b14_placed
   decodeState_err_53af8_placed_ofEnv decodeState_err_53af8_placed
   decodeState_err_53b04_placed_ofEnv decodeState_err_53b04_placed
   decodeState_err_53b10_placed_ofEnv decodeState_err_53b10_placed
   decodeState_err_push_53cbc_placed_ofEnv decodeState_err_push_53cbc_placed
   decodeState_err_push_53c9c_placed_ofEnv decodeState_err_push_53c9c_placed
   decodeState_err_push_53edc_placed_ofEnv decodeState_err_push_53edc_placed
   decodeState_err_53ec4_placed_ofEnv decodeState_err_53ec4_placed
   decodeState_err_push_53fa0_placed_ofEnv decodeState_err_push_53fa0_placed
   decodeState_err_push_53f8c_placed_ofEnv decodeState_err_push_53f8c_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem sepWPp_seg_325_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {mid ret pc0 : BitVec 64} {s : State} {Pre : SepProp}
    {post Qp : State → SepProp → Prop}
    (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hseg : ∀ m_strip : Memory,
      (s.setMem m_strip).pc = pc0 →
      (s.setMem m_strip).status = .Running →
      SepWP ((blkPC_325).rebase (blkPl_325).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
        mid (s.setMem m_strip) Pre (fun sm' Pm =>
          ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            SepWPp ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
              ret (sm'.setMem m_real) Pm post Qp)) :
    SepWPp ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext)) ret s Pre post Qp :=
  LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWPp_seg_ls_vm
    (Q := (blkPC_325).rebase (blkPl_325).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
    blkLib_eq_325 (mid := mid) (hseg := fun m_strip => hseg m_strip hpc hrun)

meta section
macro "wp_steps_sync_325 " hpc:ident hrun:ident mid:term : tactic =>
  `(tactic| (
    apply sepWPp_seg_325_vm $hpc $hrun (mid := $mid)
    intro _m_strip _hpc_strip _hrun_strip
    wp_steps
    refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine ProofLib.SepWPp.transport_budgetPool
      (_hnsp.toVmPreserved (by first | rfl | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
  ))
end

/-! ## 5. Remaining `ChainPB` Error Exits (`0x53f00..0x53fd0`, `0x53ad8`, `0x53b8c..0x53bbc`, `0x53cc8..0x53cd8`) -/

/-- Envelope-parameterized error push at `0x53f18..0x53f2c` (`+2684..+2704`, 6 instructions)
for `Chain::version`: stores `x8` (`errBox`) at `[sp + 0x2c0]` and branches to `0x53fa0`. -/
theorem decodeState_err_push_53f18_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2684#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x8) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_325 hpc hrun ((blkPl_325).base + 2820#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53fa0_placed_ofEnv hc x st0 st curSt (s.readReg64 .x8) n
    s0 _ _ R post hpost herr hn hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_push_53f18_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2684#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x8) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_push_53f18_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 n s0 s P R post hpost herr hn hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized wire-type mismatch error on `Chain::version` at
`0x53f00..0x53f14` (`+2660..+2680`, 6 instructions). -/
theorem decodeState_err_53f00_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
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
    (hpc : s.pc = decodeStatePlacedEntry + 2660#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hfrom := hc.decodeErrorFrom
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hfrom ⊢
  refine SepWPp.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWPp.exists_left; intro b1
  apply SepWPp.exists_left; intro b0
  wp_steps_sync_325 hpc hrun (lsmpl.base 261)
  try simp only [State.setMem_setMem]
  refine SepWPp.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  refine SepWPp.call_decodeErrorFrom_placed_ofEnv hfrom (s0.sp - 688#64) 0x8000000000000006#64 st
    (ret_pc := (blkPl_325).base + 2680#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hsp])
    (hw := by decide)
    (hfits := hfits1)
    (hP := by simp only [bv_sub_688_add_8, hx21]; sep_focus) ?_
  intro s1 v_k evs_fr hevs_fr hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  try simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
  try simp only [arm64_norm, wp_norm] at hx27_1 hx28_1 hx29_1 hvregs_1
  rw [bv_sub_688_add_8 s0.sp]
  wp_steps_sync_325 hpc1 hrun1 ((blkPl_325).base + 2684#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53f18_placed_ofEnv hc x st0 (M.stepEvents evs_fr st) curSt v_k 0
    s0 _ _ R post hpost herr (by decide)
    (hfits2 evs_fr hevs_fr)
    (fun evs_p1 hp1 => hfits3 evs_fr evs_p1 hevs_fr hp1)
    (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree => henv evs_fr evs_p1 evs_p2 evs_f hevs_fr hp1 hp2 hfree)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [wp_norm, arm64_norm, hsp1])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_53f00_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
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
    (hpc : s.pc = decodeStatePlacedEntry + 2660#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_53f00_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 hfits3 henv hpc hrun hsp hs0A htr hx19 hx21 hP

/-- Envelope-parameterized error push at `0x53f68..0x53f88` (`+2764..+2796`, 9 instructions)
for `Chain::starting_epoch`: stores `x8` (`errBox`) at `[sp + 0x2c0]` and branches to `0x53cbc`. -/
theorem decodeState_err_push_53f68_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2764#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x8) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_325 hpc hrun ((blkPl_325).base + 2080#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53cbc_placed_ofEnv hc x st0 st curSt (s.readReg64 .x8) n
    s0 _ _ R post hpost herr hn hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_push_53f68_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2764#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x8) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_push_53f68_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 n s0 s P R post hpost herr hn hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized wire-type mismatch error on `Chain::starting_epoch` at
`0x53f50..0x53f64` (`+2740..+2760`, 6 instructions). -/
theorem decodeState_err_53f50_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
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
    (hpc : s.pc = decodeStatePlacedEntry + 2740#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hfrom := hc.decodeErrorFrom
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hfrom ⊢
  refine SepWPp.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWPp.exists_left; intro b1
  apply SepWPp.exists_left; intro b0
  wp_steps_sync_325 hpc hrun (lsmpl.base 261)
  try simp only [State.setMem_setMem]
  refine SepWPp.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  refine SepWPp.call_decodeErrorFrom_placed_ofEnv hfrom (s0.sp - 688#64) 0x8000000000000006#64 st
    (ret_pc := (blkPl_325).base + 2760#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hsp])
    (hw := by decide)
    (hfits := hfits1)
    (hP := by simp only [bv_sub_688_add_8, hx21]; sep_focus) ?_
  intro s1 v_k evs_fr hevs_fr hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  try simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
  try simp only [arm64_norm, wp_norm] at hx27_1 hx28_1 hx29_1 hvregs_1
  rw [bv_sub_688_add_8 s0.sp]
  wp_steps_sync_325 hpc1 hrun1 ((blkPl_325).base + 2764#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53f68_placed_ofEnv hc x st0 (M.stepEvents evs_fr st) curSt v_k 0
    s0 _ _ R post hpost herr (by decide)
    (hfits2 evs_fr hevs_fr)
    (fun evs_p1 hp1 => hfits3 evs_fr evs_p1 hevs_fr hp1)
    (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree => henv evs_fr evs_p1 evs_p2 evs_f hevs_fr hp1 hp2 hfree)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [wp_norm, arm64_norm, hsp1])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_53f50_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
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
    (hpc : s.pc = decodeStatePlacedEntry + 2740#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_53f50_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 hfits3 henv hpc hrun hsp hs0A htr hx19 hx21 hP

/-- Envelope-parameterized error push at `0x53fb0..0x53fd0` (`+2836..+2868`, 9 instructions)
for `Chain::params`: stores `x0` (`errBox`) at `[sp + 0x2c0]` and branches to `0x53cbc`. -/
theorem decodeState_err_push_53fb0_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2836#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x0) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_325 hpc hrun ((blkPl_325).base + 2080#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53cbc_placed_ofEnv hc x st0 st curSt (s.readReg64 .x0) n
    s0 _ _ R post hpost herr hn hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_push_53fb0_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2836#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x0) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_push_53fb0_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 n s0 s P R post hpost herr hn hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized error conversion at `0x53cd0..0x53cd8` (`+2100..+2108`, 3 instructions)
for `Chain`: sets `x0 = sp + 0x2c0`, calls `DecodeError::from`, moves `x0` into `x1`,
and falls through to `0x53cdc` (`decodeState_err_push_53cdc_placed_ofEnv`). -/
theorem decodeState_err_from_53cd0_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hw : KindNoHeap w0)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2100#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hfrom := hc.decodeErrorFrom
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hfrom ⊢
  wp_steps_sync_325 hpc hrun (lsmpl.base 261)
  try simp only [State.setMem_setMem]
  refine SepWPp.call_decodeErrorFrom_placed_ofEnv hfrom (s0.sp - 688#64) w0 st
    (ret_pc := (blkPl_325).base + 2108#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hsp])
    (hw := hw)
    (hfits := hfits1)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k evs_fr hevs_fr hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  try simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
  try simp only [arm64_norm, wp_norm] at hx27_1 hx28_1 hx29_1 hvregs_1
  rw [bv_sub_688_add_8 s0.sp]
  wp_steps_sync_325 hpc1 hrun1 ((blkPl_325).base + 2112#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53cdc_placed_ofEnv hc x st0 (M.stepEvents evs_fr st) curSt v_k 0
    s0 _ _ R post hpost herr (by decide)
    (hfits2 evs_fr hevs_fr)
    (fun evs_p evs_f hp hfree => henv evs_fr evs_p evs_f hevs_fr hp hfree)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [wp_norm, arm64_norm, hsp1])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *])
    (by
      dsimp only [Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
        Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_from_53cd0_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hw : KindNoHeap w0)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2100#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_from_53cd0_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hw hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized error conversion at `0x53ccc` (`+2096`, 1 instruction):
stores `x8` at `[sp + 0x2c0]` (`s0.sp - 688#64`) and falls through to `0x53cd0`. -/
theorem decodeState_err_from_53ccc_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2096#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_325 hpc hrun ((blkPl_325).base + 2100#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_from_53cd0_placed_ofEnv hc x st0 st curSt (s.readReg64 .x8)
    s0 _ _ R post hpost herr hw hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_from_53ccc_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2096#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_from_53ccc_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hw hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized `BufferUnderflow` (`len > rem`) on `Chain` at `0x53cc8` (`+2092`, 1 instruction). -/
theorem decodeState_err_53cc8_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2092#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_325 hpc hrun ((blkPl_325).base + 2096#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_from_53ccc_placed_ofEnv hc x st0 st curSt w0
    s0 _ _ R post hpost herr
    (by simp only [wp_norm, arm64_norm]; decide)
    hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_53cc8_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2092#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_53cc8_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized `BufferUnderflow` (`rem < limit`) on `Chain` at
`0x53ad8..0x53adc` (`+1596..+1600`, 2 instructions). -/
theorem decodeState_err_53ad8_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1596#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_325 hpc hrun ((blkPl_325).base + 2096#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_from_53ccc_placed_ofEnv hc x st0 st curSt w0
    s0 _ _ R post hpost herr
    (by simp only [wp_norm, arm64_norm, hx21]; decide)
    hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_53ad8_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1596#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_53ad8_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hx21 hP

/-- Envelope-parameterized `InvalidKeyValue` (`key >= 2^32`) in `Chain` `decode_key` at
`0x53b8c..0x53b94` (`+1776..+1784`, 3 instructions). -/
theorem decodeState_err_53b8c_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1776#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  refine SepWPp.fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWPp.exists_left; intro w_tmp
  wp_steps_sync_325 hpc hrun ((blkPl_325).base + 2096#64)
  try simp only [State.setMem_setMem]
  refine SepWPp.fold (scratch_680_fold_8 s0.sp _) (by sep_focus) ?_
  exact decodeState_err_from_53ccc_placed_ofEnv hc x st0 st curSt w0
    s0 _ _ R post hpost herr
    (by simp only [wp_norm, arm64_norm, hx21]; decide)
    hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x1, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_53b8c_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1776#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_53b8c_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hx21 hP

/-- Envelope-parameterized `InvalidWireType` (`(key & 7) >= 6`) in `Chain` `decode_key` at
`0x53b98..0x53ba0` (`+1788..+1796`, 3 instructions). -/
theorem decodeState_err_53b98_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1788#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  refine SepWPp.fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWPp.exists_left; intro w_tmp
  wp_steps_sync_325 hpc hrun ((blkPl_325).base + 2096#64)
  try simp only [State.setMem_setMem]
  refine SepWPp.fold (scratch_680_fold_8 s0.sp _) (by sep_focus) ?_
  exact decodeState_err_from_53ccc_placed_ofEnv hc x st0 st curSt w0
    s0 _ _ R post hpost herr
    (by simp only [wp_norm, arm64_norm]; decide)
    hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_53b98_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1788#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_53b98_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized `InvalidTag` (`tag == 0`) in `Chain` `decode_key` at
`0x53ba4..0x53ba8` (`+1800..+1804`, 2 instructions). -/
theorem decodeState_err_53ba4_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1800#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_325 hpc hrun ((blkPl_325).base + 2096#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_from_53ccc_placed_ofEnv hc x st0 st curSt w0
    s0 _ _ R post hpost herr
    (by simp only [wp_norm, arm64_norm, hx21]; decide)
    hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_53ba4_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1800#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_53ba4_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hx21 hP

/-- Envelope-parameterized wire-type mismatch error (`wt != LengthDelimited`) on
`PqRatchetState::chain` at `0x53bac..0x53bbc` (`+1808..+1824`, 5 instructions). -/
theorem decodeState_err_53bac_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1808#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  refine SepWPp.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWPp.exists_left; intro b1
  apply SepWPp.exists_left; intro b0
  wp_steps_sync_325 hpc hrun ((blkPl_325).base + 2100#64)
  try simp only [State.setMem_setMem]
  refine SepWPp.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  have hw21 : KindNoHeap (s.readReg64 .x21) := by rw [hx21]; decide
  exact decodeState_err_from_53cd0_placed_ofEnv hc x st0 st curSt (s.readReg64 .x21)
    s0 _ _ R post hpost herr hw21 hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_53bac_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1808#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := decodeState_err_53bac_placed_ofEnv (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 henv hpc hrun hsp hs0A htr hx19 hx21 hP

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudget
