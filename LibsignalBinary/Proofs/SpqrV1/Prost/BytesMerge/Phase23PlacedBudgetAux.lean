/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23Placed
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.Basic
import ProofLib.SepLogic.WP

/-!
# `prost::encoding::bytes::merge [local#3]` (Block `290`): Budget-Threaded Epilogues and Phase 3

Relocatable `[LibsignalPlacement]` verification of the error/drop epilogues (`+0x074`, `+0x07c`,
`+0x254`) and Phase 3 (`+0x210..+0x280`, `+0x29c..+0x2c4`) on Block `290` under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23PlacedBudgetAux

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
  (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (vmPreserved_setPC vmPreserved_setPState vmPreserved_writeReg64 vmPreserved_writeReg32)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveCall reserveCap doReserveEvents DoReserveEnv fitsEnv_doReserve_iff
   doReserveSpec doReserveSpecWithStack framelessMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
  (bytesDropEvents bytesVtableDropSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore bytesMergeRawSpecGen doReserveClearEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
  (MergePostGen MergePanicGen bmMemcpySpecGen bytesVtableDropSpecBMGen)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux
  (mergeBytes_length_sum doReserveEvents_eq_clear doReserveClearEvents_of_le
   bmMemcpy_placed_of_framelessBudget)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded lsmpl
   blkPC_290 blkPl_290 blkLib_eq_290 withLsCl)
open CryptoVerification.RustHeap
  (allocHookStack vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap bytesBoxU8Buf bytesData bytesPlacedDropFnAddr
   bytesPlacedVtable bytesPtr bytesVtableDropStack decodeErrorAtStackLen
   decodeErrorHookStack doReserveStack)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost bytesMergeStack decodeVarintSliceStack
   bytesMergeCapOk_after_reserve bytesMergeCapOk_mono bytesMergeCapOk_reserveCap_bound
   SepWP.drop_left SepWP.with_vtableSlot_placed SepWPp.bm_call_frame_lscl
   SepWPp.bm_of_sepWP_lscl bmSliceStack bmTotalStack bm_HighCalleeSaved
   bm_vecU8At_eq_header_sep_buf bytesBoxU8Buf_nonempty fold_bytesBoxU8Buf_nonempty
   fold_stackAt_bytesMerge fold_vecU8At_clear fold_vecU8At_copied savedRegsStack
   sliceCursorAfter spAligned_sub_224 stackAt_slice_to_decodeError
   stackAt_slice_to_doReserve stackAt_slice_to_vtableDrop
   vecU8At_entails_exists vecU8At_nil_eq)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev MergePost {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  MergePostGen decodeErrorHookStack true A lim x st s0 R sf P_f

abbrev MergePanic {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  MergePanicGen decodeErrorHookStack true A lim x st s0 R sf P_f

theorem bytesVtableDropSpecBM_of_spec [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ptr : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    (h : subroutine_ok prog entry
      (withLsCl lsmpl (bytesVtableDropSpec M A lim ptr bs off))) :
    subroutine_ok prog entry
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim allocHookStack ptr bs off)) := by
  refine subroutine_ok_outcome_intro fun st R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨
      (withLsCl lsmpl (bytesVtableDropSpec M A lim ptr bs off)).pre st s0 ∗ R := by
    dsimp only [withLsCl, CryptoVerification.withLsCodeLoaded,
      bytesVtableDropSpec, bytesVtableDropSpecBMGen, bytesVtableDropStack] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨h1, h2, h3, h4, hlr⟩, hrest⟩
    exact ⟨by simp only [h1, h2, h3, h4, hlr, and_self], hrest⟩
  refine h.mono_outcome st R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex | hoom)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl, CryptoVerification.withLsCodeLoaded,
      bytesVtableDropSpec, bytesVtableDropSpecBMGen, bytesVtableDropStack] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1.1, hpost.2.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-! ## 1. Epilogues on Block `290` (`[LibsignalPlacement]`) -/

/-- Direct error epilogue from `(blkPl_290).base + 0x07c` (`+124`) to `RET` at `+0x090` (`+144`). -/
theorem epilogue3_err_0x07c_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    (hmerge : mergeBytes x.wt x.bs = none)
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ st_cur = M.stepEvents evs st)
    (hpc : s.pc = (blkPl_290).base + 124#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 ≠ 0#64)
    (hhigh : bm_HighCalleeSaved s0 s) :
    SepWPp ((blkPC_290).rebase (blkPl_290).base H) (s0.readReg64 .lr) s
      (decodeErrorAtStackLen A.repAlloc (s.readReg64 .x0) 0 ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A lim x st s0 R) (MergePanic A lim x st s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh
  rcases hevs with ⟨evs, hevs_env, rfl⟩
  dsimp only [savedRegsStack] at hpc ⊢
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMerge s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self]⟩
  intro hmf
  dsimp only [Reg.x0, bytesMergeStack,
    decodeVarintSliceStack] at hx0 hmf ⊢
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64,
    RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    Reg.x0, hx0, htrace, ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [hevs_env, pure_true, emp_sepConj]
  convert hmf using 2
  sep_ac_rfl

/-- Error epilogue from `(blkPl_290).base + 0x074` (`+116`): sets `x0 := sp + 8`, calls
`DecodeError::from` at `lsmpl.base 261`, then restores callee-saved registers and returns. -/
theorem epilogue3_decodeErrorFrom_0x074_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdef : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {R : SepProp} {w : BitVec 64}
    (hw : KindNoHeap w)
    (hmerge : mergeBytes x.wt x.bs = none)
    (hfits : FitsEnv M lim st (BytesMergeEnv x))
    (hpc : s.pc = (blkPl_290).base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_290).rebase (blkPl_290).base H) (s0.readReg64 .lr) s
      (((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool lim st s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A lim x st s0 R) (MergePanic A lim x st s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hfits_de : FitsEnv M lim st DecodeErrorFromEnv := by
    refine hfits.mono fun evs he => ?_
    simpa only [BytesMergeEnv, bytesMergeEventsCore, hmerge, DecodeErrorFromEnv] using he
  dsimp only [savedRegsStack] at hpc hdef ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 261)
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl_call hro_call
  refine SepWPp.bm_call_frame_lscl (x := (s0.sp - 216#64, w, st))
    (T := ((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
      A.pool lim st _ ∗ stackAt (s0.sp - 224#64) decodeErrorHookStack)
    hdef hcl_call hro_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeErrorFromBudgetSpec, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [KindNoHeap, wp_norm, arm64_norm, hsp, hw, hfits_de, and_self])
    (by rw [stackAt_slice_to_decodeError s0.sp]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm; dsimp only [decodeErrorFromBudgetSpec] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_de hpcf hrunf hspf hcsf _ _
  have hhigh' : bm_HighCalleeSaved s0 sf_de := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [decodeErrorFromBudgetSpec, arm64_norm, hsp, htrace]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_elim fun ⟨⟨hx0, htr⟩, hevs_de⟩ => ?_
  have hevs_bm : BytesMergeEnv x evs := by
    simpa only [BytesMergeEnv, bytesMergeEventsCore, hmerge, DecodeErrorFromEnv] using hevs_de
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) decodeVarintSliceStack)
    (by rw [stackAt_slice_to_decodeError s0.sp]; exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMerge s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self]⟩
  intro hmf
  dsimp only [bytesMergeStack,
    decodeVarintSliceStack] at hmf
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64,
    RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    Reg.x0, hx0, htr, ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [hevs_bm, pure_true, emp_sepConj]
  convert hmf using 2
  sep_ac_rfl

/-- Success epilogue from `(blkPl_290).base + 0x254` (`+596`): drops temporary `Bytes` via
vtable slot `[x24 + 0x20]` (`BLR x8` at `+0x26c`), sets `x0 := 0`, and returns at `+0x090`. -/
theorem epilogue3_vtableDrop_0x254_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st)
    (hcapOk : BytesMergeCapOk cap' rest.length)
    (hpc : s.pc = (blkPl_290).base + 596#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length + BitVec.ofNat 64 v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp ((blkPC_290).rebase (blkPl_290).base H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr cap' ptr' v ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A lim x st s0 R) (MergePanic A lim x st s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hVtableDrop' := bytesVtableDropSpecBM_of_spec hVtableDrop
  clear hVtableDrop
  rcases hevs with ⟨evs, hevs_env, hevs_eq⟩
  dsimp only [savedRegsStack] at hpc hVtableDrop' ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := bytesPlacedDropFnAddr tmpPtr v.length)
  apply SepWP.with_vtableSlot_placed tmpPtr v.length hro
  wp_steps
  apply SepWP.drop_left
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl_call hro_call
  refine SepWPp.bm_call_frame_lscl (x := st_cur)
    (T := bytesBoxU8Buf A.repAlloc tmpPtr v ∗ A.pool lim st_cur _ ∗ stackAt (s0.sp - 224#64) bytesVtableDropStack)
    hVtableDrop' hcl_call hro_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bytesVtableDropSpecBMGen, bytesVtableDropStack, arm64_norm, hsp]; rfl)
    (by
      simp only [Nat.le_refl, Nat.sub_self, BitVec.ofNat_eq_ofNat, true_and]
      simp only [wp_norm, arm64_norm, blkPl_290]
      apply lsRetAddr624_blockPlacement_base_add <;> decide)
    (by rw [stackAt_slice_to_vtableDrop s0.sp]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm; dsimp only [bytesVtableDropSpecBMGen] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_dr hpcf hrunf hspf hcsf _ _
  have hhigh' : bm_HighCalleeSaved s0 sf_dr := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [bytesVtableDropSpecBMGen, hevs_eq, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun htr => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) decodeVarintSliceStack)
    (by rw [stackAt_slice_to_vtableDrop s0.sp]; exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMerge s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.fold (vecU8At_entails_exists A.repAlloc x.valPtr cap' ptr' v hcapOk)
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self]⟩
  intro hmf
  dsimp only [bytesMergeStack,
    decodeVarintSliceStack] at hmf
  simp (config := { decide := true }) only [bytesMergeRawSpecGen,
    LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPostVec, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64,
    RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    Reg.x0, htr, ↓reduceIte, pure_true, emp_sepConj, sepExists_sepConj_left,
    sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [hevs_env, pure_true, emp_sepConj]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmf
  rcases hmf with ⟨c1, c2, hmf⟩
  refine ⟨c1, c2, ?_⟩
  convert hmf using 2
  sep_ac_rfl

/-! ## 2. Phase 3 (`+0x210..+0x280`, `+0x29c..+0x2c4`) on Block `290` (`[LibsignalPlacement]`) -/

/-- Phase 3 post-reserve (`+0x230..+0x254`): copies `v` into `valPtr` via `memcpy` (if `v ≠ []`),
updates `value.len := v.length`, and continues to `epilogue3_vtableDrop_0x254_placed`. -/
theorem phase3_from_0x230_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hmc : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ "memcpy")
      framelessMemcpyBudgetSpec)
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st)
    (hcapOk : BytesMergeCapOk cap' rest.length)
    (hcap' : v.length ≤ cap'.toNat)
    (hv_len : v.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_290).base + 560#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp ((blkPC_290).rebase (blkPl_290).base H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr cap' ptr' [] ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A lim x st s0 R) (MergePanic A lim x st s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  rcases v with _ | ⟨b0, v'⟩
  · have hep := fun {s : State} =>
      @epilogue3_vtableDrop_0x254_placed _ M A lim H x st st_cur s0 s R [] rest tmpPtr cap' ptr'
        hVtableDrop hmerge hevs hcapOk
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_290).base + 596#64)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.weaken_pre ?_ (hep
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      hhigh hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24]))
    exact Entails.of_eq (by
      simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
        RustCliAllocBudget.pool_writeReg64])
  · set v := b0 :: v'
    have hep := fun {s : State} =>
      @epilogue3_vtableDrop_0x254_placed _ M A lim H x st st_cur s0 s R v rest tmpPtr cap' ptr'
        hVtableDrop hmerge hevs hcapOk
    have hmc' : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
        ((blkPl_290).ρ "memcpy")
        (withLsCl lsmpl (bmMemcpySpecGen decodeErrorHookStack)) :=
      bmMemcpy_placed_of_framelessBudget hmc
    have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
    have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
      apply beq_false_of_ne
      intro h
      have h2 := congrArg BitVec.toNat h
      rw [hlen_toNat] at h2
      exact absurd h2 (by dsimp [v]; omega)
    have hbytesPtr : bytesPtr tmpPtr v.length = tmpPtr := by
      unfold bytesPtr
      have : v.length ≠ 0 := by omega
      simp [this]
    rw [vecU8At_nil_eq A.repAlloc x.valPtr cap' ptr' v hpos hcap', sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, hcap_lt, hptr'⟩ => ?_
    rw [bytesBoxU8Buf_nonempty A.repAlloc tmpPtr v hpos]
    refine SepWPp.weaken_pre (P' := ⌜tmpPtr ≠ 0#64 ∧ v.length < 2 ^ 63⌝ ∗
      ((x.valPtr ↦₆₄ cap') ∗ ((x.valPtr + 8#64) ↦₆₄ ptr') ∗ ((x.valPtr + 16#64) ↦₆₄ 0#64) ∗
        A.repAlloc.live ptr' cap'.toNat 1 ∗ memRegion ptr' v.length ∗
        memRegion (ptr' + BitVec.ofNat 64 v.length) (cap'.toNat - v.length) ∗
        A.repAlloc.live tmpPtr v.length 1 ∗ (tmpPtr ↦ₛ v) ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)) (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨htmp_ne, hv_lt63⟩ => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_290).ρ "memcpy")
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.bm_call_frame_lscl (x := (ptr', tmpPtr, v))
      (T := memRegion ptr' v.length ∗ (tmpPtr ↦ₛ v) ∗ stackAt (s0.sp - 224#64) decodeVarintSliceStack)
      hmc' hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [bmMemcpySpecGen, bmSliceStack, arm64_norm, hsp]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm, hlen_toNat, and_self])
      (by sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [bmMemcpySpecGen] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
    intro sf_mc hpcf hrunf hspf hcsf hclf hrof
    have hhigh' : bm_HighCalleeSaved s0 sf_mc := hhigh.of_calleeSaved hcsf
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, _, _, _, _, h29f, _⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h29f
    simp (config := { decide := true }) only [bmMemcpySpecGen, bmSliceStack, arm64_norm, hsp, htrace]
    refine SepWPp.pure_elim fun ⟨_, htr, hvm_mc⟩ => ?_
    have hpool_mc : A.pool lim st_cur s = A.pool lim st_cur sf_mc := by
      have hvm_s : VmPreserved sf_mc s := by
        simpa only [vmPreserved_setPC, vmPreserved_setPState,
          vmPreserved_writeReg64, vmPreserved_writeReg32] using hvm_mc.symm
      exact A.pool_of_vmPreserved hvm_s
    rw [hpool_mc]
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_290).base + 596#64)
    apply sepWP_seg_ls_vm (Q := (blkPC_290).rebase (blkPl_290).base (hooksException H)) blkLib_eq_290
      (mid := (blkPl_290).base + 596#64)
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
      (hnext := ?_)
    have hfb := fold_bytesBoxU8Buf_nonempty A.repAlloc tmpPtr v hpos htmp_ne hv_lt63
    dsimp only [RustCliAllocBudget.repAlloc] at hfb
    apply SepWP.fold hfb (by sep_focus)
    have hfv := fold_vecU8At_copied A.repAlloc x.valPtr cap' ptr' v hpos hcap' hcap_lt hptr'
    dsimp only [RustCliAllocBudget.repAlloc] at hfv
    apply SepWP.fold hfv (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (hep
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh'; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21, h20f, hx20, hbytesPtr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24]))
    exact Entails.of_eq (by sep_ac_rfl)

/-- Phase 3 entry (`+0x210..+0x280`, `+0x29c..+0x2c4`): clears `value.len := 0`, reserves capacity
via `do_reserve_and_handle [local#7]` (`lsmpl.base 320`) if `cap < v.length`, copies `v` into
`value`, drops temporary `Bytes`, and returns `0`. -/
theorem phase3_from_0x210_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hmc : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ "memcpy")
      framelessMemcpyBudgetSpec)
    (hReserve : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 320)
      (withLsCl lsmpl (doReserveSpec M A lim)))
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hfits_res : FitsEvents M lim st_cur (doReserveClearEvents x.valCap.toNat v.length))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧
      M.stepEvents (doReserveClearEvents x.valCap.toNat v.length ++ bytesDropEvents v) st_cur =
        M.stepEvents evs st)
    (hv_len : v.length < 2 ^ 63)
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_290).base + 528#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp ((blkPC_290).rebase (blkPl_290).base H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A lim x st s0 R) (MergePanic A lim x st s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hsum : 1 + v.length + rest.length ≤ x.bs.length := mergeBytes_length_sum hmerge
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp3 := fun (st_next : M.σ) (cap' ptr' : BitVec 64) {s : State}
      (hevs' : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (bytesDropEvents v) st_next = M.stepEvents evs st)
      (hcapOk' : BytesMergeCapOk cap' rest.length) (hcap' : v.length ≤ cap'.toNat) =>
    @phase3_from_0x230_placed _ M A lim H hmc x st st_next s0 s R v rest tmpPtr cap' ptr'
      hVtableDrop hmerge hevs' hcapOk' hcap' hv_len
  rw [bm_vecU8At_eq_header_sep_buf A.repAlloc x.valPtr x.valCap x.valBuf x.valBs]
  dsimp only [vecHeader] at hpc hReserve hp3 ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro
    (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true
      then (blkPl_290).base + 668#64 else (blkPl_290).base + 544#64)
  apply sepWP_seg_ls_vm (Q := (blkPC_290).rebase (blkPl_290).base (hooksException H)) blkLib_eq_290
    (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true
      then (blkPl_290).base + 668#64 else (blkPl_290).base + 544#64)
  intro _m_strip
  wp_steps
  refine SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
    (hnext := ?_)
  apply SepWP.fold (fold_vecU8At_clear A.repAlloc x.valPtr x.valCap x.valBuf x.valBs) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  by_cases hult : x.valCap.ult (BitVec.ofNat 64 v.length) = true
  · simp only [hult, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_lt : x.valCap.toNat < v.length := by
      simpa [BitVec.ult, hlen_toNat] using hult
    have hnewCap_bound :
        reserveCap x.valCap.toNat ([] : List (BitVec 8)).length v.length ≤ 9223372036854775807 :=
      bytesMergeCapOk_reserveCap_bound hcapOk hcap_lt hsum hbs_len
    have hcapOk' :
        BytesMergeCapOk (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) rest.length :=
      bytesMergeCapOk_after_reserve hcapOk hcap_lt hsum hbs_len
    have hnewCap_ge :
        v.length ≤ (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)).toNat := by
      dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap] at hnewCap_bound ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnewCap_ule :
        (BitVec.ofNat 64 v.length).ule
          (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) = true := by
      simp only [BitVec.ule, hlen_toNat, decide_eq_true_eq]
      exact hnewCap_ge
    let rc : DoReserveCall :=
      { v := x.valPtr, cap := x.valCap, ptr := x.valBuf, bs := [], additional := v.length }
    have hrc_evs : doReserveEvents rc = doReserveClearEvents x.valCap.toNat v.length :=
      doReserveEvents_eq_clear x.valPtr x.valCap x.valBuf v.length hcap_lt
    have hfits_rc : FitsEnv M lim st_cur (DoReserveEnv rc) := by
      rw [fitsEnv_doReserve_iff, hrc_evs]
      exact hfits_res
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := lsmpl.base 320)
    wp_steps
    refine ProofLib.SepWP.transport_budgetPool (A := A) (lim := lim) (st := st_cur) ?_ (hnext := ?_)
    · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    rw [stackAt_slice_to_doReserve s0.sp]
    refine SepWPp.bm_call_frame_lscl
      (x := (rc, st_cur))
      (T := vecU8At A.repAlloc x.valPtr x.valCap x.valBuf [] ∗
        A.pool lim st_cur _ ∗ stackAt (s0.sp - 224#64) doReserveStack)
      hReserve hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [doReserveSpec, doReserveSpecWithStack, arm64_norm, hsp, hx19, hx20]; rfl)
      (by exact ⟨rfl, rfl, hlen_toNat, hnewCap_bound, hfits_rc⟩)
      (by sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [doReserveSpec, doReserveSpecWithStack] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
    intro sf_res hpcf hrunf hspf hcsf hclf hrof
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
    obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
    dsimp only [doReserveSpec, doReserveSpecWithStack, rc, List.length_nil]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun htr => ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptr' => ?_
    rw [bm_vecU8At_eq_header_sep_buf A.repAlloc x.valPtr
      (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' []]
    dsimp only [vecHeader, List.length_nil]
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_290).base + 560#64)
    wp_steps
    apply SepWP.fold
      (fold_vecU8At_clear A.repAlloc x.valPtr
        (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' [])
      (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl3 hro3
    have hevs' : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (bytesDropEvents v) (M.stepEvents (doReserveEvents rc) st_cur) =
          M.stepEvents evs st := by
      obtain ⟨evs, he1, he2⟩ := hevs
      refine ⟨evs, he1, ?_⟩
      rw [← M.stepEvents_append, hrc_evs]
      exact he2
    refine SepWPp.weaken_pre ?_
      (hp3 (M.stepEvents (doReserveEvents rc) st_cur)
        (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' hevs' hcapOk' hnewCap_ge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
          h25f, h26f, h27f, h28f, h29f, hvregsf, h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
        hcl3 hro3
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f, hx20])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h23f])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24]))
    exact Entails.of_eq (by
      simp (config := { decide := true }) only [arm64_norm, hsp,
        RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
        RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
        RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
      rw [stackAt_slice_to_doReserve s0.sp]
      sep_ac_rfl)
  · have hult_eq : x.valCap.ult (BitVec.ofNat 64 v.length) = false :=
      Bool.eq_false_iff.mpr hult
    simp only [hult_eq, Bool.false_eq_true, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_ge : v.length ≤ x.valCap.toNat := by
      simp [BitVec.ult, hlen_toNat] at hult_eq
      exact hult_eq
    have hcapOk' : BytesMergeCapOk x.valCap rest.length :=
      bytesMergeCapOk_mono hcapOk (by omega)
    have hevs' : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st := by
      rwa [doReserveClearEvents_of_le hcap_ge, List.nil_append] at hevs
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_290).base + 560#64)
    wp_steps
    refine ProofLib.SepWP.transport_budgetPool (A := A) (lim := lim) (st := st_cur) ?_ (hnext := ?_)
    · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hp3 st_cur x.valCap x.valBuf hevs' hcapOk' hcap_ge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self])
        hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24]))

end LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23PlacedBudgetAux
