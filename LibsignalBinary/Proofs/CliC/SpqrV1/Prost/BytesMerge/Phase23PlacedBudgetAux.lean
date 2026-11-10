/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Epilogues and Phase 3 for `CliC` `bytes::merge`

Threads `RustCliAllocBudget M` and `VmPreserved` across the error/drop epilogues (`+0x074`,
`+0x07c`, `+0x254`) and Phase 3 (`+0x210..+0x250`, `+0x29c..+0x2cc`) of `CliC` `bytes::merge`
(Block `558`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.Phase23PlacedBudgetAux

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
  lsMemcpySym lsmpl withLsCl
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarintAux mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (
  KindNoHeap bytesBoxU8Buf bytesData bytesPlacedDropFnAddr bytesPlacedVtable bytesPtr
  bytesVtableDropStack decodeErrorAtStackLen decodeErrorHookStack doReserveStack
  framelessMemcpySpec reserveCap
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  BytesMergeCapOk BytesMergeGhost SepWP.drop_left SepWP.with_vtableSlot_placed
  SepWPp.bm_call_frame_lscl SepWPp.bm_of_sepWP_lscl
  bitvec_getLsbD_63_of_lt32 bitvec_if_zero_ult_self bitvec_msb_false_of_lt32
  bitvec_sub_self_64 bitvec_ult_33bits_of_lt32 bitvec_ult_zero
  bm_HighCalleeSaved bm_vecU8At_eq_header_sep_buf bytesBoxU8Buf_nonempty
  bytesMergeCapOk_after_reserve bytesMergeCapOk_mono bytesMergeCapOk_reserveCap_bound
  bytesMutDataWord_bit0 bytesMutDataWord_getElem_zero bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_lsr5 bytesMutDataWord_zero decodeVarintSliceStack
  fold_bytesBoxU8Buf_nonempty fold_stackAt_bytesMerge fold_vecU8At_clear
  fold_vecU8At_copied savedRegsStack sliceCursorAfter spAligned_sub_224
  stackAt_slice_to_decodeError stackAt_slice_to_doReserve stackAt_slice_to_vtableDrop
  vecU8At_entails_exists vecU8At_nil_eq
)
open CryptoVerification.RecordCodecs.Placed (blkPl_558 lsProg_558)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (
  DecodeErrorFromEnv decodeErrorFromBudgetSpec withVmPreserved
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveCall DoReserveEnv doReserveEvents doReserveSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget (
  bytesDropEvents bytesVtableDropSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget (
  MergePanicGen MergePostGen
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (
  BytesMergeEnv bmPostVec bytesMergeEventsCore bytesMergeRawSpec bytesMergeRawSpecGen
  doReserveClearEvents
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero
  bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32 bitvec_getLsbD_63_of_lt32
  CryptoVerification.LibsignalTripleRatchet.Prost.bitvec_ult_self
  bitvec_sub_self_64 bitvec_if_zero_ult_self

abbrev MergePost {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  MergePostGen decodeErrorHookStack true A lim x st s0 R sf P_f

abbrev MergePanic {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  MergePanicGen decodeErrorHookStack true A lim x st s0 R sf P_f

/-! ## Error and Drop Epilogue Lemmas (`+0x074`, `+0x07c`, `+0x254`) -/

theorem epilogue3_err_0x07c_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    (hmerge : mergeBytes x.wt x.bs = none)
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ st_cur = M.stepEvents evs st)
    (hpc : s.pc = (blkPl_558).base + 124#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 ≠ 0#64)
    (hhigh : bm_HighCalleeSaved s0 s) :
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
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
  obtain ⟨h25, h26, h27, h28⟩ := hhigh
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
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self]⟩
  intro hmf
  dsimp only [Reg.x0] at hx0 hmf ⊢
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64,
    RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    Reg.x0, hx0, htrace, ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [hevs_env, pure_true, emp_sepConj]
  convert hmf using 2
  sep_ac_rfl

theorem epilogue3_decodeErrorFrom_0x074_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_558 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {R : SepProp} {w : BitVec 64}
    (hw : KindNoHeap w)
    (hmerge : mergeBytes x.wt x.bs = none)
    (hfits : FitsEnv M lim st (BytesMergeEnv x))
    (hpc : s.pc = (blkPl_558).base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
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
  wp_steps_sync_pool (lsmpl.base 261)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  refine SepWPp.bm_call_frame_lscl (spec := decodeErrorFromBudgetSpec M A lim)
    (x := (s0.sp - 216#64, w, st))
    (T := ((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
      A.pool lim st _ ∗ stackAt (s0.sp - 224#64) decodeErrorHookStack)
    hdef hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeErrorFromBudgetSpec, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [KindNoHeap, wp_norm, arm64_norm, hsp, hw, hfits_de, and_self])
    (by rw [stackAt_slice_to_decodeError]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm; dsimp only [decodeErrorFromBudgetSpec] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_de hpcf hrunf hspf hcsf _hclf _hrof
  have hhigh' : bm_HighCalleeSaved s0 sf_de := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [decodeErrorFromBudgetSpec, arm64_norm, hsp, htrace]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_elim fun ⟨⟨hx0, htr⟩, hevs_de⟩ => ?_
  have hevs_bm : BytesMergeEnv x evs := by
    simpa only [BytesMergeEnv, bytesMergeEventsCore, hmerge, DecodeErrorFromEnv] using hevs_de
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) decodeVarintSliceStack)
    (by rw [stackAt_slice_to_decodeError]; exact Entails.refl _) (by sep_focus)
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
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self]⟩
  intro hmf
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64,
    RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    Reg.x0, hx0, htr, ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [hevs_bm, pure_true, emp_sepConj]
  convert hmf using 2
  sep_ac_rfl

theorem epilogue3_vtableDrop_0x254_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_558 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st)
    (hcapOk : BytesMergeCapOk cap' rest.length)
    (hpc : s.pc = (blkPl_558).base + 596#64)
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
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
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
  rcases hevs with ⟨evs, hevs_env, hevs_eq⟩
  dsimp only [savedRegsStack] at hpc hVtableDrop ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := bytesPlacedDropFnAddr tmpPtr v.length)
  apply SepWP.with_vtableSlot_placed tmpPtr v.length hro
  wp_steps
  apply SepWP.drop_left
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl_call hro_call
  refine SepWPp.bm_call_frame_lscl (spec := bytesVtableDropSpec M A lim tmpPtr v v.length) (x := st_cur)
    (T := bytesBoxU8Buf A.repAlloc tmpPtr v ∗ A.pool lim st_cur _ ∗ stackAt (s0.sp - 224#64) bytesVtableDropStack)
    hVtableDrop hcl_call hro_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bytesVtableDropSpec, arm64_norm, hsp]; rfl)
    (by
      simp only [Nat.le_refl, Nat.sub_self, BitVec.ofNat_eq_ofNat, true_and]
      simp only [wp_norm, arm64_norm, blkPl_558]
      apply lsRetAddr624_blockPlacement_base_add <;> decide)
    (by rw [stackAt_slice_to_vtableDrop]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm; dsimp only [bytesVtableDropSpec] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_dr hpcf hrunf hspf hcsf _hclf _hrof
  have hhigh' : bm_HighCalleeSaved s0 sf_dr := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [bytesVtableDropSpec, hevs_eq, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨htr, _⟩ => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) decodeVarintSliceStack)
    (by rw [stackAt_slice_to_vtableDrop]; exact Entails.refl _) (by sep_focus)
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
  dsimp only [CryptoVerification.LibsignalTripleRatchet.Prost.bytesMergeStack] at hmf
  have hstk_eq : 224 + decodeVarintSliceStack = decodeErrorHookStack + (80 + 224) := by
    dsimp [decodeVarintSliceStack]; omega
  rw [hstk_eq] at hmf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmf
  rcases hmf with ⟨cap1, ptr1, hmf⟩
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge,
    State.readReg64_setPC, State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64,
    RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    Reg.x0, htr, ↓reduceIte, pure_true, emp_sepConj, sepExists_sepConj_left,
    sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [hevs_env, pure_true, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists]
  refine ⟨cap1, ptr1, ?_⟩
  convert hmf using 2
  sep_ac_rfl

/-! ## Phase 3 (`+0x210..+0x250`, `+0x29c..+0x2cc`) -/

theorem phase3_from_0x230_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsMemcpySym)
      (withLsCl lsmpl (withVmPreserved framelessMemcpySpec)))
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_558 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st)
    (hcapOk : BytesMergeCapOk cap' rest.length)
    (hcap' : v.length ≤ cap'.toNat)
    (hv_len : v.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_558).base + 560#64)
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
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr cap' ptr' [] ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A lim x st s0 R) (MergePanic A lim x st s0 R) := by
  rcases v with _ | ⟨b0, v'⟩
  · have hep := fun {s : State} =>
      @epilogue3_vtableDrop_0x254_placed _ M A lim H
        x st st_cur s0 s R [] rest tmpPtr cap' ptr' hVtableDrop hmerge hevs hcapOk
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_558).base + 596#64)
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
    exact Entails.of_eq (by simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64])
  · set v := b0 :: v'
    have hep := fun {s : State} =>
      @epilogue3_vtableDrop_0x254_placed _ M A lim H
        x st st_cur s0 s R v rest tmpPtr cap' ptr' hVtableDrop hmerge hevs hcapOk
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
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_558).ρ lsMemcpySym)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.bm_call_frame_lscl (spec := withVmPreserved framelessMemcpySpec)
      (x := (ptr', tmpPtr, v))
      (T := memRegion ptr' v.length ∗ (tmpPtr ↦ₛ v))
      hmc hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      rfl
      (by simp (config := { decide := true }) only [withVmPreserved, framelessMemcpySpec, arm64_norm, hlen_toNat, hv_lt63, and_self])
      (by sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [withVmPreserved, framelessMemcpySpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
    intro sf_mc hpcf hrunf hspf hcsf hclf hrof
    have hhigh' : bm_HighCalleeSaved s0 sf_mc := hhigh.of_calleeSaved hcsf
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, _, _, _, _, h29f, hvregsf⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h29f hvregsf
    dsimp only [withVmPreserved, framelessMemcpySpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hvm_mc => ?_
    have hpool_mc : A.pool lim st_cur s = A.pool lim st_cur sf_mc := by
      have hvm_s : VmPreserved sf_mc s := by
        simpa only [LibsignalBinary.Proofs.Placed.BudgetVmSteps.vmPreserved_setPC,
          LibsignalBinary.Proofs.Placed.BudgetVmSteps.vmPreserved_setPState,
          LibsignalBinary.Proofs.Placed.BudgetVmSteps.vmPreserved_writeReg64] using hvm_mc.symm
      exact A.pool_of_vmPreserved hvm_s
    rw [hpool_mc]
    simp (config := { decide := true }) only [arm64_norm, htrace]
    refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_558).base + 596#64)
    wp_steps_sync_pool ((blkPl_558).base + 596#64)
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
    exact Entails.of_eq (by dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl)

private theorem decodeVarintAux_length_lt_placed (i : Nat) (acc : BitVec 64)
    (bs rest0 : List (BitVec 8)) (len : BitVec 64)
    (h : decodeVarintAux i acc bs = some (len, rest0)) :
    rest0.length < bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b bs' ih =>
    unfold decodeVarintAux at h
    dsimp only at h
    split at h
    · split at h
      · contradiction
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simp
    · split at h
      · contradiction
      · have hlt := ih _ _ h
        simp
        omega

private theorem mergeBytes_length_sum_placed {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    1 + v.length + rest.length ≤ bs.length := by
  cases wt <;> try simp [mergeBytes] at h
  cases hvar : decodeVarint bs with
  | none => simp [hvar] at h
  | some p =>
    rcases p with ⟨len, rest0⟩
    rw [hvar] at h
    dsimp only at h
    split at h
    · contradiction
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 : rest0.length < bs.length := decodeVarintAux_length_lt_placed 0 0 bs rest0 len hvar
      have h2 : (rest0.take len.toNat).length + (rest0.drop len.toNat).length = rest0.length := by
        rw [← List.length_append, List.take_append_drop]
      omega

private theorem doReserveEvents_nil_eq_clear (vPtr cap ptr : BitVec 64) (vLen : Nat)
    (hcap_lt : cap.toNat < vLen) :
    doReserveEvents { v := vPtr, cap := cap, ptr := ptr, bs := [], additional := vLen } =
      doReserveClearEvents cap.toNat vLen := by
  have hnot_le : ¬ (vLen ≤ cap.toNat) := Nat.not_le.mpr hcap_lt
  have hcap0_iff : (cap = 0#64) ↔ (cap.toNat = 0) := by
    constructor
    · rintro rfl; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  simp only [doReserveEvents, doReserveClearEvents, List.length_nil, Nat.zero_add,
    hnot_le, ↓reduceIte, hcap0_iff]

theorem phase3_from_0x210_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsMemcpySym)
      (withLsCl lsmpl (withVmPreserved framelessMemcpySpec)))
    (hReserve : subroutine_ok (lsProg_558 H) (lsmpl.base 561)
      (withLsCl lsmpl (doReserveSpec M A lim)))
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_558 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hfits_res : FitsEvents M lim st_cur (doReserveClearEvents x.valCap.toNat v.length))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧
      M.stepEvents (bytesDropEvents v)
        (M.stepEvents (doReserveClearEvents x.valCap.toNat v.length) st_cur) =
        M.stepEvents evs st)
    (hv_len : v.length < 2 ^ 63)
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_558).base + 528#64)
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
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
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
  have hsum : 1 + v.length + rest.length ≤ x.bs.length := mergeBytes_length_sum_placed hmerge
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp3 := fun (st2 : M.σ) (cap' ptr' : BitVec 64) {s : State}
      (hevs2 : ∃ evs, BytesMergeEnv x evs ∧ M.stepEvents (bytesDropEvents v) st2 = M.stepEvents evs st)
      (hcapOk' : BytesMergeCapOk cap' rest.length) (hcap' : v.length ≤ cap'.toNat) =>
    @phase3_from_0x230_placed _ M A lim H hmc
      x st st2 s0 s R v rest tmpPtr cap' ptr' hVtableDrop hmerge hevs2 hcapOk' hcap' hv_len
  rw [bm_vecU8At_eq_header_sep_buf A.repAlloc x.valPtr x.valCap x.valBuf x.valBs]
  dsimp only [vecHeader] at hpc hReserve hp3 ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro
    (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true then (blkPl_558).base + 668#64 else (blkPl_558).base + 544#64)
  wp_steps_sync_pool
    (if x.valCap.ult (BitVec.ofNat 64 v.length) = true then (blkPl_558).base + 668#64 else (blkPl_558).base + 544#64)
  have hfvc := fold_vecU8At_clear A.repAlloc x.valPtr x.valCap x.valBuf x.valBs
  dsimp only [RustCliAllocBudget.repAlloc] at hfvc
  apply SepWP.fold hfvc (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  by_cases hult : x.valCap.ult (BitVec.ofNat 64 v.length) = true
  · simp only [hult, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_lt : x.valCap.toNat < v.length := by
      simpa [BitVec.ult, hlen_toNat] using hult
    have hnewCap_bound : reserveCap x.valCap.toNat ([] : List (BitVec 8)).length v.length ≤ 9223372036854775807 :=
      bytesMergeCapOk_reserveCap_bound hcapOk hcap_lt hsum hbs_len
    have hcapOk' : BytesMergeCapOk (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) rest.length :=
      bytesMergeCapOk_after_reserve hcapOk hcap_lt hsum hbs_len
    have hnewCap_ge : v.length ≤ (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)).toNat := by
      dsimp [reserveCap] at hnewCap_bound ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnewCap_ule :
        (BitVec.ofNat 64 v.length).ule (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) = true := by
      simp only [BitVec.ule, hlen_toNat, decide_eq_true_eq]
      exact hnewCap_ge
    let rcall : DoReserveCall :=
      { v := x.valPtr, cap := x.valCap, ptr := x.valBuf, bs := [], additional := v.length }
    have hfits_do : FitsEnv M lim st_cur (DoReserveEnv rcall) := by
      intro evs he
      rw [DoReserveEnv] at he
      subst he
      rwa [doReserveEvents_nil_eq_clear _ _ _ _ hcap_lt]
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := lsmpl.base 561)
    wp_steps_sync_pool (lsmpl.base 561)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    rw [stackAt_slice_to_doReserve s0.sp]
    refine SepWPp.bm_call_frame_lscl (spec := doReserveSpec M A lim)
      (x := (rcall, st_cur))
      (T := vecU8At A.repAlloc x.valPtr x.valCap x.valBuf [] ∗
        A.pool lim st_cur _ ∗ stackAt (s0.sp - 224#64) doReserveStack)
      hReserve hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [doReserveSpec, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack, rcall, arm64_norm, hsp, hx19, hx20]; rfl)
      (by simp only [hlen_toNat, hnewCap_bound, and_true, true_and]; exact hfits_do)
      (by dsimp only [RustCliAllocBudget.repAlloc]; sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [doReserveSpec, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
    intro sf_res hpcf hrunf hspf hcsf hclf hrof
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
    obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
    dsimp only [doReserveSpec, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack, rcall, List.length_nil]
    rw [doReserveEvents_nil_eq_clear _ _ _ _ hcap_lt]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun htr => ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptr' => ?_
    rw [bm_vecU8At_eq_header_sep_buf A.repAlloc x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' []]
    dsimp only [vecHeader, List.length_nil]
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_558).base + 560#64)
    wp_steps_sync_pool ((blkPl_558).base + 560#64)
    have hfvc' := fold_vecU8At_clear A.repAlloc x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' []
    dsimp only [RustCliAllocBudget.repAlloc] at hfvc'
    apply SepWP.fold hfvc' (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl3 hro3
    refine SepWPp.weaken_pre (P' :=
      vecU8At A.repAlloc x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' [] ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        A.pool lim (M.stepEvents (doReserveClearEvents x.valCap.toNat v.length) st_cur) _ ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (Entails.of_eq (by dsimp only [RustCliAllocBudget.repAlloc]; simp (config := { decide := true }) only [arm64_norm, hsp]; rw [stackAt_slice_to_doReserve s0.sp]; sep_ac_rfl)) ?_
    exact hp3 (M.stepEvents (doReserveClearEvents x.valCap.toNat v.length) st_cur)
      (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' hevs hcapOk' hnewCap_ge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
      hcl3 hro3
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h23f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24])
  · have hult_eq : x.valCap.ult (BitVec.ofNat 64 v.length) = false :=
      Bool.eq_false_iff.mpr hult
    simp only [hult_eq, Bool.false_eq_true, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_ge : v.length ≤ x.valCap.toNat := by
      simp [BitVec.ult, hlen_toNat] at hult_eq
      exact hult_eq
    have hclear_nil : doReserveClearEvents x.valCap.toNat v.length = [] := by
      simp [doReserveClearEvents, hcap_ge]
    have hevs' : ∃ evs, BytesMergeEnv x evs ∧ M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st := by
      simpa only [hclear_nil, AllocCostModel.stepEvents_nil] using hevs
    have hcapOk' : BytesMergeCapOk x.valCap rest.length :=
      bytesMergeCapOk_mono hcapOk (by omega)
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_558).base + 560#64)
    wp_steps_sync_pool ((blkPl_558).base + 560#64)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl))
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

end LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.Phase23PlacedBudgetAux
