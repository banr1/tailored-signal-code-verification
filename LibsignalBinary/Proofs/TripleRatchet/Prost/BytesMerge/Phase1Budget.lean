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
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.Basic
import ProofLib.SepLogic.WP

/-!
# Budget-Threaded Relocatable `prost::encoding::bytes::merge::<Vec<u8>>` Phase 1

Verifies Phase 1 under `RustCliAllocBudget` and `[LibsignalPlacement]` and proves
`bytes_merge_placed_ok_of_contracts_gen`, `bytes_merge_placed_ok_of_contracts`, and
`bytes_merge_placed_ok_of_contracts_x`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1Budget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustAllocEvents rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocBudgetSpecWithStack)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec decodeErrorFromBudgetSpecWithStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
  (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveSpec doReserveSpecX doReserveSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
  (bytesFromVecPlacedSpec bytesVtableDropSpec bytesVtableDropSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (DecodeVarintSlowEnv decodeVarintSlowEvents
   decodeVarintSlowBudgetSpec decodeVarintSlowBudgetSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents decodeVarintSliceSpec decodeVarintSliceSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore bmPreBoundBudget bytesMergeRawSpecGen
   BytesMergePlacedOk BytesMergePlacedOkX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
  (BytesMergeExactPlacedOkX MergeExactPostGen MergeExactPanicGen MergePostGen MergePanicGen
   bmMemcpySpecGen bmShimSpecGen bytesMergeExactRawSpecGen bytesMergeExactRawSpecGen_post_entails
   bytesVtableDropSpecBMGen decodeVarintSliceSpecBMGen
   epilogue_decodeErrorFrom_placed_gen epilogue_err_0x0a4_placed_gen)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23Budget.BytesMergeFacts
  (phase2_from_0x0e0_export_placed_gen)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded lsmpl
   blkPC_7 blkPl_7 blkLib_eq_7 withLsCl lsRustNoAllocShimSym lsRustAllocSym)
open CryptoVerification.RustHeap
  (allocHookStack vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap bytesPlacedDropFnAddr bytesVtableDropStack bytesVtableDropStackX
   decodeErrorAtStackLen decodeErrorHookStack extHookStack varintSlow
   withLsCodeRoLoaded extract_withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
  (varintSlow_some_iff)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost DecodeVarintSliceGhost VarintSlicePre varintSliceResultAt
   SepWPp.bm_call_frame_lscl SepWPp.bm_of_sepWP_lscl
   SepWPp.unfold_cells_64 SepWPp.unfold_memRegion_216
   SepWPp.unfold_memRegion_216_invalidWireType
   bmCapCond bmLenBound bmLenBound_lt63 bmSliceStack bmTotalStack bm_HighCalleeSaved
   bm_decodeVarint_suffix bm_pointsToBytes_split_last
   bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
   bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero
   bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32 bitvec_getLsbD_63_of_lt32
   bitvec_sub_self_64 bitvec_if_zero_ult_self
   decodeErrorHookStackX decodeVarint_cons_of_signExtend_63_false
   fold_memRegion_40_bytes fold_memRegion_48_sret_err fold_memRegion_48_sret_ok
   fold_sliceCursorAfter_cons fold_sliceCursorAfter_drop fold_sliceCursorAfter_from_consumed
   fold_slot_16 mask_ff_32_of_setWidth8 memRegion_48_sret24
   mergeBytes_ne_lengthDelimited mergeBytes_nil mergeBytes_of_decodeVarint_none
   savedRegsStack sliceCursorAfter sliceCursorAt spAligned_sub_224
   stackAt_bytesMergeGen_entry stackAt_sliceGen_split
   toNat_le_0x7f_of_getLsbD_7_false varintSlow_none_iff)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (bitvec8_forall truncate32_zeroExtend64_and_255_eq)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero
  bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32 bitvec_getLsbD_63_of_lt32
  bitvec_ult_self bitvec_sub_self_64 bitvec_if_zero_ult_self

/-! ## Precondition, stack-spec, and outcome helpers -/

theorem bmPreBoundBudget_elim {M : AllocCostModel} {reqCap : Bool} {lim : BudgetLimits}
    {st : M.σ} {s : State} {x : BytesMergeGhost}
    (h : bmPreBoundBudget reqCap lim st s x) :
    (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧
      bmLenBound reqCap x.bs.length ∧ bmCapCond reqCap x.valCap x.bs.length ∧
      FitsEnv M lim st (BytesMergeEnv x) := by
  cases reqCap
  · obtain ⟨h0, h1, h2, h3, hfits⟩ := h
    exact ⟨h0, h1, h2, h3, trivial, hfits⟩
  · exact h

theorem bytesVtableDropSpecBMGen_of_spec [LibsignalPlacement]
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

theorem bytesVtableDropSpecBMGen_of_spec_x [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ptr : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    (h : subroutine_ok prog entry
      (withLsCl lsmpl (bytesVtableDropSpecX M A lim ptr bs off))) :
    subroutine_ok prog entry
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim extHookStack ptr bs off)) := by
  refine subroutine_ok_outcome_intro fun st R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨
      (withLsCl lsmpl (bytesVtableDropSpecX M A lim ptr bs off)).pre st s0 ∗ R := by
    dsimp only [withLsCl, CryptoVerification.withLsCodeLoaded,
      bytesVtableDropSpecX, bytesVtableDropSpecBMGen, bytesVtableDropStackX] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨h1, h2, h3, h4, hlr⟩, hrest⟩
    exact ⟨by simp only [h1, h2, h3, h4, hlr, and_self], hrest⟩
  refine h.mono_outcome st R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex | hoom)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl, CryptoVerification.withLsCodeLoaded,
      bytesVtableDropSpecX, bytesVtableDropSpecBMGen, bytesVtableDropStackX] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1.1, hpost.2.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

abbrev session2MemcpyBudgetSpecBMX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  bmMemcpySpecGen decodeErrorHookStackX

abbrev session2ShimBudgetSpecBMX : Spec Unit :=
  bmShimSpecGen decodeErrorHookStackX

theorem SepWPp.to_subroutineOutcome_placed_gen [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {errStack : Nat} {reqCap : Bool}
    {x : BytesMergeGhost} {st : M.σ} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (MergePostGen errStack reqCap A lim x st s0 R)
      (MergePanicGen errStack reqCap A lim x st s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (withLsCodeRoLoaded lsmpl (bytesMergeRawSpecGen A lim errStack reqCap))
        (x, st) R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hoom⟩⟩ :=
    h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem SepWPp.to_subroutineOutcome_exact_placed_gen [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {errStack : Nat} {reqCap : Bool}
    {x : BytesMergeGhost} {st : M.σ} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (withLsCodeRoLoaded lsmpl (bytesMergeExactRawSpecGen A lim errStack reqCap))
        (x, st) R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hoom⟩⟩ :=
    h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Relocatable `[LibsignalPlacement]` Phase 1 and `bytes_merge_placed_ok` -/

private theorem phase1_from_0x08c_placed_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim errStack)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (bmShimSpecGen errStack)))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false hStack)))
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecBMGen A lim errStack)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack M A lim (hStack + 48))))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim hStack tmpPtr v v.length)))
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {R : SepProp}
    (hwt : x.wt = .lengthDelimited)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hfits : FitsEnv M lim st (BytesMergeEnv x))
    (hpre : VarintSlicePre x.bs)
    (hpc : s.pc = (blkPl_7).base + 140#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx1 : s.readReg64 .x1 = x.ptr)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.bs.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = x.slot)
    (hx21 : s.readReg64 .x21 = x.bufRef)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool lim st s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hbs_toNat : (BitVec.ofNat 64 x.bs.length).toNat = x.bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hfits_vs : FitsEnv M lim st (DecodeVarintSliceEnv x.bs) := by
    intro evs hevs
    subst hevs
    unfold decodeVarintSliceEvents
    cases hdv : decodeVarint x.bs with
    | none =>
      have hm : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hdv
      exact hfits (rustAllocEvents 72 8) (by simp [BytesMergeEnv, bytesMergeEventsCore, hm])
    | some _ => trivial
  have herr_exit := fun {st_cur : M.σ} {s : State}
      (hmerge : mergeBytes x.wt x.bs = none)
      (hevs : ∃ evs, BytesMergeEnv x evs ∧ st_cur = M.stepEvents evs st) =>
    @epilogue_err_0x0a4_placed_gen _ M A lim H errStack reqCap hbnd x st st_cur s0 s R hmerge hevs
  have h0e0_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hvar : decodeVarint x.bs = some (len, rest0)) =>
    @phase2_from_0x0e0_export_placed_gen _ M A lim H hStack errStack reqCap hbnd hres_le
      hdef hmc hshim halloc hBytesFromVec hReserve
      hVtableDrop x st s0 s R len rest0 hwt hvar hbs_len hcapOk hfits
  clear hBytesFromVec hReserve hVtableDrop
  dsimp only [sliceCursorAt] at hpc hVarintSlice herr_exit h0e0_exit ⊢
  rw [memRegion_48_sret24 (s0.sp - 216#64)]
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 76)
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  refine SepWPp.bm_call_frame_lscl
    (x := (({ ret := s0.sp - 216#64, ptr := x.ptr, bs := x.bs } : DecodeVarintSliceGhost), st))
    (T := memRegion (s0.sp - 216#64) 24 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool lim st _ ∗
      stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    hVarintSlice hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeVarintSliceSpecBMGen,
      LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.decodeVarintSliceSpecGen,
      arm64_norm, hsp]; rfl)
    (by exact ⟨by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1],
               by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8, hbs_toNat],
               bmLenBound_lt63 hbs_len, hpre, hfits_vs⟩)
    (by (conv => lhs; simp (config := { failIfUnchanged := false }) only [arm64_norm]); sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm
        dsimp only [decodeVarintSliceSpecBMGen,
          LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.decodeVarintSliceSpecGen] at hm
        rw [sepConj_assoc] at hm
        exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_vs hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx29] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  simp (config := { decide := true }) only [decodeVarintSliceSpecBMGen,
    LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.decodeVarintSliceSpecGen,
    arm64_norm, hsp, htrace, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_elim fun ⟨htr, hevs_vs⟩ => ?_
  rcases hvar : decodeVarint x.bs with _ | ⟨len, rest0⟩
  · have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
    have hevs_bm : BytesMergeEnv x evs := by
      simpa [DecodeVarintSliceEnv, decodeVarintSliceEvents, hvar,
        BytesMergeEnv, bytesMergeEventsCore, hmerge] using hevs_vs
    dsimp only [varintSliceResultAt]
    refine SepWPp.weaken_pre (P' :=
      (∃∗ e : BitVec 64, ⌜e ≠ 0#64⌝ ∗ ((s0.sp - 216#64 + 8#64) ↦₆₄ e) ∗
        decodeErrorAtStackLen A.repAlloc e 0) ∗
        (((s0.sp - 216#64) ↦₆₄ 1#64) ∗ memRegion (s0.sp - 216#64 + 16#64) 8 ∗
          (x.ptr ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) sf_vs ∗
          stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          memRegion (s0.sp - 224#64) 8 ∗ memRegion (s0.sp - 216#64 + 24#64) 24 ∗
          memRegion (s0.sp - 168#64) 104 ∗ savedRegsStack s0.sp s0))
      (Entails.of_eq (by dsimp only [bmSliceStack]; simp (config := { decide := true }) only [arm64_norm]; sep_ac_rfl)) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun e => ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun he => ?_
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (164))
    wp_steps
    apply SepWP.fold (fold_memRegion_48_sret_err (s0.sp - 216#64) 1#64 e) (by sep_focus)
    apply SepWP.fold (fold_slot_16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (herr_exit hmerge ⟨evs, hevs_bm, rfl⟩
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; exact he)
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
        h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self]))
    exact Entails.of_eq (by
      simp (config := { decide := true, failIfUnchanged := false }) only [arm64_norm]
      sep_ac_rfl)
  · have hevs_nil : evs = [] := by
      simpa [DecodeVarintSliceEnv, decodeVarintSliceEvents, hvar] using hevs_vs
    subst hevs_nil
    dsimp only [varintSliceResultAt, AllocCostModel.stepEvents]
    have hrest0_le : rest0.length ≤ x.bs.length := by
      obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
      rw [hpfx, List.length_append]
      omega
    have hcons_toNat : (BitVec.ofNat 64 (x.bs.length - rest0.length)).toNat = x.bs.length - rest0.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hult_cons : (BitVec.ofNat 64 x.bs.length).ult (BitVec.ofNat 64 (x.bs.length - rest0.length)) = false := by
      simp [BitVec.ult, hbs_toNat, hcons_toNat]
    have hule_cons : (BitVec.ofNat 64 (x.bs.length - rest0.length)).ule (BitVec.ofNat 64 x.bs.length) = true := by
      simp [BitVec.ule, hbs_toNat, hcons_toNat]
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (224))
    apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
      (mid := (blkPl_7).base + bv% (224))
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hult_cons, hule_cons])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
      (hnext := ?_)
    apply SepWP.fold (fold_memRegion_48_sret_ok (s0.sp - 216#64) 0#64 len
      (BitVec.ofNat 64 (x.bs.length - rest0.length))) (by sep_focus)
    apply SepWP.fold (fold_sliceCursorAfter_from_consumed x.slot x.ptr x.bs rest0 hrest0_le) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hult_cons, hule_cons])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (h0e0_exit len rest0 hvar
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hult_cons, hule_cons])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
        h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))
    exact Entails.of_eq (by dsimp only [AllocCostModel.stepEvents, List.foldl, bmSliceStack]; sep_ac_rfl)

private theorem phase1_from_0x398_placed_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim errStack)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (bmShimSpecGen errStack)))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false hStack)))
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowBudgetSpecWithStack M A lim (64 + errStack))))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack M A lim (hStack + 48))))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim hStack tmpPtr v v.length)))
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {R : SepProp}
    (hwt : x.wt = .lengthDelimited)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hfits : FitsEnv M lim st (BytesMergeEnv x))
    (hpc : s.pc = (blkPl_7).base + 920#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx21 : s.readReg64 .x21 = x.bufRef)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool lim st s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hfits_vs : FitsEnv M lim st (DecodeVarintSlowEnv x.bs) := by
    intro evs hevs
    subst hevs
    unfold decodeVarintSlowEvents
    cases hvs : varintSlow x.bs with
    | none =>
      have hdv : decodeVarint x.bs = none := (varintSlow_none_iff x.bs).mp hvs
      have hm : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hdv
      exact hfits (rustAllocEvents 72 8) (by simp [BytesMergeEnv, bytesMergeEventsCore, hm])
    | some _ => trivial
  have herr_exit := fun {st_cur : M.σ} {s : State}
      (hmerge : mergeBytes x.wt x.bs = none)
      (hevs : ∃ evs, BytesMergeEnv x evs ∧ st_cur = M.stepEvents evs st) =>
    @epilogue_err_0x0a4_placed_gen _ M A lim H errStack reqCap hbnd x st st_cur s0 s R hmerge hevs
  have h0e0_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hvar : decodeVarint x.bs = some (len, rest0)) =>
    @phase2_from_0x0e0_export_placed_gen _ M A lim H hStack errStack reqCap hbnd hres_le
      hdef hmc hshim halloc hBytesFromVec hReserve
      hVtableDrop x st s0 s R len rest0 hwt hvar hbs_len hcapOk hfits
  clear hBytesFromVec hReserve hVtableDrop
  dsimp only [sliceCursorAt] at hpc hVarintSlow herr_exit h0e0_exit ⊢
  rw [stackAt_sliceGen_split s0.sp errStack (64 + errStack) (by dsimp [bmSliceStack]; omega) hbnd]
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 293)
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  refine SepWPp.bm_call_frame_lscl
    (x := (x.bufRef, x.slot, x.ptr, x.bs, st))
    (T := (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
      ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      (x.ptr ↦ₛ x.bs) ∗ A.pool lim st _ ∗ stackAt (s0.sp - 224#64) (64 + errStack))
    hVarintSlow hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeVarintSlowBudgetSpecWithStack, arm64_norm, hsp, hx21]; rfl)
    (by refine ⟨?_, hfits_vs⟩; omega)
    (by (conv => lhs; simp (config := { failIfUnchanged := false }) only [arm64_norm]); sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm; dsimp only [decodeVarintSlowBudgetSpecWithStack] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_vs hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx21, hx29] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  simp (config := { decide := true }) only [decodeVarintSlowBudgetSpecWithStack, arm64_norm, hsp, htrace,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_elim fun ⟨htr, hevs_vs⟩ => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    (by rw [stackAt_sliceGen_split s0.sp errStack (64 + errStack) (by dsimp [bmSliceStack]; omega) hbnd]
        exact Entails.refl _) (by sep_focus)
  rcases hvs : varintSlow x.bs with _ | ⟨len, k⟩
  · dsimp only
    have hvar : decodeVarint x.bs = none := (varintSlow_none_iff x.bs).mp hvs
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
    have hevs_bm : BytesMergeEnv x evs := by
      simpa [DecodeVarintSlowEnv, decodeVarintSlowEvents, hvs,
        BytesMergeEnv, bytesMergeEventsCore, hmerge] using hevs_vs
    refine SepWPp.weaken_pre (P' :=
      ⌜sf_vs.readReg64 .x0 = 1#64 ∧ sf_vs.readReg64 .x1 ≠ 0#64⌝ ∗
        (decodeErrorAtStackLen A.repAlloc (sf_vs.readReg64 .x1) 0 ∗
          (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (min 10 x.bs.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.bs.length - min 10 x.bs.length)) ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ (x.ptr ↦ₛ x.bs) ∗
          A.pool lim (M.stepEvents evs st) sf_vs ∗
          stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (164))
    wp_steps
    apply SepWP.fold (fold_slot_16 x.slot
      (x.ptr + BitVec.ofNat 64 (min 10 x.bs.length))
      (BitVec.ofNat 64 (x.bs.length - min 10 x.bs.length))) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (herr_exit hmerge ⟨evs, hevs_bm, rfl⟩
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; exact hx1_sf)
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
        h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self]))
    exact Entails.of_eq (by
      simp (config := { decide := true, failIfUnchanged := false }) only [arm64_norm]
      sep_ac_rfl)
  · have hevs_nil : evs = [] := by
      simpa [DecodeVarintSlowEnv, decodeVarintSlowEvents, hvs] using hevs_vs
    subst hevs_nil
    dsimp only [AllocCostModel.stepEvents]
    obtain ⟨hk1, hkl, hvar⟩ := (varintSlow_some_iff x.bs len k).mp hvs
    refine SepWPp.weaken_pre (P' :=
      ⌜sf_vs.readReg64 .x0 = 0#64 ∧ sf_vs.readReg64 .x1 = len⌝ ∗
        ((x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 k)) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.bs.length - k)) ∗
          (x.ptr ↦ₛ x.bs) ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ A.pool lim st sf_vs ∗
          stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (224))
    wp_steps
    apply SepWP.fold (fold_sliceCursorAfter_drop x.slot x.ptr x.bs k hkl) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (h0e0_exit len (x.bs.drop k) hvar
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
        h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))
    exact Entails.of_eq (by
      simp (config := { failIfUnchanged := false }) only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
      sep_ac_rfl)

private theorem phase1_from_0x074_placed_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim errStack)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (bmShimSpecGen errStack)))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false hStack)))
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowBudgetSpecWithStack M A lim (64 + errStack))))
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecBMGen A lim errStack)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack M A lim (hStack + 48))))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim hStack tmpPtr v v.length)))
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {R : SepProp}
    (hwt : x.wt = .lengthDelimited)
    (hne : x.bs ≠ [])
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hfits : FitsEnv M lim st (BytesMergeEnv x))
    (hpc : s.pc = (blkPl_7).base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx1 : s.readReg64 .x1 = x.ptr)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.bs.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = x.slot)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool lim st s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hbs_toNat : (BitVec.ofNat 64 x.bs.length).toNat = x.bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h08c_exit := fun {s : State} (hpre : VarintSlicePre x.bs) =>
    @phase1_from_0x08c_placed_gen _ M A lim H hStack errStack reqCap hbnd hres_le
      hdef hmc hshim halloc hVarintSlice hBytesFromVec
      hReserve hVtableDrop x st s0 s R hwt hbs_len hcapOk hfits hpre
  have h398_exit := fun {s : State} =>
    @phase1_from_0x398_placed_gen _ M A lim H hStack errStack reqCap hbnd hres_le
      hdef hmc hshim halloc hVarintSlow hBytesFromVec
      hReserve hVtableDrop x st s0 s R hwt hbs_len hcapOk hfits
  clear hVarintSlow hVarintSlice hBytesFromVec hReserve hVtableDrop
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  apply SepWPp.bm_of_sepWP_lscl hcl hro
    (mid := if (10#64).ult (BitVec.ofNat 64 x.bs.length) = true
      then (blkPl_7).base + bv% (140) else (blkPl_7).base + bv% (128))
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx8])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  by_cases h11 : (10#64).ult (BitVec.ofNat 64 x.bs.length) = true
  · simp only [h11, ↓reduceIte] at hcl1 hro1 ⊢
    have hge11 : 11 ≤ x.bs.length := by
      have : 10 < x.bs.length := by simpa [BitVec.ult, hbs_toNat] using h11
      omega
    have hpre : VarintSlicePre x.bs := Or.inl hge11
    refine SepWPp.weaken_pre ?_ (h08c_exit hpre
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx8, h11])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
        h25_0, h26_0, h27_0, h28_0, and_self])
      hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
    exact Entails.of_eq (by
      simp (config := { failIfUnchanged := false }) only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg])
  · have h11_eq : (10#64).ult (BitVec.ofNat 64 x.bs.length) = false := Bool.eq_false_iff.mpr h11
    simp only [h11_eq, Bool.false_eq_true, ↓reduceIte] at hcl1 hro1 ⊢
    dsimp only [sliceCursorAt]
    rw [bm_pointsToBytes_split_last x.ptr x.bs hne (bmLenBound_lt63 hbs_len)]
    by_cases hlast : (x.bs.getLast hne).getLsbD 7 = true
    · have hlast31 : (((x.bs.getLast hne).signExtend 32).zeroExtend 64).getLsbD 31 = true := by
        revert hlast; generalize x.bs.getLast hne = b; revert b; apply bitvec8_forall; decide
      apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (920))
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          (x.ptr ↦ₛ x.bs.dropLast) ∗
          ((x.ptr + BitVec.ofNat 64 x.bs.length + 0xffffffffffffffff#64) ↦₈ x.bs.getLast hne) ⊢
          sliceCursorAt x.slot x.ptr x.bs from by
        unfold sliceCursorAt
        rw [← bm_pointsToBytes_split_last x.ptr x.bs hne (bmLenBound_lt63 hbs_len)]
        exact Entails.of_eq (by sep_ac_rfl)) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hcl2 hro2
      refine SepWPp.weaken_pre ?_ (h398_exit
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
          h25_0, h26_0, h27_0, h28_0, and_self])
        hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
      exact Entails.of_eq (by
        simp (config := { failIfUnchanged := false }) only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
        sep_ac_rfl)
    · have hlast_eq : (x.bs.getLast hne).getLsbD 7 = false := Bool.eq_false_iff.mpr hlast
      have hlast31 : (((x.bs.getLast hne).signExtend 32).zeroExtend 64).getLsbD 31 = false := by
        revert hlast_eq; generalize x.bs.getLast hne = b; revert b; apply bitvec8_forall; decide
      apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (140))
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          (x.ptr ↦ₛ x.bs.dropLast) ∗
          ((x.ptr + BitVec.ofNat 64 x.bs.length + 0xffffffffffffffff#64) ↦₈ x.bs.getLast hne) ⊢
          sliceCursorAt x.slot x.ptr x.bs from by
        unfold sliceCursorAt
        rw [← bm_pointsToBytes_split_last x.ptr x.bs hne (bmLenBound_lt63 hbs_len)]
        exact Entails.of_eq (by sep_ac_rfl)) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hcl2 hro2
      have hpre : VarintSlicePre x.bs := Or.inr ⟨hne, toNat_le_0x7f_of_getLsbD_7_false hlast_eq⟩
      refine SepWPp.weaken_pre ?_ (h08c_exit hpre
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
          h25_0, h26_0, h27_0, h28_0, and_self])
        hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
      exact Entails.of_eq (by
        simp (config := { failIfUnchanged := false }) only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
        sep_ac_rfl)

theorem bytes_merge_placed_ok_of_contracts_exact_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim errStack)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (bmShimSpecGen errStack)))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false hStack)))
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowBudgetSpecWithStack M A lim (64 + errStack))))
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecBMGen A lim errStack)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack M A lim (hStack + 48))))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim hStack tmpPtr v v.length))) :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (blkPl_7).base
      (withLsCodeRoLoaded lsmpl (bytesMergeExactRawSpecGen A lim errStack reqCap)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp_align =>
    reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMergeExactRawSpecGen, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hpreB, hm⟩ := hpre
  obtain ⟨hw0, hx1, hx2, hbs_len, hcapOk, hfits⟩ := bmPreBoundBudget_elim hpreB
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hde_exit := fun (w : BitVec 64) (hw : KindNoHeap w) {s : State}
      (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue_decodeErrorFrom_placed_gen _ M A lim H errStack reqCap hbnd hdef x st s0 s R
      w hw hmerge hfits
  have h0e0_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hwt : x.wt = .lengthDelimited)
      (hvar : decodeVarint x.bs = some (len, rest0)) =>
    @phase2_from_0x0e0_export_placed_gen _ M A lim H hStack errStack reqCap hbnd hres_le
      hdef hmc hshim halloc hBytesFromVec hReserve
      hVtableDrop x st s0 s R len rest0 hwt hvar hbs_len hcapOk hfits
  have h074_exit := fun {s : State} (hwt : x.wt = .lengthDelimited) (hne : x.bs ≠ []) =>
    @phase1_from_0x074_placed_gen _ M A lim H hStack errStack reqCap hbnd hres_le
      hdef hmc hshim halloc hVarintSlow hVarintSlice
      hBytesFromVec hReserve hVtableDrop x st s0 s R hwt hne hbs_len hcapOk hfits
  clear hVarintSlow hVarintSlice hBytesFromVec hReserve hVtableDrop
  suffices hwp : _ by
    obtain ⟨sf, hsteps, hout⟩ := SepWPp.to_subroutineOutcome_exact_placed_gen hsp_align hm hL hwp
    exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  rw [stackAt_bytesMergeGen_entry s0.sp errStack hbnd]
  refine SepWPp.weaken_pre (P' := cells (s0.sp - 64#64) 8 ∗
    (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool lim st s0 ∗
      stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWPp.unfold_cells_64 fun c0 c1 c2 c3 c4 c5 c6 c7 => ?_
  by_cases hwt : x.wt = .lengthDelimited
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = false
      rw [truncate32_zeroExtend64_and_255_eq, hw0, hwt]
      decide
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_7).base + bv% (36))
    apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
      (mid := (blkPl_7).base + bv% (36))
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
      (hnext := ?_)
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    rcases hbs : x.bs with _ | ⟨b0, bs'⟩
    · have hmerge : mergeBytes x.wt x.bs = none := by rw [hbs]; exact mergeBytes_nil
      dsimp only [sliceCursorAt]
      refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗ _)
        (Entails.of_eq (by sep_focus)) ?_
      refine SepWPp.unfold_memRegion_216 fun w216 => ?_
      apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (248))
      apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
        (mid := (blkPl_7).base + bv% (248))
      intro _m_strip2
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        fun _m_real2 _hnsp2 => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp2.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        (hnext := ?_)
      apply SepWP.fold (fold_slot_16 x.slot x.ptr 0#64) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hcl2 hro2
      refine SepWPp.weaken_pre ?_ (hde_exit 0x8000000000000001#64 (by simp [KindNoHeap]) hmerge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
        hcl2 hro2)
      rw [hbs]
      exact Entails.of_eq (by
        simp (config := { decide := true }) only [arm64_norm]
        sep_ac_rfl)
    · have hbs_ne : x.bs ≠ [] := by simp [hbs]
      have hbs_len' : (b0 :: bs').length < 2 ^ 63 := by simpa [hbs] using bmLenBound_lt63 hbs_len
      have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs').length).toNat = (b0 :: bs').length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hlen_ne0 : (BitVec.ofNat 64 (b0 :: bs').length == 0#64) = false := by
        apply beq_false_of_ne
        intro h
        have h2 := congrArg BitVec.toNat h
        rw [hlen_toNat] at h2
        exact absurd h2 (by simp)
      dsimp only [sliceCursorAt]
      rw [pointsToBytes_cons]
      by_cases hb0 : (b0.signExtend 64).getLsbD 63 = false
      · apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (64))
        wp_steps
        refine ProofLib.SepWP.transport_budgetPool (A := A) (lim := lim) (st := st) ?_ (hnext := ?_)
        · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        intro hcl2 hro2
        have hvar : decodeVarint x.bs = some (b0.signExtend 64, bs') := by
          rw [hbs]
          exact decodeVarint_cons_of_signExtend_63_false hb0
        apply SepWPp.bm_of_sepWP_lscl hcl2 hro2 (mid := (blkPl_7).base + bv% (224))
        apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
          (mid := (blkPl_7).base + bv% (224))
        intro _m_strip2
        wp_steps
        refine SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
          fun _m_real2 _hnsp2 => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp2.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
          (hnext := ?_)
        apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + 1#64)) ∗
            ((x.slot + 8#64) ↦₆₄ (BitVec.ofNat 64 (b0 :: bs').length - 1#64)) ∗
            (x.ptr ↦₈ b0) ∗ ((x.ptr + 1#64) ↦ₛ bs') ⊢
            sliceCursorAfter x.slot x.ptr x.bs bs' from by
          rw [hbs]
          exact fold_sliceCursorAfter_cons x.slot x.ptr b0 bs') (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        intro hcl3 hro3
        refine SepWPp.weaken_pre ?_ (h0e0_exit (b0.signExtend 64) bs' hwt hvar
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
          hcl3 hro3
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        exact Entails.of_eq (by sep_ac_rfl)
      · have hb0_eq : (b0.signExtend 64).getLsbD 63 = true :=
          Bool.eq_true_of_not_eq_false hb0
        apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (116))
        wp_steps
        refine ProofLib.SepWP.transport_budgetPool (A := A) (lim := lim) (st := st) ?_ (hnext := ?_)
        · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        intro hcl2 hro2
        apply SepWPp.fold (T' := sliceCursorAt x.slot x.ptr x.bs)
          (show (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bs').length) ∗
              (x.ptr ↦₈ b0) ∗ ((x.ptr + 1#64) ↦ₛ bs') ⊢
              sliceCursorAt x.slot x.ptr x.bs from by
            unfold sliceCursorAt
            rw [hbs, pointsToBytes_cons]
            exact Entails.of_eq (by sep_ac_rfl)) (by sep_focus)
        refine SepWPp.weaken_pre ?_ (h074_exit hwt hbs_ne
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
          hcl2 hro2
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hbs])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        exact Entails.of_eq (by sep_ac_rfl)
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = true
      rw [truncate32_zeroExtend64_and_255_eq, hw0]
      cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_ne_lengthDelimited hwt
    dsimp only [sliceCursorAt]
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (((s0.sp - 64#64) ↦₆₄ c0) ∗ ((s0.sp - 56#64) ↦₆₄ c1) ∗
        ((s0.sp - 48#64) ↦₆₄ c2) ∗ ((s0.sp - 40#64) ↦₆₄ c3) ∗
        ((s0.sp - 32#64) ↦₆₄ c4) ∗ ((s0.sp - 24#64) ↦₆₄ c5) ∗
        ((s0.sp - 16#64) ↦₆₄ c6) ∗ ((s0.sp - 8#64) ↦₆₄ c7) ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool lim st s0 ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104)) (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216_invalidWireType fun w0_216 b0_216 b1_216 => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_7).base + bv% (248))
    apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
      (mid := (blkPl_7).base + bv% (248))
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
      (hnext := ?_)
    apply SepWP.fold (fold_memRegion_40_bytes (s0.sp - 216#64)
      (BitVec.ofNat 8 x.wt.toNat) 2#8) (by sep_focus)
    apply SepWP.fold (fold_slot_16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.weaken_pre ?_ (hde_exit 0x8000000000000006#64 (by simp [KindNoHeap]) hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
      hcl1 hro1)
    exact Entails.of_eq (by
      dsimp only [savedRegsStack]
      simp (config := { decide := true }) only [arm64_norm]
      sep_ac_rfl)

theorem bytes_merge_placed_ok_of_contracts_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim errStack)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (bmShimSpecGen errStack)))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false hStack)))
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowBudgetSpecWithStack M A lim (64 + errStack))))
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecBMGen A lim errStack)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack M A lim (hStack + 48))))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim hStack tmpPtr v v.length))) :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (blkPl_7).base
      (withLsCodeRoLoaded lsmpl (bytesMergeRawSpecGen A lim errStack reqCap)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp_align => ?_
  refine (bytes_merge_placed_ok_of_contracts_exact_gen hbnd hres_le hdef hmc hshim halloc
    hVarintSlow hVarintSlice hBytesFromVec hReserve hVtableDrop).mono_outcome
    (x, st) R s0 hpc hrun hpre hsp_align fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · exact Or.inl ⟨hret, hcc,
      Satisfies.mono
        (sepConj_mono_left (bytesMergeExactRawSpecGen_post_entails A lim errStack reqCap x st s0 sf))
        hpost⟩
  · exact Or.inr hrest

theorem bytes_merge_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen decodeErrorHookStack)))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (bmShimSpecGen decodeErrorHookStack)))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpec M A lim false)))
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowBudgetSpec M A lim)))
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpec A lim)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpec M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length))) :
    BytesMergePlacedOk A lim H :=
  bytes_merge_placed_ok_of_contracts_gen (hStack := allocHookStack) (errStack := decodeErrorHookStack)
    (reqCap := true) (by decide) (by decide) hdef hmc hshim halloc hVarintSlow hVarintSlice
    hBytesFromVec hReserve (fun tmpPtr v => bytesVtableDropSpecBMGen_of_spec (hVtableDrop tmpPtr v))

theorem bytes_merge_placed_ok_of_contracts_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl session2MemcpyBudgetSpecBMX))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl session2ShimBudgetSpecBMX))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)))
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowBudgetSpecWithStack M A lim (64 + decodeErrorHookStackX))))
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecX A lim)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecX M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecX M A lim tmpPtr v v.length))) :
    BytesMergePlacedOkX A lim H :=
  bytes_merge_placed_ok_of_contracts_gen (hStack := extHookStack) (errStack := decodeErrorHookStackX)
    (reqCap := true) (by decide) (by decide) hdef hmc hshim halloc hVarintSlow hVarintSlice
    hBytesFromVec hReserve (fun tmpPtr v => bytesVtableDropSpecBMGen_of_spec_x (hVtableDrop tmpPtr v))

theorem bytes_merge_placed_ok_of_contracts_exact_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl session2MemcpyBudgetSpecBMX))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl session2ShimBudgetSpecBMX))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)))
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowBudgetSpecWithStack M A lim (64 + decodeErrorHookStackX))))
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecX A lim)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecX M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecX M A lim tmpPtr v v.length))) :
    BytesMergeExactPlacedOkX A lim H :=
  bytes_merge_placed_ok_of_contracts_exact_gen (hStack := extHookStack)
    (errStack := decodeErrorHookStackX) (reqCap := true) (by decide) (by decide)
    hdef hmc hshim halloc hVarintSlow hVarintSlice hBytesFromVec hReserve
    (fun tmpPtr v => bytesVtableDropSpecBMGen_of_spec_x (hVtableDrop tmpPtr v))

end LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1Budget
