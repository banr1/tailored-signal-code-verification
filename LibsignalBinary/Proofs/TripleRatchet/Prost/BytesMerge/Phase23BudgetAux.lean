/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.Basic
import ProofLib.SepLogic.WP

/-!
# Budget-Threaded `prost::encoding::bytes::merge::<Vec<u8>>` Phase 3 and Phase 2 Suffixes

Allocator/shim/`memcpy` contract-lifting lemmas and `[LibsignalPlacement]` `RustCliAllocBudget`
proofs of Phase 3 (`phase3_from_0x294_placed_gen`) and the Phase 2 suffixes
(`phase2_from_0x23c_placed_gen`, `phase2_from_0x168_nonempty_placed_gen`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv FitsEvents
   RustLayoutOk VmPreserved AllocCallPreserved NullAllowed
   rustAllocEvents rustDeallocEvents rustReallocEvents
   not_nullAllowed_of_fitsAllocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocBudgetSpecWithStack rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
  (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveCall reserveCap doReserveEvents DoReserveEnv fitsEnv_doReserve_iff
   doReserveSpecWithStack noAllocShimBudgetSpec framelessMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
  (bytesDropEvents bytesFromVecPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (withStack subroutine_ok_withStack_of_subroutine_ok)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (doReserveClearEvents bytesMergeEventsCore BytesMergeEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
  (MergeExactPostGen MergeExactPanicGen bmNextCap bmShimSpecGen bmMemcpySpecGen
   bytesVtableDropSpecBMGen phase3_from_0x2b4_placed_gen)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks LibsignalCodeLoaded LibsignalRoLoaded
   lsmpl blkPC_7 blkPl_7 blkLib_eq_7 withLsCl)
open CryptoVerification.RustHeap
  (vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarintAux mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (bytesFromVecStack bytesPtr bytesData bytesBoxU8Buf
   bytesPlacedVtable bytesPlacedAt bytesPlacedDropFnAddr)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost SepWPp.bm_call_frame_lscl SepWPp.bm_of_sepWP_lscl
   sliceCursorAfter bmSliceStack bmTotalStack
   savedRegsStack bm_HighCalleeSaved bmCapCond bmCapCond_mono bmCapCond_after_reserve
   bmLenBound bmLenBound_lt63 bm_reserveCap_bound
   spAligned_sub_224 stackAt_sliceGen_split subroutine_ok_withLsCl_of_plain
   bm_vecU8At_eq_header_sep_buf fold_vecU8At_clear memRegion_104_fold
   bytesMutDataWord bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
   bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero
   bm_vecU8Buf fold_vecU8At_sp136 unfold_vecHeader_sp136 unfold_bytesPlacedAt_sp112
   mergeBytes_lengthDelimited_ok sliceCursorAfter_split_copy
   sliceCursorAfter_advance_fold fold_vecU8Buf_nonempty
   bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32 bitvec_getLsbD_63_of_lt32
   bitvec_sub_self_64 bitvec_if_zero_ult_self)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero

/-! ## Pure and contract-lifting helpers -/

private theorem decodeVarintAux_length_lt (i : Nat) (acc : BitVec 64)
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
        simp; omega

theorem mergeBytes_length_sum {wt : WireType} {bs v rest : List (BitVec 8)}
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
      have h1 : rest0.length < bs.length := decodeVarintAux_length_lt 0 0 bs rest0 len hvar
      have h2 : (rest0.take len.toNat).length + (rest0.drop len.toNat).length = rest0.length := by
        rw [← List.length_append, List.take_append_drop]
      omega

theorem doReserveEvents_eq_clear (valPtr valCap valBuf : BitVec 64) (vLen : Nat)
    (hcap_lt : valCap.toNat < vLen) :
    doReserveEvents { v := valPtr, cap := valCap, ptr := valBuf, bs := [], additional := vLen } =
      doReserveClearEvents valCap.toNat vLen := by
  have hnle : ¬ vLen ≤ valCap.toNat := by omega
  unfold doReserveEvents doReserveClearEvents
  simp only [List.length_nil, hnle, ↓reduceIte]
  by_cases hcap0 : valCap = 0#64
  · subst hcap0; rfl
  · have hcap_nat : valCap.toNat ≠ 0 := fun h0 => hcap0 (BitVec.eq_of_toNat_eq h0)
    simp only [hcap0, hcap_nat, ↓reduceIte]

theorem doReserveClearEvents_of_le {cap vLen : Nat} (hle : vLen ≤ cap) :
    doReserveClearEvents cap vLen = [] := by
  simp [doReserveClearEvents, hle]

theorem subroutine_ok_withLsCl_allocNoOomWithStack_of_budgetWithStack [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (h : subroutine_ok prog entry
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim zeroed stk))) :
    subroutine_ok prog entry
      (withLsCl lsmpl (rustCliAllocNoOomSpecWithStack M A lim zeroed stk)) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨size, align, st⟩ R s0 hpc hrun hpre hal _
  dsimp only [withLsCl, rustCliAllocNoOomSpecWithStack] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlay, hFit, hlr⟩, hrest⟩
  have hpre_b : s0.mem ⊨
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim zeroed stk)).pre
        (size, align, st) s0 ∗ R := by
    dsimp only [withLsCl, rustCliAllocBudgetSpecWithStack]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay, hlr⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (size, align, st) R s0 hpc hrun hpre_b hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl, rustCliAllocBudgetSpecWithStack] at hpost
    by_cases hnull : sf.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hna : NullAllowed size align := by
        have hEq :
            (⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗
              (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
                stackAt s0.sp stk ∗ ⌜NullAllowed size align⌝)) ∗ R =
            ⌜NullAllowed size align⌝ ∗
              (⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗ ⌜AllocCallPreserved s0 sf⌝ ∗
                A.pool lim st sf ∗ stackAt s0.sp stk ∗ R) := by sep_ac_rfl
        rw [hEq, satisfies_pure_sepConj] at hpost
        exact hpost.1
      exact False.elim (not_nullAllowed_of_fitsAllocEvents hlay hFit hna)
    · simp only [hnull, ↓reduceIte] at hpost
      dsimp only [withLsCl, rustCliAllocNoOomSpecWithStack]
      have hEq1 :
          (⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗
            (⌜AllocCallPreserved s0 sf⌝ ∗
              A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt s0.sp stk ∗
              (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) size align ∗
                (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
                 else memRegion (sf.readReg64 .x0) size)))) ∗ R =
          ⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗
            (⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
                (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
                  stackAt s0.sp stk ∗ A.live (sf.readReg64 .x0) size align ∗
                  (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
                   else memRegion (sf.readReg64 .x0) size) ∗ R))) := by sep_ac_rfl
      rw [hEq1, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hcl_f, hpost⟩
      rw [satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hacp, hpost⟩
      rw [satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hal_f, hspRest⟩
      have hne0 : sf.readReg64 .x0 ≠ 0#64 := hnull
      have hEq2 :
          (⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗
            (⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
                (sf.readReg64 .x0).toNat % align = 0⌝ ∗
              A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt s0.sp stk ∗ A.live (sf.readReg64 .x0) size align ∗
              (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
               else memRegion (sf.readReg64 .x0) size))) ∗ R =
          ⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗
            (⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
                (sf.readReg64 .x0).toNat % align = 0⌝ ∗
              (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
                stackAt s0.sp stk ∗ A.live (sf.readReg64 .x0) size align ∗
                (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
                 else memRegion (sf.readReg64 .x0) size) ∗ R)) := by sep_ac_rfl
      rw [hEq2, satisfies_pure_sepConj]
      refine ⟨hcl_f, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hacp, hne0, hal_f⟩, hspRest⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · dsimp only [withLsCl, rustCliAllocBudgetSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hFit)

theorem bmShim_placed_of_noAllocShim [LibsignalPlacement] {prog : Program} {addr : BitVec 64}
    {errStack : Nat} (hshim : subroutine_ok prog addr noAllocShimBudgetSpec) :
    subroutine_ok prog addr (withLsCl lsmpl (bmShimSpecGen errStack)) := by
  apply subroutine_ok_withLsCl_of_plain
  have h := subroutine_ok_withStack_of_subroutine_ok hshim (bmSliceStack errStack)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack noAllocShimBudgetSpec (bmSliceStack errStack)).pre x s0 ∗ R := by
    dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
      noAllocShimBudgetSpec, bmShimSpecGen] at hpre ⊢
    simpa only [pure_true, emp_sepConj, sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex | hoom)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
      noAllocShimBudgetSpec, bmShimSpecGen] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem bmMemcpy_placed_of_framelessBudget [LibsignalPlacement] {prog : Program} {addr : BitVec 64}
    {errStack : Nat} (hmc : subroutine_ok prog addr framelessMemcpyBudgetSpec) :
    subroutine_ok prog addr (withLsCl lsmpl (bmMemcpySpecGen errStack)) := by
  apply subroutine_ok_withLsCl_of_plain
  have h := subroutine_ok_withStack_of_subroutine_ok hmc (bmSliceStack errStack)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨
      (withStack framelessMemcpyBudgetSpec (bmSliceStack errStack)).pre x s0 ∗ R := by
    dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
      framelessMemcpyBudgetSpec, bmMemcpySpecGen] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex | hoom)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
      framelessMemcpyBudgetSpec, bmMemcpySpecGen] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-! ## Relocatable `[LibsignalPlacement]` Phase 3 and Phase 2 suffixes -/

theorem phase3_from_0x294_placed_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack M A lim (hStack + 48))))
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim hStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hfits_res : FitsEvents M lim st_cur (doReserveClearEvents x.valCap.toNat v.length))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧
      M.stepEvents (doReserveClearEvents x.valCap.toNat v.length ++ bytesDropEvents v) st_cur =
        M.stepEvents evs st)
    (hv_len : v.length < 2 ^ 63)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_7).base + 660#64)
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
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hsum : 1 + v.length + rest.length ≤ x.bs.length := mergeBytes_length_sum hmerge
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp3 := fun (st_next : M.σ) (cap' ptr' : BitVec 64) {s : State}
      (hevs' : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (bytesDropEvents v) st_next = M.stepEvents evs st)
      (hcapOk' : bmCapCond reqCap cap' rest.length)
      (hcapEq : cap'.toNat = bmNextCap x.valCap.toNat v.length)
      (hcap' : v.length ≤ cap'.toNat) =>
    @phase3_from_0x2b4_placed_gen _ M A lim H hStack errStack reqCap hbnd (by omega) hmc
      x st st_next s0 s R v rest tmpPtr cap' ptr'
      hVtableDrop hmerge hevs' hcapOk' hcapEq hcap' hv_len
  rw [bm_vecU8At_eq_header_sep_buf A.repAlloc x.valPtr x.valCap x.valBuf x.valBs]
  dsimp only [vecHeader] at hpc hReserve hp3 ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro
    (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true
      then (blkPl_7).base + bv% (800) else (blkPl_7).base + bv% (676))
  apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
    (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true
      then (blkPl_7).base + bv% (800) else (blkPl_7).base + bv% (676))
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
      bm_reserveCap_bound reqCap hcapOk hcap_lt hsum hbs_len
    have hcapOk' :
        bmCapCond reqCap (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) rest.length :=
      bmCapCond_after_reserve hcapOk hcap_lt hsum hbs63
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
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := lsmpl.base 13)
    wp_steps
    refine ProofLib.SepWP.transport_budgetPool (A := A) (lim := lim) (st := st_cur) ?_ (hnext := ?_)
    · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    rw [stackAt_sliceGen_split s0.sp errStack ((hStack + 48) + 64) hres_le hbnd]
    refine SepWPp.bm_call_frame_lscl
      (x := (rc, st_cur))
      (T := vecU8At A.repAlloc x.valPtr x.valCap x.valBuf [] ∗
        A.pool lim st_cur _ ∗ stackAt (s0.sp - 224#64) ((hStack + 48) + 64))
      hReserve hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [doReserveSpecWithStack, arm64_norm, hsp, hx19, hx20]; rfl)
      (by exact ⟨rfl, rfl, hlen_toNat, hnewCap_bound, hfits_rc⟩)
      (by sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [doReserveSpecWithStack] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
    intro sf_res hpcf hrunf hspf hcsf hclf hrof
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
    obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
    dsimp only [doReserveSpecWithStack, rc, List.length_nil]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun htr => ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptr' => ?_
    rw [bm_vecU8At_eq_header_sep_buf A.repAlloc x.valPtr
      (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' []]
    dsimp only [vecHeader, List.length_nil]
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (692))
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
        (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' hevs' hcapOk'
        (by
          have hnle : ¬ v.length ≤ x.valCap.toNat := by omega
          dsimp [bmNextCap, reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap] at hnewCap_bound ⊢
          simp only [hnle, ↓reduceIte]
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
        hnewCap_ge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
          h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
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
      rw [stackAt_sliceGen_split s0.sp errStack ((hStack + 48) + 64) hres_le hbnd]
      sep_ac_rfl)
  · have hult_eq : x.valCap.ult (BitVec.ofNat 64 v.length) = false :=
      Bool.eq_false_iff.mpr hult
    simp only [hult_eq, Bool.false_eq_true, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_ge : v.length ≤ x.valCap.toNat := by
      simp [BitVec.ult, hlen_toNat] at hult_eq
      exact hult_eq
    have hcapOk' : bmCapCond reqCap x.valCap rest.length :=
      bmCapCond_mono hcapOk (by omega)
    have hevs' : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st := by
      rwa [doReserveClearEvents_of_le hcap_ge, List.nil_append] at hevs
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (692))
    wp_steps
    refine ProofLib.SepWP.transport_budgetPool (A := A) (lim := lim) (st := st_cur) ?_ (hnext := ?_)
    · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hp3 st_cur x.valCap x.valBuf hevs' hcapOk' (by simp [bmNextCap, hcap_ge]) hcap_ge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by obtain ⟨h25, h26, h27, h28⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
        hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24]))

theorem phase2_from_0x23c_placed_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack M A lim (hStack + 48))))
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim hStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hfits_res : FitsEvents M lim st_cur (doReserveClearEvents x.valCap.toNat v.length))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧
      M.stepEvents (doReserveClearEvents x.valCap.toNat v.length ++ bytesDropEvents v) st_cur =
        M.stepEvents evs st)
    (hv_len : v.length < 2 ^ 63)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_7).base + 572#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 v.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = tmpPtr)
    (hx22 : s.readReg64 .x22 = bytesMutDataWord (BitVec.ofNat 64 v.length))
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        bm_vecU8Buf A.repAlloc (BitVec.ofNat 64 v.length) tmpPtr v ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp3 := fun {s : State} =>
    @phase3_from_0x294_placed_gen _ M A lim H hStack errStack reqCap hbnd hres_le hmc hReserve
      x st st_cur s0 s R v rest tmpPtr hVtableDrop hmerge hfits_res hevs hv_len hbs_len hcapOk
  clear hReserve
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 250)
  apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
    (mid := lsmpl.base 250)
  intro _m_strip
  wp_steps
  refine SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
      bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
    (hnext := ?_)
  apply SepWP.fold (fold_vecU8At_sp136 A.repAlloc s0.sp (BitVec.ofNat 64 v.length) tmpPtr v)
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
      bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  rw [stackAt_sliceGen_split s0.sp errStack bytesFromVecStack
    (by dsimp [bmSliceStack, bytesFromVecStack]; omega) hbnd]
  refine SepWPp.bm_call_frame_lscl
    (x := (s0.sp - 136#64, s0.sp - 112#64, BitVec.ofNat 64 v.length, tmpPtr, v))
    (T := vecU8At A.repAlloc (s0.sp - 136#64) (BitVec.ofNat 64 v.length) tmpPtr v ∗
      memRegion (s0.sp - 112#64) 32 ∗
      stackAt (s0.sp - 224#64) bytesFromVecStack)
    hBytesFromVec hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
      bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bytesFromVecPlacedSpec, arm64_norm, hsp, hx29])
    hlen_toNat
    (by sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm; dsimp only [bytesFromVecPlacedSpec] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_bfv hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx19, hx20, hx21, hx22, hx29,
    bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  dsimp only [bytesFromVecPlacedSpec]
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr, hvm_bfv⟩ => ?_
  have hpool_bfv : A.pool lim st_cur (_ : State) = A.pool lim st_cur sf_bfv :=
    A.pool_of_vmPreserved hvm_bfv.symm
  rw [hpool_bfv]
  rw [unfold_vecHeader_sp136, unfold_bytesPlacedAt_sp112]
  apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (660))
  apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
    (mid := (blkPl_7).base + bv% (660))
  intro _m_strip2
  wp_steps
  refine SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    fun _m_real2 _hnsp2 => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp2.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
    (hnext := ?_)
  apply SepWP.fold (memRegion_104_fold s0.sp w0 w1 w2 w3
    (BitVec.ofNat 64 v.length) tmpPtr (BitVec.ofNat 64 v.length)
    (bytesPlacedVtable tmpPtr v.length) (bytesPtr tmpPtr v.length)
    (BitVec.ofNat 64 v.length) (bytesData tmpPtr v.length) 0#64) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  intro hcl2 hro2
  refine SepWPp.weaken_pre (P' :=
    vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      bytesBoxU8Buf A.repAlloc tmpPtr v ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur _ ∗
      stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104 ∗
      savedRegsStack s0.sp s0)
    (Entails.of_eq (by
      simp (config := { decide := true }) only [arm64_norm, hsp]
      rw [stackAt_sliceGen_split s0.sp errStack bytesFromVecStack
        (by dsimp [bmSliceStack, bytesFromVecStack]; omega) hbnd]
      sep_ac_rfl)) ?_
  exact hp3
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
    hsp_align
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
    (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
      h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
    hcl2 hro2
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])

theorem phase2_from_0x168_nonempty_placed_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack M A lim (hStack + 48))))
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {pfx rest0 : List (BitVec 8)} {b0 : BitVec 8} {v' : List (BitVec 8)}
    {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (bytesPlacedDropFnAddr tmpPtr (b0 :: v').length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim hStack tmpPtr (b0 :: v') (b0 :: v').length)))
    (hvar : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
    (hpfx : x.bs = pfx ++ rest0)
    (hle : (b0 :: v').length ≤ rest0.length)
    (hv_take : rest0.take (b0 :: v').length = b0 :: v')
    (hwt : x.wt = .lengthDelimited)
    (hfits_res : FitsEvents M lim st_cur (doReserveClearEvents x.valCap.toNat (b0 :: v').length))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧
      M.stepEvents (doReserveClearEvents x.valCap.toNat (b0 :: v').length ++
        bytesDropEvents (b0 :: v')) st_cur = M.stepEvents evs st)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (htmp_ne : tmpPtr ≠ 0#64)
    (hpc : s.pc = (blkPl_7).base + 360#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (b0 :: v').length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 rest0.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx21 : s.readReg64 .x21 = tmpPtr)
    (hx24 : s.readReg64 .x24 = x.slot)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        A.repAlloc.live tmpPtr (b0 :: v').length 1 ∗ memRegion tmpPtr (b0 :: v').length ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  set v := b0 :: v'
  have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hv_len : v.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmin_v : (if (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true
      then BitVec.ofNat 64 v.length else BitVec.ofNat 64 rest0.length) = BitVec.ofNat 64 v.length := by
    by_cases hlt : v.length < rest0.length
    · have hult : (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true := by
        simp [BitVec.ult, hlen_toNat, hrest0_toNat, hlt]
      simp [hult]
    · have heq : rest0.length = v.length := by omega
      simp [heq]
  have hrest0_ult_v : (BitVec.ofNat 64 rest0.length).ult (BitVec.ofNat 64 v.length) = false := by
    simp [BitVec.ult, hlen_toNat, hrest0_toNat, hle]
  have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
    apply beq_false_of_ne
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [hlen_toNat] at h2
    exact absurd h2 (by dsimp [v]; omega)
  have hmerge : mergeBytes x.wt x.bs = some (v, rest0.drop v.length) := by
    have hm := mergeBytes_lengthDelimited_ok hwt hvar (by rw [hlen_toNat]; exact hle)
    rwa [hlen_toNat, hv_take] at hm
  have hp2 := fun {s : State} =>
    @phase2_from_0x23c_placed_gen _ M A lim H hStack errStack reqCap hbnd hres_le hmc
      hBytesFromVec hReserve x st st_cur s0 s R
      v (rest0.drop v.length) tmpPtr tmpPtr (BitVec.ofNat 64 v.length) (BitVec.ofNat 64 v.length)
      (1#64 ||| (if (64#64 - BitVec.ofNat 64 (countLeadingZeros (BitVec.ofNat 64 v.length >>> 10))).ult 7#64 = true
        then 64#64 - BitVec.ofNat 64 (countLeadingZeros (BitVec.ofNat 64 v.length >>> 10)) else 7#64) <<< 2)
      w4 w5 w6 w80 hVtableDrop hmerge hfits_res hevs hv_len hbs_len hcapOk
  clear hBytesFromVec hReserve
  rw [sliceCursorAfter_split_copy x.slot x.ptr x.bs pfx rest0 v.length hpfx hle]
  rw [hv_take]
  have hadv := sliceCursorAfter_advance_fold x.slot x.ptr x.bs pfx rest0 v.length hpfx hle hbs63
  dsimp only at hadv
  rw [hv_take] at hadv
  clear hpfx
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_7).ρ "memcpy")
  apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
    (mid := (blkPl_7).ρ "memcpy")
  intro _m_strip
  wp_steps
  refine SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
    (hnext := ?_)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  refine SepWPp.bm_call_frame_lscl
    (x := (tmpPtr, x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length), v))
    (T := memRegion tmpPtr v.length ∗ ((x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)) ↦ₛ v) ∗
      stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    hmc hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bmMemcpySpecGen, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, hlen_toNat, and_self])
    (by sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm; dsimp only [bmMemcpySpecGen] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_mc hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx8, hx19, hx21, hx24, hx29, hmin_v] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  simp (config := { decide := true }) only [bmMemcpySpecGen, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨_, htr, hvm_mc⟩ => ?_
  have hpool_mc : A.pool lim st_cur (_ : State) = A.pool lim st_cur sf_mc :=
    A.pool_of_vmPreserved hvm_mc.symm
  rw [hpool_mc]
  apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (572))
  apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
    (mid := (blkPl_7).base + bv% (572))
  intro _m_strip2
  wp_steps
  refine SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    fun _m_real2 _hnsp2 => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp2.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
    (hnext := ?_)
  have hfv := fold_vecU8Buf_nonempty A.repAlloc tmpPtr v hpos hv_len htmp_ne
  dsimp only [RustCliAllocBudget.repAlloc] at hfv
  apply SepWP.fold hfv (by sep_focus)
  apply SepWP.fold hadv (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  intro hcl2 hro2
  refine SepWPp.weaken_pre ?_
    (hp2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
        h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [bytesMutDataWord, wp_norm, arm64_norm, h22f,
        ProofLib.ofNat_countLeadingZeros64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))
  exact Entails.of_eq (by simp only [ProofLib.ofNat_countLeadingZeros64]; sep_ac_rfl)

end LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux
