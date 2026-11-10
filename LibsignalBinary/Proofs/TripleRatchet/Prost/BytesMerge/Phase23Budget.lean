/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.Basic
import ProofLib.SepLogic.WP

/-!
# Budget-Threaded Relocatable `prost::encoding::bytes::merge::<Vec<u8>>` Phases 2 and 3

Proves `phase2_from_0x0e0_placed_gen` under `RustCliAllocBudget` and `[LibsignalPlacement]`
and re-exports the Phase 2/3 suffix lemmas from `Phase23BudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23Budget

export LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux
  (phase3_from_0x294_placed_gen phase2_from_0x23c_placed_gen
   phase2_from_0x168_nonempty_placed_gen)

open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux
  (mergeBytes_length_sum doReserveEvents_eq_clear doReserveClearEvents_of_le
   subroutine_ok_withLsCl_allocNoOomWithStack_of_budgetWithStack
   bmShim_placed_of_noAllocShim bmMemcpy_placed_of_framelessBudget)

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv FitsEvents
   RustLayoutOk VmPreserved AllocCallPreserved
   rustAllocEvents rustDeallocEvents fitsEvents_append)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocBudgetSpecWithStack rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpecWithStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
  (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
  (bytesDropEvents bytesFromVecPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (doReserveClearEvents bytesMergeEventsCore BytesMergeEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
  (MergeExactPostGen MergeExactPanicGen bmShimSpecGen bmMemcpySpecGen bytesVtableDropSpecBMGen
   epilogue_decodeErrorFrom_placed_gen)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks LibsignalCodeLoaded LibsignalRoLoaded
   lsmpl blkPC_7 blkPl_7 blkLib_eq_7 withLsCl
   lsRustNoAllocShimSym lsRustAllocSym)
open CryptoVerification.RustHeap
  (vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap bytesPlacedDropFnAddr)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost SepWPp.bm_call_frame_lscl SepWPp.bm_of_sepWP_lscl
   sliceCursorAfter bmSliceStack bmTotalStack
   savedRegsStack bm_HighCalleeSaved bmCapCond bmLenBound bmLenBound_lt63
   spAligned_sub_224 stackAt_sliceGen_split
   bytesMutDataWord bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
   bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero
   bm_decodeVarint_suffix mergeBytes_lengthDelimited_underflow mergeBytes_lengthDelimited_ok
   vecU8Buf_nil_one sliceCursorAfter_to_err
   SepWPp.unfold_memRegion_216 SepWPp.unfold_memRegion_168
   bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32 bitvec_getLsbD_63_of_lt32
   bitvec_sub_self_64 bitvec_if_zero_ult_self)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero

/-! ## Relocatable `[LibsignalPlacement]` Phase 2 entry -/

theorem phase2_from_0x0e0_placed_gen [LibsignalPlacement]
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
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited)
    (hvar : decodeVarint x.bs = some (len, rest0))
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hfits : FitsEnv M lim st (BytesMergeEnv x))
    (hpc : s.pc = (blkPl_7).base + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = len)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool lim st s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R) := by
  have halloc' := subroutine_ok_withLsCl_allocNoOomWithStack_of_budgetWithStack halloc
  clear halloc
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hde_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue_decodeErrorFrom_placed_gen _ M A lim H errStack reqCap hbnd hdef x st s0 s R
      0x8000000000000007#64 (by simp [KindNoHeap]) hmerge hfits
  have h23c_exit := fun (w4 w5 w6 w80 : BitVec 64) {s : State}
      (hmerge : mergeBytes x.wt x.bs = some ([], rest0))
      (hfits_res : FitsEvents M lim st (doReserveClearEvents x.valCap.toNat 0))
      (hevs : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (doReserveClearEvents x.valCap.toNat 0 ++ bytesDropEvents []) st =
          M.stepEvents evs st) =>
    @phase2_from_0x23c_placed_gen _ M A lim H hStack errStack reqCap hbnd hres_le hmc
      hBytesFromVec hReserve x st st s0 s R
      [] rest0 1#64 1#64 0#64 0#64 1#64 w4 w5 w6 w80 (hVtableDrop 1#64 [])
      hmerge hfits_res hevs (by decide) hbs_len hcapOk
  have h168_exit := fun (b0 : BitVec 8) (v' : List (BitVec 8)) (st_cur : M.σ)
      (tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64) {s : State}
      (hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
      (hle' : (b0 :: v').length ≤ rest0.length)
      (hv_take' : rest0.take (b0 :: v').length = b0 :: v')
      (hfits_res : FitsEvents M lim st_cur (doReserveClearEvents x.valCap.toNat (b0 :: v').length))
      (hevs : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (doReserveClearEvents x.valCap.toNat (b0 :: v').length ++
          bytesDropEvents (b0 :: v')) st_cur = M.stepEvents evs st)
      (htmp_ne : tmpPtr ≠ 0#64) =>
    @phase2_from_0x168_nonempty_placed_gen _ M A lim H hStack errStack reqCap hbnd hres_le hmc
      hBytesFromVec hReserve x st st_cur s0 s R
      pfx rest0 b0 v' tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 (hVtableDrop tmpPtr (b0 :: v'))
      hvar' hpfx hle' hv_take' hwt hfits_res hevs hbs_len hcapOk htmp_ne
  clear hBytesFromVec hReserve hVtableDrop
  dsimp only [sliceCursorAfter]
  apply SepWPp.bm_of_sepWP_lscl hcl hro
    (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true
      then (blkPl_7).base + bv% (280) else (blkPl_7).base + bv% (240))
  wp_steps
  refine ProofLib.SepWP.transport_budgetPool (A := A) (lim := lim) (st := st) ?_ (hnext := ?_)
  · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
      ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
      sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  by_cases hule : len.ule (BitVec.ofNat 64 rest0.length) = false
  · simp only [hule, Bool.false_eq_true, ↓reduceIte] at hcl1 hro1 ⊢
    have hlt : rest0.length < len.toNat := by simp [BitVec.ule, hrest0_toNat] at hule; omega
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_lengthDelimited_underflow hwt hvar hlt
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool lim st _ ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216 fun w216 => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (248))
    apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
      (mid := (blkPl_7).base + bv% (248))
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
      (hnext := ?_)
    apply SepWP.fold (sliceCursorAfter_to_err x.slot x.ptr x.bs rest0) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (hde_exit hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by obtain ⟨h25, h26, h27, h28⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
      hcl2 hro2)
    exact Entails.of_eq (by
      simp (config := { decide := true }) only [arm64_norm, hsp,
        RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
        RustCliAllocBudget.pool_writeReg64]
      sep_ac_rfl)
  · have hule_eq : len.ule (BitVec.ofNat 64 rest0.length) = true :=
      Bool.eq_true_of_not_eq_false hule
    simp only [hule_eq, ↓reduceIte] at hcl1 hro1 ⊢
    have hle : len.toNat ≤ rest0.length := by simpa [BitVec.ule, hrest0_toNat] using hule_eq
    have hlen_lt32 : len.toNat < 2 ^ 63 := by omega
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 168#64) 104 ∗
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool lim st _ ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_168 fun w0 w1 w2 w3 w4 w5 w6 w80 => ?_
    rcases hv : rest0.take len.toNat with _ | ⟨b0, v'⟩
    · have hlen0 : len = 0#64 := by
        have hv_len0 : (rest0.take len.toNat).length = 0 := by rw [hv]; rfl
        rw [List.length_take_of_le hle] at hv_len0
        exact BitVec.eq_of_toNat_eq hv_len0
      have hmerge : mergeBytes x.wt x.bs = some ([], rest0) := by
        have hv_len0 : len.toNat = 0 := by rw [hlen0]; rfl
        have hdrop0 : rest0.drop len.toNat = rest0 := by rw [hv_len0]; rfl
        have hm := mergeBytes_lengthDelimited_ok hwt hvar hle
        rwa [hv, hdrop0] at hm
      clear hv
      have hfits_res0 : FitsEvents M lim st (doReserveClearEvents x.valCap.toNat 0) := by
        rw [doReserveClearEvents_of_le (Nat.zero_le _)]
        trivial
      have hevs0 : ∃ evs, BytesMergeEnv x evs ∧
          M.stepEvents (doReserveClearEvents x.valCap.toNat 0 ++ bytesDropEvents []) st =
            M.stepEvents evs st := by
        refine ⟨[], ?_, ?_⟩
        · simp [BytesMergeEnv, bytesMergeEventsCore, hmerge]
        · simp [doReserveClearEvents_of_le (Nat.zero_le _), bytesDropEvents]
      have hmin0 : (if (0#64).ult (BitVec.ofNat 64 rest0.length) = true
          then 0#64 else BitVec.ofNat 64 rest0.length) = 0#64 :=
        bitvec_if_zero_ult_self (BitVec.ofNat 64 rest0.length)
      dsimp only [sliceCursorAfter]
      rw [← emp_sepConj (((s0.sp - 168#64) ↦₆₄ w0) ∗ _)]
      apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (572))
      apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
        (mid := (blkPl_7).base + bv% (572))
      intro _m_strip
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp,
          hule_eq, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        (hnext := ?_)
      apply SepWP.fold (vecU8Buf_nil_one A.repAlloc) (by sep_focus)
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp,
          hule_eq, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hcl2 hro2
      refine SepWPp.weaken_pre ?_ (h23c_exit w4 w5 w6 w80 hmerge hfits_res0 hevs0
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp,
          hule_eq, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by obtain ⟨h25, h26, h27, h28⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
        hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0,
          bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0,
          bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, bytesMutDataWord_zero])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
      exact Entails.of_eq (by
        simp (config := { decide := true }) only [arm64_norm, hsp,
          RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
          RustCliAllocBudget.pool_writeReg64]
        sep_ac_rfl)
    · have hlen_v : len = BitVec.ofNat 64 (b0 :: v').length := by
        have hv_len_eq : (b0 :: v').length = len.toNat := by
          rw [← hv, List.length_take_of_le hle]
        rw [hv_len_eq, BitVec.ofNat_toNat]; rfl
      have hle' : (b0 :: v').length ≤ rest0.length := by
        have hv_len_eq : (b0 :: v').length = len.toNat := by
          rw [← hv, List.length_take_of_le hle]
        omega
      have hv_take' : rest0.take (b0 :: v').length = b0 :: v' := by
        have hv_len_eq : (b0 :: v').length = len.toNat := by
          rw [← hv, List.length_take_of_le hle]
        rw [hv_len_eq]; exact hv
      clear hv
      have hpos : 0 < (b0 :: v').length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
      have hv_len : (b0 :: v').length < 2 ^ 63 := by omega
      have hlen_toNat : (BitVec.ofNat 64 (b0 :: v').length).toNat = (b0 :: v').length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0) := by
        rwa [← hlen_v]
      have hmerge_v : mergeBytes x.wt x.bs = some (b0 :: v', rest0.drop (b0 :: v').length) := by
        have hm := mergeBytes_lengthDelimited_ok hwt hvar' (by rw [hlen_toNat]; exact hle')
        rwa [hlen_toNat, hv_take'] at hm
      let evs_all : List AllocEvent :=
        rustAllocEvents (b0 :: v').length 1 ++
          doReserveClearEvents x.valCap.toNat (b0 :: v').length ++
          rustDeallocEvents (b0 :: v').length 1
      have hevs_bm : BytesMergeEnv x evs_all := by
        have hne0 : (b0 :: v').length ≠ 0 := by simp
        simp only [BytesMergeEnv, bytesMergeEventsCore, hmerge_v, hne0, ↓reduceIte, evs_all]
      have hdrop_eq : bytesDropEvents (b0 :: v') = rustDeallocEvents (b0 :: v').length 1 := by
        simp [bytesDropEvents]
      have hfits_all : FitsEvents M lim st evs_all := hfits evs_all hevs_bm
      have hfits_split1 :
          FitsEvents M lim st (rustAllocEvents (b0 :: v').length 1) ∧
            FitsEvents M lim (M.stepEvents (rustAllocEvents (b0 :: v').length 1) st)
              (doReserveClearEvents x.valCap.toNat (b0 :: v').length ++
                rustDeallocEvents (b0 :: v').length 1) := by
        rw [← fitsEvents_append]
        simpa only [evs_all, List.append_assoc] using hfits_all
      have hfits_alloc : FitsEvents M lim st (rustAllocEvents (b0 :: v').length 1) :=
        hfits_split1.1
      have hfits_res :
          FitsEvents M lim (M.stepEvents (rustAllocEvents (b0 :: v').length 1) st)
            (doReserveClearEvents x.valCap.toNat (b0 :: v').length) :=
        ((fitsEvents_append M lim _ _ _).mp hfits_split1.2).1
      have hevs_after :
          ∃ evs, BytesMergeEnv x evs ∧
            M.stepEvents (doReserveClearEvents x.valCap.toNat (b0 :: v').length ++
              bytesDropEvents (b0 :: v'))
              (M.stepEvents (rustAllocEvents (b0 :: v').length 1) st) =
              M.stepEvents evs st := by
        refine ⟨evs_all, hevs_bm, ?_⟩
        rw [← M.stepEvents_append, hdrop_eq]
        simp only [evs_all, List.append_assoc]
      have hmsb : (BitVec.ofNat 64 (b0 :: v').length).getLsbD 63 = false :=
        bitvec_getLsbD_63_of_lt32 hv_len
      have hlen_ne : (BitVec.ofNat 64 (b0 :: v').length == 0#64) = false := by
        apply beq_false_of_ne
        intro h
        have h2 := congrArg BitVec.toNat h
        rw [hlen_toNat] at h2
        exact absurd h2 (by simp)
      apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).ρ lsRustNoAllocShimSym)
      apply sepWP_seg_ls_vm (Q := (blkPC_7).rebase (blkPl_7).base (hooksException H)) blkLib_eq_7
        (mid := (blkPl_7).ρ lsRustNoAllocShimSym)
      intro _m_strip
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp,
          hule_eq, hlen_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32,
          bitvec_msb_false_of_lt32, bitvec_getLsbD_63_of_lt32])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        (hnext := ?_)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp,
          hule_eq, hlen_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32,
          bitvec_msb_false_of_lt32, bitvec_getLsbD_63_of_lt32])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hcl2 hro2
      refine SepWPp.bm_call_frame_lscl (x := ())
        (T := stackAt (s0.sp - 224#64) (bmSliceStack errStack))
        hshim hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp,
          hule_eq, hlen_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32,
          bitvec_msb_false_of_lt32, bitvec_getLsbD_63_of_lt32])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
        (by simp (config := { decide := true }) only [bmShimSpecGen, arm64_norm, hsp])
        trivial (by sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (by intro _ _ hm; dsimp only [bmShimSpecGen] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
      intro sf_sh hpcf_sh hrunf_sh hspf_sh hcsf_sh hclf_sh hrof_sh
      obtain ⟨h19_sh, h20_sh, h21_sh, h22_sh, h23_sh, h24_sh, h25_sh, h26_sh, h27_sh, h28_sh, h29_sh⟩ := hcsf_sh
      simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx2, hx19, hx29, hlen_v] at hpcf_sh hspf_sh h19_sh h20_sh h21_sh h22_sh h23_sh h24_sh h25_sh h26_sh h27_sh h28_sh h29_sh
      simp (config := { decide := true }) only [bmShimSpecGen, arm64_norm, hsp]
      refine SepWPp.pure_elim fun ⟨htr_sh, hvm_sh⟩ => ?_
      have hpool_sh : A.pool lim st (_ : State) = A.pool lim st sf_sh :=
        A.pool_of_vmPreserved hvm_sh.symm
      rw [hpool_sh]
      apply SepWPp.bm_of_sepWP_lscl hclf_sh hrof_sh (mid := (blkPl_7).ρ lsRustAllocSym)
      wp_steps
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
      intro hcl3 hro3
      rw [stackAt_sliceGen_split s0.sp errStack hStack (by omega) hbnd]
      refine SepWPp.bm_call_frame_lscl (x := ((b0 :: v').length, 1, st))
        (T := A.pool lim st _ ∗ stackAt (s0.sp - 224#64) hStack)
        halloc' hcl3 hro3
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
        (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hspf_sh, hsp_align]) rfl
        (by simp (config := { decide := true }) only [rustCliAllocNoOomSpecWithStack, arm64_norm, hspf_sh, h21_sh]; rfl)
        (by
          refine ⟨?_, ⟨⟨hpos, ⟨0, rfl⟩, ?_⟩, by decide⟩, hfits_alloc, ?_⟩
          · simp (config := { decide := true }) only [arm64_norm, h21_sh, hlen_toNat]
          · simp only [List.length_cons] at hv_len ⊢; omega
          · simp only [wp_norm, arm64_norm, blkPl_7]
            apply lsRetAddr624_blockPlacement_base_add <;> decide)
        (by (conv => lhs; simp (config := { failIfUnchanged := false }) only [arm64_norm]); sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (by intro _ _ hm; dsimp only [rustCliAllocNoOomSpecWithStack] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
      intro sf_al hpcf_al hrunf_al hspf_al hcsf_al hclf_al hrof_al
      obtain ⟨h19_al, h20_al, h21_al, h22_al, h23_al, h24_al, h25_al, h26_al, h27_al, h28_al, h29_al⟩ := hcsf_al
      simp (config := { decide := true }) only [arm64_norm, hspf_sh, h19_sh, h21_sh, h24_sh, h29_sh] at hpcf_al hspf_al h19_al h20_al h21_al h22_al h23_al h24_al h25_al h26_al h27_al h28_al h29_al
      dsimp only [rustCliAllocNoOomSpecWithStack]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hacp_al, h0_64, _⟩ => ?_
      have htr_al : sf_al.trace = s0.trace := by
        have htr0 := hacp_al.2.1
        simp (config := { decide := true }) only [arm64_norm, htr_sh, htrace] at htr0
        exact htr0
      have h0_beq : (sf_al.readReg64 .x0 == 0#64) = false := beq_false_of_ne h0_64
      refine SepWPp.weaken_pre (P' :=
        ((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
          ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
          ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
          ((s0.sp - 120#64) ↦₆₄ w6) ∗
          memRegion (s0.sp - 112#64) 32 ∗
          ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
          A.repAlloc.live (sf_al.readReg64 .x0) (b0 :: v').length 1 ∗
          memRegion (sf_al.readReg64 .x0) (b0 :: v').length ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
          A.pool lim (M.stepEvents (rustAllocEvents (b0 :: v').length 1) st) sf_al ∗
          stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          savedRegsStack s0.sp s0)
        (Entails.of_eq (by
          dsimp only [RustCliAllocBudget.repAlloc]
          simp (config := { decide := true }) only [arm64_norm, hspf_sh]
          rw [stackAt_sliceGen_split s0.sp errStack hStack (by omega) hbnd]
          sep_ac_rfl)) ?_
      dsimp only [sliceCursorAfter]
      apply SepWPp.bm_of_sepWP_lscl hclf_al hrof_al (mid := (blkPl_7).base + bv% (360))
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
      intro hcl4 hro4
      obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
      refine SepWPp.weaken_pre ?_ (h168_exit b0 v'
        (M.stepEvents (rustAllocEvents (b0 :: v').length 1) st)
        (sf_al.readReg64 .x0) w0 w1 w2 w3 w4 w5 w6 w80
        hvar' hle' hv_take' hfits_res hevs_after h0_64
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf_al])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr_al])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
          h25_al, h26_al, h27_al, h28_al, h29_al, h25_sh, h26_sh, h27_sh, h28_sh, h29_sh,
          h25_0, h26_0, h27_0, h28_0, and_self])
        hcl4 hro4
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29_al]))
      exact Entails.of_eq (by
        simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
          RustCliAllocBudget.pool_writeReg64]
        sep_ac_rfl)

namespace BytesMergeFacts

theorem phase2_from_0x0e0_export_placed_gen [LibsignalPlacement]
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
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited)
    (hvar : decodeVarint x.bs = some (len, rest0))
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hfits : FitsEnv M lim st (BytesMergeEnv x))
    (hpc : s.pc = (blkPl_7).base + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = len)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool lim st s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R) :=
  phase2_from_0x0e0_placed_gen hbnd hres_le hdef hmc hshim halloc hBytesFromVec hReserve
    hVtableDrop hwt hvar hbs_len hcapOk hfits hpc hrun hsp hsp_align htrace hhigh hcl hro
    hx0 hx2 hx19 hx29

end BytesMergeFacts

end LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23Budget
