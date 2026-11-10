/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23PlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.Basic
import ProofLib.SepLogic.WP

/-!
# `prost::encoding::bytes::merge [local#3]` (Block `290`): Budget-Threaded Phase 2

Relocatable `[LibsignalPlacement]` verification of Phase 2 (`+0x094..+0x210`) for Block `290`
under `FitsEnv M lim st (BytesMergeEnv x)` (`RustCliAllocBudget M`), re-exporting epilogues and
Phase 3 from `Phase23PlacedBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23PlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23PlacedBudgetAux
  (epilogue3_err_0x07c_placed epilogue3_decodeErrorFrom_0x074_placed
   epilogue3_vtableDrop_0x254_placed phase3_from_0x230_placed phase3_from_0x210_placed)

abbrev MergePost :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23PlacedBudgetAux.MergePost
abbrev MergePanic :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23PlacedBudgetAux.MergePanic
abbrev bytesVtableDropSpecBM_of_spec :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23PlacedBudgetAux.bytesVtableDropSpecBM_of_spec

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   RustLayoutOk VmPreserved AllocCallPreserved
   rustAllocEvents rustDeallocEvents fitsEvents_append
   rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
  (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveSpec framelessMemcpyBudgetSpec noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
  (bytesDropEvents bytesFromVecPlacedSpec bytesVtableDropSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore doReserveClearEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
  (bmMemcpySpecGen bmShimSpecGen)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux
  (doReserveClearEvents_of_le subroutine_ok_withLsCl_allocNoOomWithStack_of_budgetWithStack
   bmShim_placed_of_noAllocShim bmMemcpy_placed_of_framelessBudget)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded lsmpl
   blkPC_290 blkPl_290 blkLib_eq_290 withLsCl
   lsRustNoAllocShimSym lsRustAllocSym)
open CryptoVerification.RustHeap
  (allocHookStack vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (bytesBoxU8Buf bytesData bytesFromVecStack bytesPlacedDropFnAddr
   bytesPlacedVtable bytesPtr decodeErrorHookStack)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost decodeVarintSliceStack
   SepWPp.bm_call_frame_lscl SepWPp.bm_of_sepWP_lscl
   SepWPp.unfold_memRegion_168 bmSliceStack bm_HighCalleeSaved bm_decodeVarint_suffix
   bm_vecU8Buf bytesMutDataWord bytesMutDataWord_zero bytesMutDataWord_bit0
   bytesMutDataWord_getLsbD_zero bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5
   bitvec_ult_zero bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32
   bitvec_getLsbD_63_of_lt32 bitvec_sub_self_64 bitvec_if_zero_ult_self
   fold_vecU8At_sp136 fold_vecU8Buf_nonempty memRegion_104_fold
   mergeBytes_lengthDelimited_ok savedRegsStack sliceCursorAfter
   sliceCursorAfter_advance_fold sliceCursorAfter_split_copy spAligned_sub_224
   stackAt_slice_to_alloc stackAt_slice_to_bytesFromVec
   unfold_bytesPlacedAt_sp112 unfold_vecHeader_sp136 vecU8Buf_nil_one)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero

/-! ## Phase 2 (`+0x094..+0x210`) on Block `290` -/

/-- Phase 2 tail (`+0x1b8..+0x210`): converts `BytesMut` to `Bytes` via `<Bytes as From<Vec<u8>>>::from`
(`lsmpl.base 250`) and transitions to `phase3_from_0x210_placed`. -/
theorem phase2_from_0x1b8_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hmc : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ "memcpy")
      framelessMemcpyBudgetSpec)
    (hBytesFromVec : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 320)
      (withLsCl lsmpl (doReserveSpec M A lim)))
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
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
    (hpc : s.pc = (blkPl_290).base + 440#64)
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
    SepWPp ((blkPC_290).rebase (blkPl_290).base H) (s0.readReg64 .lr) s
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        bm_vecU8Buf A.repAlloc (BitVec.ofNat 64 v.length) tmpPtr v ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)
      (MergePost A lim x st s0 R) (MergePanic A lim x st s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp3 := fun {s : State} =>
    @phase3_from_0x210_placed _ M A lim H hmc hReserve x st st_cur s0 s R v rest tmpPtr
      hVtableDrop hmerge hfits_res hevs hv_len hbs_len hcapOk
  clear hReserve
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 250)
  apply sepWP_seg_ls_vm (Q := (blkPC_290).rebase (blkPl_290).base (hooksException H)) blkLib_eq_290
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
  rw [stackAt_slice_to_bytesFromVec s0.sp]
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
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx19, hx20, hx21, hx22, hx29,
    bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
  dsimp only [bytesFromVecPlacedSpec]
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr, hvm_bfv⟩ => ?_
  have hpool_bfv : A.pool lim st_cur (_ : State) = A.pool lim st_cur sf_bfv :=
    A.pool_of_vmPreserved hvm_bfv.symm
  rw [hpool_bfv]
  rw [unfold_vecHeader_sp136, unfold_bytesPlacedAt_sp112]
  apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_290).base + 528#64)
  apply sepWP_seg_ls_vm (Q := (blkPC_290).rebase (blkPl_290).base (hooksException H)) blkLib_eq_290
    (mid := (blkPl_290).base + 528#64)
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
      stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104 ∗
      savedRegsStack s0.sp s0)
    (Entails.of_eq (by
      simp (config := { decide := true }) only [arm64_norm, hsp]
      rw [stackAt_slice_to_bytesFromVec s0.sp]
      sep_ac_rfl)) ?_
  exact hp3
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
    hsp_align
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
    (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
      h25f, h26f, h27f, h28f, h29f, hvregsf, h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
    hcl2 hro2
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])

/-- Phase 2 post-alloc (`+0x0e4..+0x1b8`, non-empty `v = b0 :: v'`): copies `v` from the input
slice into `tmpPtr` via `memcpy`, advances the input slice cursor by `v.length`, and continues to
`phase2_from_0x1b8_placed`. -/
theorem phase2_from_0x0e4_nonempty_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hmc : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ "memcpy")
      framelessMemcpyBudgetSpec)
    (hBytesFromVec : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 320)
      (withLsCl lsmpl (doReserveSpec M A lim)))
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {pfx rest0 : List (BitVec 8)} {b0 : BitVec 8} {v' : List (BitVec 8)}
    {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (bytesPlacedDropFnAddr tmpPtr (b0 :: v').length)
      (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr (b0 :: v') (b0 :: v').length)))
    (hvar : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
    (hpfx : x.bs = pfx ++ rest0)
    (hle : (b0 :: v').length ≤ rest0.length)
    (hv_take : rest0.take (b0 :: v').length = b0 :: v')
    (hwt : x.wt = .lengthDelimited)
    (hfits_res : FitsEvents M lim st_cur (doReserveClearEvents x.valCap.toNat (b0 :: v').length))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧
      M.stepEvents (doReserveClearEvents x.valCap.toNat (b0 :: v').length ++
        bytesDropEvents (b0 :: v')) st_cur = M.stepEvents evs st)
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (htmp_ne : tmpPtr ≠ 0#64)
    (hpc : s.pc = (blkPl_290).base + 228#64)
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
    SepWPp ((blkPC_290).rebase (blkPl_290).base H) (s0.readReg64 .lr) s
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        A.repAlloc.live tmpPtr (b0 :: v').length 1 ∗ memRegion tmpPtr (b0 :: v').length ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)
      (MergePost A lim x st s0 R) (MergePanic A lim x st s0 R) := by
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
    @phase2_from_0x1b8_placed _ M A lim H hmc hBytesFromVec hReserve x st st_cur s0 s R
      v (rest0.drop v.length) tmpPtr tmpPtr (BitVec.ofNat 64 v.length) (BitVec.ofNat 64 v.length)
      (1#64 ||| (if (64#64 - BitVec.ofNat 64 (countLeadingZeros (BitVec.ofNat 64 v.length >>> 10))).ult 7#64 = true
        then 64#64 - BitVec.ofNat 64 (countLeadingZeros (BitVec.ofNat 64 v.length >>> 10)) else 7#64) <<< 2)
      w4 w5 w6 w80 hVtableDrop hmerge hfits_res hevs hv_len hbs_len hcapOk
  have hmc' : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen decodeErrorHookStack)) :=
    bmMemcpy_placed_of_framelessBudget hmc
  clear hBytesFromVec hReserve
  rw [sliceCursorAfter_split_copy x.slot x.ptr x.bs pfx rest0 v.length hpfx hle]
  rw [hv_take]
  have hadv := sliceCursorAfter_advance_fold x.slot x.ptr x.bs pfx rest0 v.length hpfx hle hbs_len
  dsimp only at hadv
  rw [hv_take] at hadv
  clear hpfx
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_290).ρ "memcpy")
  apply sepWP_seg_ls_vm (Q := (blkPC_290).rebase (blkPl_290).base (hooksException H)) blkLib_eq_290
    (mid := (blkPl_290).ρ "memcpy")
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
      stackAt (s0.sp - 224#64) decodeVarintSliceStack)
    hmc' hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bmMemcpySpecGen, bmSliceStack, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, hlen_toNat, and_self])
    (by sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm; dsimp only [bmMemcpySpecGen] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_mc hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx8, hx19, hx21, hx24, hx29, hmin_v] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
  simp (config := { decide := true }) only [bmMemcpySpecGen, bmSliceStack, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨_, htr, hvm_mc⟩ => ?_
  have hpool_mc : A.pool lim st_cur (_ : State) = A.pool lim st_cur sf_mc :=
    A.pool_of_vmPreserved hvm_mc.symm
  rw [hpool_mc]
  apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_290).base + 440#64)
  apply sepWP_seg_ls_vm (Q := (blkPC_290).rebase (blkPl_290).base (hooksException H)) blkLib_eq_290
    (mid := (blkPl_290).base + 440#64)
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
        h25f, h26f, h27f, h28f, h29f, hvregsf, h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [bytesMutDataWord, wp_norm, arm64_norm, h22f, ProofLib.ofNat_countLeadingZeros64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))
  exact Entails.of_eq (by
    simp only [ProofLib.ofNat_countLeadingZeros64]
    sep_ac_rfl)

/-- Phase 2 post-length-check (`+0x094..+0x210`, when `len ≤ rest0.length`):
allocates `len` bytes if `len ≠ 0`, copies `rest0.take len.toNat`, converts `BytesMut` to `Bytes`,
reserves and copies into `x.valPtr`, drops temporary `Bytes`, and returns `0` with zero OOM/panic
under `FitsEnv M lim st (BytesMergeEnv x)`. -/
theorem phase2_from_0x094_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hmc : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ "memcpy")
      framelessMemcpyBudgetSpec)
    (hshim : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ lsRustNoAllocShimSym)
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpec M A lim false)))
    (hBytesFromVec : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 320)
      (withLsCl lsmpl (doReserveSpec M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length)))
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {R : SepProp}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited)
    (hvar : decodeVarint x.bs = some (len, rest0))
    (hle : len.toNat ≤ rest0.length)
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (hfits : FitsEnv M lim st (BytesMergeEnv x))
    (hpc : s.pc = (blkPl_290).base + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = len)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 rest0.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx24 : s.readReg64 .x24 = x.slot)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_290).rebase (blkPl_290).base H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool lim st s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A lim x st s0 R) (MergePanic A lim x st s0 R) := by
  have halloc' :=
    subroutine_ok_withLsCl_allocNoOomWithStack_of_budgetWithStack halloc
  clear halloc
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1b8_exit := fun (w4 w5 w6 w80 : BitVec 64) {s : State}
      (hmerge : mergeBytes x.wt x.bs = some ([], rest0))
      (hfits_res : FitsEvents M lim st (doReserveClearEvents x.valCap.toNat 0))
      (hevs : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (doReserveClearEvents x.valCap.toNat 0 ++ bytesDropEvents []) st =
          M.stepEvents evs st) =>
    @phase2_from_0x1b8_placed _ M A lim H hmc hBytesFromVec hReserve x st st s0 s R
      [] rest0 1#64 1#64 0#64 0#64 1#64 w4 w5 w6 w80 (hVtableDrop 1#64 [])
      hmerge hfits_res hevs (by decide) hbs_len hcapOk
  have h0e4_exit := fun (b0 : BitVec 8) (v' : List (BitVec 8)) (st_cur : M.σ)
      (tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64) {s : State}
      (hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
      (hle' : (b0 :: v').length ≤ rest0.length)
      (hv_take' : rest0.take (b0 :: v').length = b0 :: v')
      (hfits_res : FitsEvents M lim st_cur (doReserveClearEvents x.valCap.toNat (b0 :: v').length))
      (hevs : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (doReserveClearEvents x.valCap.toNat (b0 :: v').length ++
          bytesDropEvents (b0 :: v')) st_cur = M.stepEvents evs st)
      (htmp_ne : tmpPtr ≠ 0#64) =>
    @phase2_from_0x0e4_nonempty_placed _ M A lim H hmc hBytesFromVec hReserve x st st_cur s0 s R
      pfx rest0 b0 v' tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 (hVtableDrop tmpPtr (b0 :: v'))
      hvar' hpfx hle' hv_take' hwt hfits_res hevs hbs_len hcapOk htmp_ne
  have hshim' : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (bmShimSpecGen decodeErrorHookStack)) :=
    bmShim_placed_of_noAllocShim hshim
  clear hBytesFromVec hReserve hVtableDrop
  have hlen_lt32 : len.toNat < 2 ^ 63 := by omega
  refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 168#64) 104 ∗
    (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool lim st s ∗
      stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      savedRegsStack s0.sp s0)) (Entails.of_eq (by sep_ac_rfl)) ?_
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
    have hfits_res : FitsEvents M lim st (doReserveClearEvents x.valCap.toNat 0) := by
      rw [doReserveClearEvents_of_le (Nat.zero_le _)]
      trivial
    have hevs_nil :
        ∃ evs, BytesMergeEnv x evs ∧
          M.stepEvents (doReserveClearEvents x.valCap.toNat 0 ++ bytesDropEvents []) st =
            M.stepEvents evs st := by
      refine ⟨[], ?_, ?_⟩
      · simp [BytesMergeEnv, bytesMergeEventsCore, hmerge]
      · simp [doReserveClearEvents_of_le (Nat.zero_le _), bytesDropEvents]
    have hmin0 : (if (0#64).ult (BitVec.ofNat 64 rest0.length) = true
        then 0#64 else BitVec.ofNat 64 rest0.length) = 0#64 :=
      bitvec_if_zero_ult_self (BitVec.ofNat 64 rest0.length)
    rw [← emp_sepConj (((s0.sp - 168#64) ↦₆₄ w0) ∗ _)]
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_290).base + 440#64)
    apply sepWP_seg_ls_vm (Q := (blkPC_290).rebase (blkPl_290).base (hooksException H)) blkLib_eq_290
      (mid := (blkPl_290).base + 440#64)
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp,
        hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
      (hnext := ?_)
    apply SepWP.fold (vecU8Buf_nil_one A.repAlloc) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp,
        hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (h1b8_exit w4 w5 w6 w80 hmerge hfits_res hevs_nil
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp,
        hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh
          simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
            h25, h26, h27, h28, hvregs, and_self])
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
      simp (config := { decide := true }) only [arm64_norm, hsp]
      sep_ac_rfl)
  · set v := b0 :: v'
    have hlen_v : len = BitVec.ofNat 64 v.length := by
      have hv_len_eq : v.length = len.toNat := by rw [← hv, List.length_take_of_le hle]
      rw [hv_len_eq, BitVec.ofNat_toNat]; rfl
    have hle' : v.length ≤ rest0.length := by
      have hv_len_eq : v.length = len.toNat := by rw [← hv, List.length_take_of_le hle]
      omega
    have hv_take' : rest0.take v.length = v := by
      have hv_len_eq : v.length = len.toNat := by rw [← hv, List.length_take_of_le hle]
      rw [hv_len_eq]; exact hv
    clear hv
    have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
    have hv_len : v.length < 2 ^ 63 := by omega
    have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 v.length, rest0) := by
      rwa [← hlen_v]
    have hmerge_v : mergeBytes x.wt x.bs = some (v, rest0.drop v.length) := by
      have hm := mergeBytes_lengthDelimited_ok hwt hvar' (by rw [hlen_toNat]; exact hle')
      rwa [hlen_toNat, hv_take'] at hm
    let evs_all :=
      rustAllocEvents v.length 1 ++
        doReserveClearEvents x.valCap.toNat v.length ++
        rustDeallocEvents v.length 1
    have hevs_bm : BytesMergeEnv x evs_all := by
      have hne0 : v.length ≠ 0 := by dsimp [v]; simp
      simp only [BytesMergeEnv, bytesMergeEventsCore, hmerge_v, hne0, ↓reduceIte, evs_all]
    have hdrop_eq : bytesDropEvents v = rustDeallocEvents v.length 1 := by
      dsimp [v]; simp [bytesDropEvents]
    have hfits_all : FitsEvents M lim st evs_all := hfits evs_all hevs_bm
    have hfits_split1 :
        FitsEvents M lim st (rustAllocEvents v.length 1) ∧
          FitsEvents M lim (M.stepEvents (rustAllocEvents v.length 1) st)
            (doReserveClearEvents x.valCap.toNat v.length ++
              rustDeallocEvents v.length 1) := by
      rw [← fitsEvents_append]
      simpa only [evs_all, List.append_assoc] using hfits_all
    have hfits_alloc : FitsEvents M lim st (rustAllocEvents v.length 1) :=
      hfits_split1.1
    have hfits_res :
        FitsEvents M lim (M.stepEvents (rustAllocEvents v.length 1) st)
          (doReserveClearEvents x.valCap.toNat v.length) :=
      ((fitsEvents_append M lim _ _ _).mp hfits_split1.2).1
    have hevs_after :
        ∃ evs, BytesMergeEnv x evs ∧
          M.stepEvents (doReserveClearEvents x.valCap.toNat v.length ++
            bytesDropEvents v)
            (M.stepEvents (rustAllocEvents v.length 1) st) =
            M.stepEvents evs st := by
      refine ⟨evs_all, hevs_bm, ?_⟩
      rw [← M.stepEvents_append, hdrop_eq]
      simp only [evs_all, List.append_assoc]
    have hmin_v : (if (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true
        then BitVec.ofNat 64 v.length else BitVec.ofNat 64 rest0.length) = BitVec.ofNat 64 v.length := by
      by_cases hlt : v.length < rest0.length
      · have hult : (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true := by
          simp [BitVec.ult, hlen_toNat, hrest0_toNat, hlt]
        simp [hult]
      · have heq : rest0.length = v.length := by omega
        simp [heq]
    have hmsb : (BitVec.ofNat 64 v.length).getLsbD 63 = false :=
      bitvec_getLsbD_63_of_lt32 hv_len
    have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
      apply beq_false_of_ne
      intro h
      have h2 := congrArg BitVec.toNat h
      rw [hlen_toNat] at h2
      exact absurd h2 (by dsimp [v]; simp)
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_290).ρ lsRustNoAllocShimSym)
    apply sepWP_seg_ls_vm (Q := (blkPC_290).rebase (blkPl_290).base (hooksException H)) blkLib_eq_290
      (mid := (blkPl_290).ρ lsRustNoAllocShimSym)
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp,
        hlen_v, hmin_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
        bitvec_getLsbD_63_of_lt32])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
      (hnext := ?_)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp,
        hlen_v, hmin_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
        bitvec_getLsbD_63_of_lt32])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.bm_call_frame_lscl (x := ())
      (T := stackAt (s0.sp - 224#64) decodeVarintSliceStack)
      hshim' hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp,
        hlen_v, hmin_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
        bitvec_getLsbD_63_of_lt32])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [bmShimSpecGen, bmSliceStack, arm64_norm, hsp])
      trivial (by sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [bmShimSpecGen] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
    intro sf_sh hpcf_sh hrunf_sh hspf_sh hcsf_sh hclf_sh hrof_sh
    obtain ⟨h19_sh, h20_sh, h21_sh, h22_sh, h23_sh, h24_sh, h25_sh, h26_sh, h27_sh, h28_sh, h29_sh, hvregs_sh⟩ := hcsf_sh
    simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx8, hx19, hx24, hx29, hlen_v, hmin_v] at hpcf_sh hspf_sh h19_sh h20_sh h21_sh h22_sh h23_sh h24_sh h25_sh h26_sh h27_sh h28_sh h29_sh hvregs_sh
    simp (config := { decide := true }) only [bmShimSpecGen, bmSliceStack, arm64_norm, hsp]
    refine SepWPp.pure_elim fun ⟨htr_sh, hvm_sh⟩ => ?_
    have hpool_sh : A.pool lim st (_ : State) = A.pool lim st sf_sh :=
      A.pool_of_vmPreserved hvm_sh.symm
    rw [hpool_sh]
    apply SepWPp.bm_of_sepWP_lscl hclf_sh hrof_sh (mid := (blkPl_290).ρ lsRustAllocSym)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
    intro hcl3 hro3
    rw [stackAt_slice_to_alloc s0.sp]
    refine SepWPp.bm_call_frame_lscl (x := (v.length, 1, st))
      (T := A.pool lim st _ ∗ stackAt (s0.sp - 224#64) allocHookStack)
      halloc' hcl3 hro3
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hspf_sh, hsp_align]) rfl
      (by simp (config := { decide := true }) only [rustCliAllocNoOomSpecWithStack, arm64_norm, hspf_sh, h21_sh]; rfl)
      (by
        refine ⟨?_, ⟨⟨hpos, ⟨0, rfl⟩, ?_⟩, by decide⟩, hfits_alloc, ?_⟩
        · simp (config := { decide := true }) only [arm64_norm, h21_sh, hlen_toNat]
        · simp only [v, List.length_cons] at hv_len ⊢; omega
        · simp only [wp_norm, arm64_norm, blkPl_290]
          apply lsRetAddr624_blockPlacement_base_add <;> decide)
      (by (conv => lhs; simp (config := { failIfUnchanged := false }) only [arm64_norm]); sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [rustCliAllocNoOomSpecWithStack] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
    intro sf_al hpcf_al hrunf_al hspf_al hcsf_al hclf_al hrof_al
    obtain ⟨h19_al, h20_al, h21_al, h22_al, h23_al, h24_al, h25_al, h26_al, h27_al, h28_al, h29_al, hvregs_al⟩ := hcsf_al
    simp (config := { decide := true }) only [arm64_norm, hspf_sh, h19_sh, h21_sh, h24_sh, h29_sh] at hpcf_al hspf_al h19_al h20_al h21_al h22_al h23_al h24_al h25_al h26_al h27_al h28_al h29_al hvregs_al
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
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)
      (Entails.of_eq (by
        dsimp only [RustCliAllocBudget.repAlloc, v]
        simp (config := { decide := true }) only [arm64_norm, hspf_sh]
        rw [stackAt_slice_to_alloc s0.sp]
        sep_ac_rfl)) ?_
    dsimp only [sliceCursorAfter]
    apply SepWPp.bm_of_sepWP_lscl hclf_al hrof_al (mid := (blkPl_290).base + 228#64)
    wp_steps
    apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
        sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
    intro hcl4 hro4
    obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
    refine SepWPp.weaken_pre ?_ (h0e4_exit b0 v'
      (M.stepEvents (rustAllocEvents (b0 :: v').length 1) st)
      (sf_al.readReg64 .x0) w0 w1 w2 w3 w4 w5 w6 w80
      hvar' hle' hv_take' hfits_res hevs_after h0_64
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf_al])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr_al])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
        h25_al, h26_al, h27_al, h28_al, h29_al, hvregs_al,
        h25_sh, h26_sh, h27_sh, h28_sh, h29_sh, hvregs_sh,
        h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
      hcl4 hro4
      (by dsimp only [v]; simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19_al])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29_al]))
    exact Entails.of_eq (by
      simp (config := { failIfUnchanged := false }) only [arm64_norm]
      sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23PlacedBudget
