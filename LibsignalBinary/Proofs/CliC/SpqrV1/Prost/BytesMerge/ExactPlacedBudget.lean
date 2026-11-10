/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.DoReservePlacedBudget
public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.ExactPlacedBudgetAux
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2PlacedBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget
import LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Exact-Capacity Budget-Threaded Proof of `CliC` `prost::encoding::bytes::merge`

Proves `bytesMerge3RawBudgetSpec M A lim` under `[LibsignalPlacement]` for `CliC`
`prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#6]` (Block `558`), preserving the
deterministic capacity equation `cap'.toNat = bmNextCap x.valCap.toNat v.length`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.ExactPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
  lsHandleErrorSym lsMemcpySym lsRustAllocSym lsRustDeallocSym
  lsRustNoAllocShimSym lsRustReallocSym ls_hook_ok_of_mem
  ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain lsmpl withLsCl
)
open CryptoVerification.RustHeap (allocHookStack vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (
  KindNoHeap bytesPlacedDropFnAddr decodeErrorAtStackLen decodeErrorHookStack
  extract_withLsCodeRoLoaded framelessMemcpySpec noAllocShimSpec withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  BytesMergeCapOk BytesMergeGhost DecodeVarintSlowGhost
  SepWPp.bm_call_frame_lscl SepWPp.bm_of_sepWP_lscl
  SepWPp.unfold_cells_64 SepWPp.unfold_memRegion_168
  SepWPp.unfold_memRegion_216 SepWPp.unfold_memRegion_216_invalidWireType
  bitvec_getLsbD_63_of_lt32 bitvec_if_zero_ult_self bitvec_msb_false_of_lt32
  bitvec_sub_self_64 bitvec_ult_33bits_of_lt32 bitvec_ult_zero
  bm_HighCalleeSaved bm_decodeVarint_suffix bytesMergeStack bytesMutDataWord
  bytesMutDataWord_bit0 bytesMutDataWord_getElem_zero bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_lsr5 bytesMutDataWord_zero decodeVarintSliceStack
  fold_memRegion_40_bytes fold_slot_16 mask_ff_32_of_setWidth8
  mergeBytes_lengthDelimited_ok mergeBytes_lengthDelimited_underflow
  mergeBytes_ne_lengthDelimited mergeBytes_of_decodeVarint_none
  savedRegsStack sliceCursorAfter sliceCursorAfter_to_err sliceCursorAt
  spAligned_sub_224 stackAt_slice_to_alloc
  subroutine_ok_withLsCl_of_plain subroutine_ok_withLsCl_of_withLsCodeLoaded
  vecU8Buf_nil_one
)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts (
  truncate32_zeroExtend64_and_255_eq
)
open CryptoVerification.RecordCodecs.Placed (
  blkLib_eq_558 blkPC_558 blkPl_558 lsProg_558
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (
  lsRetAddr624_blockPlacement_base_add
)
open CryptoVerification.SpqrV1.Prost.BytesMerge (
  stackAt_bytesMerge3_entry stackAt_bytesMerge3_eq stackAt_varint2_to_slice
)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  fitsEvents_append fitsEvents_nil rustAllocEvents rustCliAllocBudgetSpec
  rustCliAllocNoOomSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
  rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.DoReservePlacedBudget (do_reserve_7_placed_ok)
open LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.ExactPlacedBudgetAux (
  MergeExactPanic MergeExactPost epilogue3_decodeErrorFrom_0x074_exact_placed
  epilogue3_err_0x07c_exact_placed phase2_from_0x0e4_nonempty_exact_placed
  phase2_from_0x1b8_exact_placed
)
open LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2PlacedBudget (
  decodeVarint2_placed_ok
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (
  BytesMerge3Env BytesMerge3EnvCore bytesMerge3RawBudgetSpec
)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (
  DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  doReserveSpec noAllocShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget (
  bytesDropEvents bytesFromVecPlacedSpec bytesVtableDropSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget (bytesVtableDrop_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget (bytesFromVec_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget (
  bmExactCapCond bmExactPostVecGen bytesMergeExactRawSpecGen
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (
  DecodeVarintSliceEnv decodeVarintSliceEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (
  BytesMergeEnv bytesMergeEventsCore doReserveClearEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget (
  decode_error_from_placed_ok
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero
  bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32 bitvec_getLsbD_63_of_lt32
  bitvec_ult_self bitvec_sub_self_64 bitvec_if_zero_ult_self

/-! ## Outer Phase 2 (`+0x094`) -/

theorem phase2_from_0x094_exact_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsMemcpySym)
      (withLsCl lsmpl (withVmPreserved framelessMemcpySpec)))
    (hshim : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (withVmPreserved noAllocShimSpec)))
    (halloc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocNoOomSpec M A lim false)))
    (hBytesFromVec : subroutine_ok (lsProg_558 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok (lsProg_558 H) (lsmpl.base 561)
      (withLsCl lsmpl (doReserveSpec M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_558 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length)))
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {R : SepProp}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited)
    (hvar : decodeVarint x.bs = some (len, rest0))
    (hle : len.toNat ≤ rest0.length)
    (hfits : FitsEnv M lim st (BytesMergeEnv x))
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_558).base + 148#64)
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
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool lim st s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPost A lim x st s0 R) (MergeExactPanic A lim x st s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1b8_exit := fun (w4 w5 w6 w80 : BitVec 64) {s : State}
      (hmerge : mergeBytes x.wt x.bs = some ([], rest0))
      (hfits_res : FitsEvents M lim st (doReserveClearEvents x.valCap.toNat ([] : List (BitVec 8)).length))
      (hevs : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (bytesDropEvents [])
          (M.stepEvents (doReserveClearEvents x.valCap.toNat ([] : List (BitVec 8)).length) st) =
          M.stepEvents evs st) =>
    @phase2_from_0x1b8_exact_placed _ M A lim H hmc hBytesFromVec hReserve
      x st st s0 s R [] rest0 1#64 1#64 0#64 0#64 1#64 w4 w5 w6 w80 (hVtableDrop 1#64 [])
      hmerge hfits_res hevs (by decide) hbs_len hcapOk
  have h0e4_exit := fun (b0 : BitVec 8) (v' : List (BitVec 8)) (st1 : M.σ)
      (tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64) {s : State}
      (hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
      (hle' : (b0 :: v').length ≤ rest0.length)
      (hv_take' : rest0.take (b0 :: v').length = b0 :: v')
      (hfits_res : FitsEvents M lim st1 (doReserveClearEvents x.valCap.toNat (b0 :: v').length))
      (hevs : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (bytesDropEvents (b0 :: v'))
          (M.stepEvents (doReserveClearEvents x.valCap.toNat (b0 :: v').length) st1) =
          M.stepEvents evs st)
      (htmp_ne : tmpPtr ≠ 0#64) =>
    @phase2_from_0x0e4_nonempty_exact_placed _ M A lim H hmc hBytesFromVec hReserve
      x st st1 s0 s R pfx rest0 b0 v' tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 (hVtableDrop tmpPtr (b0 :: v'))
      hvar' hpfx hle' hv_take' hwt hfits_res hevs hbs_len hcapOk htmp_ne
  clear hBytesFromVec hReserve hVtableDrop
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
    have hfits_res0 : FitsEvents M lim st (doReserveClearEvents x.valCap.toNat ([] : List (BitVec 8)).length) := by
      simp [doReserveClearEvents, fitsEvents_nil]
    have hevs0 : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (bytesDropEvents [])
          (M.stepEvents (doReserveClearEvents x.valCap.toNat ([] : List (BitVec 8)).length) st) =
          M.stepEvents evs st := by
      refine ⟨[], ?_, ?_⟩
      · simp [BytesMergeEnv, bytesMergeEventsCore, hmerge]
      · simp [doReserveClearEvents, bytesDropEvents]
    have hmin0 : (if (0#64).ult (BitVec.ofNat 64 rest0.length) = true then 0#64 else BitVec.ofNat 64 rest0.length) = 0#64 :=
      bitvec_if_zero_ult_self (BitVec.ofNat 64 rest0.length)
    rw [← emp_sepConj (((s0.sp - 168#64) ↦₆₄ w0) ∗ _)]
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_558).base + 440#64)
    wp_steps_sync_pool ((blkPl_558).base + 440#64)
    apply SepWP.fold (vecU8Buf_nil_one A.repAlloc) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (h1b8_exit w4 w5 w6 w80 hmerge hfits_res0 hevs0
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, bytesMutDataWord_zero])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
    exact Entails.of_eq (by dsimp only [RustCliAllocBudget.repAlloc]; simp (config := { decide := true }) only [arm64_norm, hsp]; sep_ac_rfl)
  · set v := b0 :: v'
    have hlen_v : len = BitVec.ofNat 64 v.length := by
      have hv_len_eq : v.length = len.toNat := by rw [← hv, List.length_take_of_le hle]
      rw [hv_len_eq, BitVec.ofNat_toNat]
      rfl
    have hle' : v.length ≤ rest0.length := by
      have hv_len_eq : v.length = len.toNat := by rw [← hv, List.length_take_of_le hle]
      omega
    have hv_take' : rest0.take v.length = v := by
      have hv_len_eq : v.length = len.toNat := by rw [← hv, List.length_take_of_le hle]
      rw [hv_len_eq]
      exact hv
    clear hv
    have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
    have hv_len : v.length < 2 ^ 63 := by omega
    have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hmerge_v : mergeBytes x.wt x.bs = some (v, rest0.drop v.length) := by
      have hm := mergeBytes_lengthDelimited_ok hwt hvar hle
      rwa [hlen_v, hlen_toNat, hv_take'] at hm
    have hv_len_ne0 : v.length ≠ 0 := by omega
    have hcore_eq : bytesMergeEventsCore x.wt x.valCap x.bs =
        rustAllocEvents v.length 1 ++
          (doReserveClearEvents x.valCap.toNat v.length ++ rustDeallocEvents v.length 1) := by
      simp [bytesMergeEventsCore, hmerge_v, hv_len_ne0, List.append_assoc]
    have hfits_all : FitsEvents M lim st
        (rustAllocEvents v.length 1 ++
          (doReserveClearEvents x.valCap.toNat v.length ++ rustDeallocEvents v.length 1)) := by
      rw [← hcore_eq]
      exact hfits _ rfl
    obtain ⟨hfits_al, hfits_tail⟩ := (fitsEvents_append M lim _ _ st).mp hfits_all
    let st1 := M.stepEvents (rustAllocEvents v.length 1) st
    obtain ⟨hfits_res, _⟩ := (fitsEvents_append M lim _ _ st1).mp hfits_tail
    have hevs_v : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (bytesDropEvents v)
          (M.stepEvents (doReserveClearEvents x.valCap.toNat v.length) st1) =
          M.stepEvents evs st := by
      refine ⟨bytesMergeEventsCore x.wt x.valCap x.bs, rfl, ?_⟩
      have hdrop_eq : bytesDropEvents v = rustDeallocEvents v.length 1 := by
        simp [bytesDropEvents, hv_len_ne0]
      rw [hdrop_eq, hcore_eq]
      simp only [st1, AllocCostModel.stepEvents_append, List.append_assoc]
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
      exact absurd h2 (by simp [v])
    have hrlay : RustLayoutOk v.length 1 :=
      ⟨⟨hpos, ⟨0, rfl⟩, by simp only [v, List.length_cons] at hv_len ⊢; omega⟩, by decide⟩
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_558).ρ lsRustNoAllocShimSym)
    wp_steps_sync_pool ((blkPl_558).ρ lsRustNoAllocShimSym)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp,
        hlen_v, hmin_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
        bitvec_getLsbD_63_of_lt32])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.bm_call_frame_lscl (spec := withVmPreserved noAllocShimSpec) (x := ()) (T := emp)
      hshim hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp,
        hlen_v, hmin_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
        bitvec_getLsbD_63_of_lt32])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp [withVmPreserved, noAllocShimSpec]) trivial (by rw [emp_sepConj])
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [withVmPreserved, noAllocShimSpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
    intro sf_sh hpcf_sh hrunf_sh hspf_sh hcsf_sh hclf_sh hrof_sh
    obtain ⟨h19_sh, h20_sh, h21_sh, h22_sh, h23_sh, h24_sh, h25_sh, h26_sh, h27_sh, h28_sh, h29_sh, hvregs_sh⟩ := hcsf_sh
    simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx8, hx19, hx24, hx29, hlen_v, hmin_v] at hpcf_sh hspf_sh h19_sh h20_sh h21_sh h22_sh h23_sh h24_sh h25_sh h26_sh h27_sh h28_sh h29_sh hvregs_sh
    dsimp only [withVmPreserved, noAllocShimSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hvm_sh => ?_
    rw [A.pool_of_vmPreserved hvm_sh.symm]
    refine SepWPp.pure_elim fun htr_sh => ?_
    apply SepWPp.bm_of_sepWP_lscl hclf_sh hrof_sh (mid := (blkPl_558).ρ lsRustAllocSym)
    wp_steps_sync_pool ((blkPl_558).ρ lsRustAllocSym)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
    intro hcl3 hro3
    rw [stackAt_slice_to_alloc s0.sp]
    refine SepWPp.bm_call_frame_lscl
      (spec := rustCliAllocNoOomSpec M A lim false)
      (x := (v.length, 1, st))
      (T := A.pool lim st _ ∗ stackAt (s0.sp - 224#64) allocHookStack)
      halloc hcl3 hro3
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hspf_sh, hsp_align]) rfl
      (by simp (config := { decide := true }) only [rustCliAllocNoOomSpec, arm64_norm, hspf_sh, h21_sh]; rfl)
      (by
        simp only [hlen_toNat, hrlay, and_true, true_and]
        refine ⟨hfits_al, ?_⟩
        simp only [wp_norm, arm64_norm, blkPl_558]
        apply lsRetAddr624_blockPlacement_base_add <;> decide)
      (by sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [rustCliAllocNoOomSpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
    intro sf_al hpcf_al hrunf_al hspf_al hcsf_al hclf_al hrof_al
    obtain ⟨h19_al, h20_al, h21_al, h22_al, h23_al, h24_al, h25_al, h26_al, h27_al, h28_al, h29_al, hvregs_al⟩ := hcsf_al
    simp (config := { decide := true }) only [arm64_norm, hspf_sh, h19_sh, h21_sh, h24_sh, h29_sh] at hpcf_al hspf_al h19_al h20_al h21_al h22_al h23_al h24_al h25_al h26_al h27_al h28_al h29_al hvregs_al
    dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpres_al, h0_64, _⟩ => ?_
    have htr_al : sf_al.trace = s0.trace := by
      have ht := hpres_al.2.1
      simp (config := { decide := true }) only [wp_norm, arm64_norm, htr_sh, htrace] at ht
      exact ht
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
        A.pool lim st1 sf_al ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)
      (Entails.of_eq (by
        dsimp only [st1, v, RustCliAllocBudget.repAlloc]
        simp (config := { decide := true }) only [arm64_norm, hspf_sh]
        rw [stackAt_slice_to_alloc s0.sp]
        sep_ac_rfl)) ?_
    dsimp only [sliceCursorAfter]
    apply SepWPp.bm_of_sepWP_lscl hclf_al hrof_al (mid := (blkPl_558).base + 228#64)
    wp_steps_sync_pool ((blkPl_558).base + 228#64)
    apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
        sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
    intro hcl4 hro4
    have hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0) := by rwa [← hlen_v]
    obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
    refine SepWPp.weaken_pre ?_ (h0e4_exit b0 v' st1 (sf_al.readReg64 .x0) w0 w1 w2 w3 w4 w5 w6 w80
      hvar' hle' hv_take' hfits_res hevs_v h0_64
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf_al])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr_al])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_al, h26_al, h27_al, h28_al, hvregs_al, h25_sh, h26_sh, h27_sh, h28_sh, hvregs_sh, h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
      hcl4 hro4
      (by dsimp only [v]; simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19_al])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29_al]))
    exact Entails.of_eq (by dsimp only [RustCliAllocBudget.repAlloc]; (try simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64]); sep_ac_rfl)

/-! ## `MergeExactPost3` and `MergeExactPanic3` Frame Lifters -/

abbrev MergeExactPost3 {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawBudgetSpec M A lim).post (x, st) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergeExactPanic3 {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawBudgetSpec M A lim).onPanic (x, st) s0 sf ∗ R)

theorem SepWPp.to_subroutineOutcome3_exact_placed [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : BytesMergeGhost} {st : M.σ} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (MergeExactPost3 A lim x st s0 R) (MergeExactPanic3 A lim x st s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim))
        (x, st) R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem SepWPp.lift_merge3_exact {M : AllocCostModel} {prog : Program}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {P R : SepProp}
    (h : SepWPp prog (s0.readReg64 .lr) s P
      (MergeExactPost A lim x st s0 (memRegion (s0.sp - 8544#64) 48 ∗ R))
      (MergeExactPanic A lim x st s0 (memRegion (s0.sp - 8544#64) 48 ∗ R))) :
    SepWPp prog (s0.readReg64 .lr) s (memRegion (s0.sp - 8544#64) 48 ∗ P)
      (MergeExactPost3 A lim x st s0 R) (MergeExactPanic3 A lim x st s0 R) := by
  intro F hm hL
  have hm' : s.mem ⊨ P ∗ (memRegion (s0.sp - 8544#64) 48 ∗ F) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h (memRegion (s0.sp - 8544#64) 48 ∗ F) hm' hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, memRegion (s0.sp - 8544#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf, ?_, hsp, hcs⟩⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 8544#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmr
    have hp := hpost hmr'
    dsimp only [bytesMergeExactRawSpecGen, bmExactPostVecGen, bmExactCapCond,
      BytesMergeEnv, bytesMerge3RawBudgetSpec, BytesMerge3Env, BytesMerge3EnvCore,
      LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget.bmNextCap,
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bmNextCap] at hp ⊢
    rw [show 0xe0 + (0x50 + decodeErrorHookStack) = bytesMergeStack from rfl] at hp
    rw [stackAt_bytesMerge3_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, memRegion (s0.sp - 8544#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf, ?_⟩)⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 8544#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmr
    have hp := hpanic hmr'
    dsimp only [bytesMergeExactRawSpecGen] at hp
    exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-! ## Phase 1 and Top-Level Exact-Capacity Verification -/

private theorem fitsEnv_decodeVarint2_of_bytesMerge {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : BytesMergeGhost}
    (hfits : FitsEnv M lim st (BytesMergeEnv x)) :
    FitsEnv M lim st (DecodeVarint2Env x.bs) := by
  intro evs hevs
  rcases hdv : decodeVarint x.bs with _ | ⟨len, rest0⟩
  · have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hdv
    apply hfits
    simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents,
      BytesMergeEnv, bytesMergeEventsCore, hdv, hmerge] using hevs
  · have hnil : evs = [] := by
      simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] using hevs
    subst hnil
    trivial

private theorem hookSat_sessionShimBudget_of_withVmPreserved
    {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym (withVmPreserved noAllocShimSpec)) :
    HookSat H sym sessionShimBudgetSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr hrest

private theorem hookSat_noAllocShimBudget_of_withVmPreserved
    {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym (withVmPreserved noAllocShimSpec)) :
    HookSat H sym noAllocShimBudgetSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

theorem bytes_merge_3_exact_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_558 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hmc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsMemcpySym)
      (withLsCl lsmpl (withVmPreserved framelessMemcpySpec)))
    (hshim : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (withVmPreserved noAllocShimSpec)))
    (halloc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocNoOomSpec M A lim false)))
    (hDecodeVarint2 : subroutine_ok (lsProg_558 H) (lsmpl.base 559)
      (withLsCl lsmpl (decodeVarint2Spec A lim)))
    (hBytesFromVec : subroutine_ok (lsProg_558 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve7 : subroutine_ok (lsProg_558 H) (lsmpl.base 561)
      (withLsCl lsmpl (doReserveSpec M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_558 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length))) :
    subroutine_ok (lsProg_558 H) (blkPl_558).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp_align hL => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMerge3RawBudgetSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw0, hx1, hx2, hbs_len, hcapOk, hfits3⟩, hm⟩ := hpre
  have hfits : FitsEnv M lim st (BytesMergeEnv x) := hfits3
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  let R48 : SepProp := memRegion (s0.sp - 8544#64) 48 ∗ R
  have herr_exit := fun {st_cur : M.σ} {s : State} (hmerge : mergeBytes x.wt x.bs = none)
      (hevs : ∃ evs, BytesMergeEnv x evs ∧ st_cur = M.stepEvents evs st) =>
    @epilogue3_err_0x07c_exact_placed _ M A lim H x st st_cur s0 s R48 hmerge hevs
  have hde_exit := fun (w : BitVec 64) (hw : KindNoHeap w) {s : State}
      (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue3_decodeErrorFrom_0x074_exact_placed _ M A lim H hdef x st s0 s R48 w hw hmerge hfits
  have h094_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hwt : x.wt = WireType.lengthDelimited)
      (hvar : decodeVarint x.bs = some (len, rest0))
      (hle : len.toNat ≤ rest0.length) =>
    @phase2_from_0x094_exact_placed _ M A lim H hmc hshim halloc hBytesFromVec hReserve7
      hVtableDrop x st s0 s R48 len rest0 hwt hvar hle hfits hbs_len hcapOk
  clear hBytesFromVec hReserve7 hVtableDrop
  refine Exists.elim (SepWPp.to_subroutineOutcome3_exact_placed hsp_align hm hL ?_)
    fun _ ⟨hsteps, hout⟩ => reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  rw [stackAt_bytesMerge3_entry s0.sp]
  refine SepWPp.weaken_pre (P' := cells (s0.sp - 64#64) 8 ∗
    (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool lim st s0 ∗
      stackAt (s0.sp - 224#64) decodeVarint2Stack ∗
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
    have hfits_dv : FitsEnv M lim st (DecodeVarint2Env x.bs) :=
      fitsEnv_decodeVarint2_of_bytesMerge hfits
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 559)
    apply sepWP_seg_ls_vm (Q := (blkPC_558).rebase (blkPl_558).base (hooksException H)) blkLib_eq_558
      (mid := lsmpl.base 559)
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
    refine SepWPp.bm_call_frame_lscl
      (x := (({ bufRef := x.bufRef, slot := x.slot, ptr := x.ptr, bs := x.bs } : DecodeVarintSlowGhost), st))
      (T := (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool lim st _ ∗
        stackAt (s0.sp - 224#64) decodeVarint2Stack)
      hDecodeVarint2 hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp_align]) rfl
      (by
        simp (config := { decide := true }) only [decodeVarint2Spec, decodeVarint2SpecGen,
          arm64_norm, hx2]
        rfl)
      (by exact ⟨hbs_len, hfits_dv⟩)
      (by sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen] at hm
          rw [sepConj_assoc] at hm
          exact False.elim (not_satisfies_false_sepConj hm)) ?_
    intro sf_dv hpcf hrunf hspf hcsf hclf hrof
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hx1, hx2] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
    dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
    simp (config := { decide := true }) only [
      show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
      arm64_norm]
    rw [stackAt_varint2_to_slice s0.sp]
    rcases hvar : decodeVarint x.bs with _ | ⟨len, rest0⟩
    · dsimp only
      have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
      refine SepWPp.exists_elim fun evs => ?_
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.trace = s0.trace ∧ DecodeVarint2Env x.bs evs⌝ ∗
        ⌜sf_dv.readReg64 .x0 = 1#64⌝ ∗ ⌜sf_dv.readReg64 .x1 ≠ 0#64⌝ ∗
          (memRegion (s0.sp - 8544#64) 48 ∗
            decodeErrorAtStackLen A.repAlloc (sf_dv.readReg64 .x1) 0 ∗
            vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗
            A.pool lim (M.stepEvents evs st) sf_dv ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          sep_ac_rfl)) ?_
      refine SepWPp.pure_elim fun ⟨htr, hevs_dv⟩ => ?_
      refine SepWPp.pure_elim fun hx0_sf => ?_
      refine SepWPp.pure_elim fun hx1_sf => ?_
      have hevs_bm : BytesMergeEnv x evs := by
        simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents,
          BytesMergeEnv, bytesMergeEventsCore, hvar, hmerge] using hevs_dv
      apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_558).base + 124#64)
      apply sepWP_seg_ls_vm (Q := (blkPC_558).rebase (blkPl_558).base (hooksException H)) blkLib_eq_558
        (mid := (blkPl_558).base + 124#64)
      intro _m_strip2
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        fun _m_real2 _hnsp2 => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp2.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        (hnext := ?_)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hcl2 hro2
      refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3_exact (herr_exit hmerge ⟨evs, hevs_bm, rfl⟩
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; simpa [Reg.x1] using hx1_sf)
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
          h25f, h26f, h27f, h28f, hvregsf, and_self])))
      exact Entails.of_eq (by
        dsimp only [Reg.x0, Reg.x1]
        simp (config := { decide := true }) only [wp_norm, arm64_norm]
        sep_ac_rfl)
    · dsimp only
      obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
      have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
      have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine SepWPp.exists_elim fun evs => ?_
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.trace = s0.trace ∧ DecodeVarint2Env x.bs evs⌝ ∗
        ⌜sf_dv.readReg64 .x0 = 0#64 ∧ sf_dv.readReg64 .x1 = len⌝ ∗
          (memRegion (s0.sp - 8544#64) 48 ∗
            vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
            A.pool lim (M.stepEvents evs st) sf_dv ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          sep_ac_rfl)) ?_
      refine SepWPp.pure_elim fun ⟨htr, hevs_dv⟩ => ?_
      refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
      have hevs_nil : evs = [] := by
        simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hvar] using hevs_dv
      subst hevs_nil
      dsimp only [AllocCostModel.stepEvents, List.foldl, sliceCursorAfter]
      apply SepWPp.bm_of_sepWP_lscl hclf hrof
        (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then (blkPl_558).base + 148#64 else (blkPl_558).base + 80#64)
      apply sepWP_seg_ls_vm (Q := (blkPC_558).rebase (blkPl_558).base (hooksException H)) blkLib_eq_558
        (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then (blkPl_558).base + 148#64 else (blkPl_558).base + 80#64)
      intro _m_strip3
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        fun _m_real3 _hnsp3 => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp3.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        (hnext := ?_)
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hcl2 hro2
      by_cases hule : len.ule (BitVec.ofNat 64 rest0.length) = false
      · simp only [hule, Bool.false_eq_true, ↓reduceIte] at hcl2 hro2 ⊢
        have hlt : rest0.length < len.toNat := by simp [BitVec.ule, hrest0_toNat] at hule; omega
        have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_lengthDelimited_underflow hwt hvar hlt
        refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
          (memRegion (s0.sp - 8544#64) 48 ∗
            vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool lim st _ ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
          (Entails.of_eq (by sep_ac_rfl)) ?_
        refine SepWPp.unfold_memRegion_216 fun w216 => ?_
        apply SepWPp.bm_of_sepWP_lscl hcl2 hro2 (mid := (blkPl_558).base + 116#64)
        apply sepWP_seg_ls_vm (Q := (blkPC_558).rebase (blkPl_558).base (hooksException H)) blkLib_eq_558
          (mid := (blkPl_558).base + 116#64)
        intro _m_strip4
        wp_steps
        refine SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          fun _m_real4 _hnsp4 => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp4.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
          (hnext := ?_)
        apply SepWP.fold (sliceCursorAfter_to_err x.slot x.ptr x.bs rest0) (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        intro hcl3 hro3
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3_exact (hde_exit 0x8000000000000007#64 (by simp [KindNoHeap]) hmerge
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hcl3 hro3))
        exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; sep_ac_rfl)
      · have hule_eq : len.ule (BitVec.ofNat 64 rest0.length) = true :=
          Bool.eq_true_of_not_eq_false hule
        simp only [hule_eq, ↓reduceIte] at hcl2 hro2 ⊢
        have hle : len.toNat ≤ rest0.length := by simpa [BitVec.ule, hrest0_toNat] using hule_eq
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3_exact (h094_exit len rest0 hwt hvar hle
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hcl2 hro2
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1_sf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f])))
        exact Entails.of_eq (by sep_ac_rfl)
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = true
      rw [truncate32_zeroExtend64_and_255_eq, hw0]
      cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_ne_lengthDelimited hwt
    dsimp only [sliceCursorAt]
    rw [stackAt_varint2_to_slice s0.sp]
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (memRegion (s0.sp - 8544#64) 48 ∗
        ((s0.sp - 64#64) ↦₆₄ c0) ∗ ((s0.sp - 56#64) ↦₆₄ c1) ∗
        ((s0.sp - 48#64) ↦₆₄ c2) ∗ ((s0.sp - 40#64) ↦₆₄ c3) ∗
        ((s0.sp - 32#64) ↦₆₄ c4) ∗ ((s0.sp - 24#64) ↦₆₄ c5) ∗
        ((s0.sp - 16#64) ↦₆₄ c6) ∗ ((s0.sp - 8#64) ↦₆₄ c7) ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool lim st s0 ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104)) (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216_invalidWireType fun w0_216 b0_216 b1_216 => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_558).base + 116#64)
    apply sepWP_seg_ls_vm (Q := (blkPC_558).rebase (blkPl_558).base (hooksException H)) blkLib_eq_558
      (mid := (blkPl_558).base + 116#64)
    intro _m_strip5
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      fun _m_real5 _hnsp5 => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp5.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
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
    refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3_exact (hde_exit 0x8000000000000006#64 (by simp [KindNoHeap]) hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
      hcl1 hro1))
    exact Entails.of_eq (by dsimp only [savedRegsStack]; simp (config := { decide := true }) only [arm64_norm]; sep_ac_rfl)

theorem bytes_merge_3_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym (withVmPreserved framelessMemcpySpec))
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_558 H) (blkPl_558).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)) :=
  bytes_merge_3_exact_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_plain (callerProg := lsProg_558 H)
      (decode_error_from_placed_ok (hookSat_sessionShimBudget_of_withVmPreserved hshim) halloc))
    (subroutine_ok_withLsCl_of_plain
      (ls_hook_ok_of_mem (prog := lsProg_558 H) (i := 558) hmc))
    (subroutine_ok_withLsCl_of_plain
      (ls_hook_ok_of_mem (prog := lsProg_558 H) (i := 558) hshim))
    (subroutine_ok_withLsCl_of_plain
      (subroutine_ok_allocNoOom_of_budget
        (ls_hook_ok_of_mem (prog := lsProg_558 H) (i := 558) halloc)))
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_558 H)
      (decodeVarint2_placed_ok (hookSat_sessionShimBudget_of_withVmPreserved hshim) halloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := lsProg_558 H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_558 H)
      (do_reserve_7_placed_ok hpanic_raw (hookSat_noAllocShimBudget_of_withVmPreserved hshim)
        halloc hrealloc))
    (fun tmpPtr v =>
      subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok (callerProg := lsProg_558 H) (i := 558) hdealloc
          (by decide) tmpPtr v v.length))

end LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.ExactPlacedBudget
