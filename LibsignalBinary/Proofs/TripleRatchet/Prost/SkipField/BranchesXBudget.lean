/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux
public meta import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Verification of Non-`StartGroup` `skip_field` Branches

Re-exports the non-delimited wire-type branch proofs from `BranchesXBudgetAux` and proves
`skipField_lengthDelimited_placed_ok_x` for `prost::encoding::skip_field` (block 1).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudget

export LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux
  (call_inv_lscl call_frame_budget_lscl
   fitsEnv_decodeErrorFrom_of_skipField_none skipFieldEnv_of_decodeErrorFrom
   skipFieldEnv_nil_of_some fitsEnv_varintSlice_of_skipField fitsEnv_varintSlow_of_skipField
   skipFieldEnv_of_varintSlice_none skipFieldEnv_of_varintSlow_none
   varintSliceEnv_some_eq_nil varintSlowEnv_some_eq_nil
   skipField_depth_zero_placed_ok_x skipField_endGroup_placed_ok_x
   skipField_sixtyFourBit_placed_ok_x skipField_thirtyTwoBit_placed_ok_x
   skipField_varint_placed_ok_x)

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpecWithStack)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl
   blkPC_1 blkPl_1 withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarintAux decodeVarint_length skipBytes skipField)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (SepWPp.of_sepWP_lscl VarintSlicePre
   bv_len_sub_consumed bv_len_sub_skip bv_ptr_add_skip
   cbz_depth_succ cbz_len_cons_false decodeErrorHookStackX decodeVarint_1
   getLsbD_7_of_gt getLsbD_7_of_le len_cons_sub_one len_ult_consumed_false
   memRegion_48_skipSlice memRegion_48_split
   pointsTo64_pair_entails_memRegion16 pointsToBytes_split_last
   signExtend64_eq_and_0x7f signExtend64_getLsbD_63_of_gt signExtend64_getLsbD_63_of_le
   skipBelowX_err skipBelowX_err_entails skipBelowX_leaf skipBelowX_leaf_entails
   skipBelowX_slow skipBelowX_slow_entails
   skipField_succ_lengthDelimited
   skipSliceErr_entails_memRegion48 skipSliceOk_entails_memRegion48 skipSliceTail_entails_memRegion40
   sliceCursorAfter sliceCursorAt stackAt_skipFieldX
   ule_len_of_ge ule_len_of_lt ult_10_of_ge_11 ult_10_of_lt_11
   varintSliceResultAt w0_and_255_eq)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (DecodeVarintSlowEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceSpecGen decodeVarintSliceSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudgetAux
  (decodeVarintSlowSpecGen decodeVarintSlowSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmasBudget
  (skipFieldSpecAtX)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "wp_reach" : tactic =>
  `(tactic| apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *]))

set_option maxHeartbeats 2400000 in
theorem skipField_lengthDelimited_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hSlowCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 293)
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A lim)))
    (hSliceCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 76)
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A lim)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A lim (d + 1) (fun x => x.wt = .lengthDelimited))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipFieldSpecAtX
    simp only [sliceCursorAt, stackAt_skipFieldX _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hwt_eq : wt = .lengthDelimited := by assumption
  subst hwt_eq
  have hdepth_eq : depth = d + 1 := by assumption
  subst hdepth_eq
  have hx0 : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat := by assumption
  have hx3 : (s0.readReg64 (Reg.gpr 3#5)).setWidth 32 = BitVec.ofNat 32 (d + 1) := by assumption
  have h : bs.length < 2 ^ 63 := by assumption
  have hfits : FitsEnv M lim st (SkipFieldEnv ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩) := by assumption
  have hcbz := cbz_depth_succ hx3 hdepth
  have hw0 := w0_and_255_eq hx0
  dsimp [WireType.toNat] at hw0
  have hpool_nil : A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) := rfl
  cases bs with
  | nil =>
    have hnone : skipField (2 * ([] : List (BitVec 8)).length + 2) (d + 1) tag .lengthDelimited [] = none := by
      rw [skipField_succ_lengthDelimited]; simp [decodeVarint, decodeVarintAux]
    have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none hnone hfits
    rw [hnone]
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps_sync_pool (lsmpl.base 261)
    simp only [State.setMem_setMem]
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr 0#64) (by sep_focus)
    conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hcl1
    refine call_frame_budget_lscl (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
      (x := (s0.sp - 96#64, 0x8000000000000001#64, st))
      (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000001#64 ∧
        FitsEnv M lim st DecodeErrorFromEnv)
      (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
      ⟨rfl, by decide, hfits_de⟩
      (by sep_focus)
      ?_
    intro sm hpcm hrunm hspm hcsm _
    apply SepWPp.of_sepWP_ret
    simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
    apply SepWP.exists_elim; intro evs
    wp_pull_pures
    have hevs_de : DecodeErrorFromEnv evs := by assumption
    have hevs_sf := skipFieldEnv_of_decodeErrorFrom
      (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, []⟩) hnone hevs_de
    apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    wp_done
  | cons b0 bs1 =>
    have hcbz_len := cbz_len_cons_false h
    have himp_none : decodeVarint (b0 :: bs1) = none →
        skipField (2 * (b0 :: bs1).length + 2) (d + 1) tag .lengthDelimited (b0 :: bs1) = none := by
      intro hd; rw [skipField_succ_lengthDelimited, hd]
    have hfits_sl := fitsEnv_varintSlice_of_skipField himp_none hfits
    have hfits_slw := fitsEnv_varintSlow_of_skipField himp_none hfits
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := signExtend64_getLsbD_63_of_le hb0
      have hse := signExtend64_eq_and_0x7f hb0
      have hsub1 := len_cons_sub_one b0 bs1
      by_cases hlt : bs1.length < ((b0 &&& 0x7f#8).zeroExtend 64).toNat
      · have hule := ule_len_of_lt hlt (by simp at h; omega)
        have hnone : skipField (2 * (b0 :: bs1).length + 2) (d + 1) tag .lengthDelimited (b0 :: bs1) = none := by
          rw [skipField_succ_lengthDelimited, decodeVarint_1 bs1 hb0]
          dsimp only
          simp only [skipBytes, hlt, ↓reduceIte]
        have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none hnone hfits
        rw [hnone]
        apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
        conv => arg 4; rw [pointsToBytes_cons, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply SepWP.exists_elim; intro v_err0
        wp_steps_sync_pool (lsmpl.base 261)
        simp only [State.setMem_setMem]
        apply SepWP.fold (Entails.of_eq (pointsToBytes_cons ptr b0 bs1).symm) (by sep_focus)
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + 1#64) (BitVec.ofNat 64 bs1.length)) (by sep_focus)
        conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
        wp_reach
        intro hcl1
        refine call_frame_budget_lscl (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
          (x := (s0.sp - 96#64, 0x8000000000000007#64, st))
          (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64 ∧
            FitsEnv M lim st DecodeErrorFromEnv)
          (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl1
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
          ⟨rfl, by decide, hfits_de⟩
          (by sep_focus)
          ?_
        intro sm hpcm hrunm hspm hcsm _
        apply SepWPp.of_sepWP_ret
        simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
        apply SepWP.exists_elim; intro evs
        wp_pull_pures
        have hevs_de : DecodeErrorFromEnv evs := by assumption
        have hevs_sf := skipFieldEnv_of_decodeErrorFrom
          (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, b0 :: bs1⟩) hnone hevs_de
        apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
        wp_steps_sync_pool (s0.readReg64 Reg.lr)
        simp only [State.setMem_setMem]
        wp_done
      · have hule := ule_len_of_ge hlt (by simp at h; omega)
        have hsub := bv_len_sub_skip (rest := bs1) (n := (b0 &&& 0x7f#8).zeroExtend 64) hlt
        have hadd : ptr + 1#64 + (b0 &&& 0x7f#8).zeroExtend 64 =
            ptr + BitVec.ofNat 64 ((b0 :: bs1).length - (bs1.drop ((b0 &&& 0x7f#8).zeroExtend 64).toNat).length) := by
          have := bv_ptr_add_skip (bs := b0 :: bs1) (rest := bs1) (ptr := ptr)
            (n := (b0 &&& 0x7f#8).zeroExtend 64) (by simp) hlt
          simpa only [List.length_cons, Nat.add_sub_cancel_left] using this
        have hsome : skipField (2 * (b0 :: bs1).length + 2) (d + 1) tag .lengthDelimited (b0 :: bs1) =
            some (bs1.drop ((b0 &&& 0x7f#8).zeroExtend 64).toNat) := by
          rw [skipField_succ_lengthDelimited, decodeVarint_1 bs1 hb0]
          dsimp only
          simp only [skipBytes, hlt, ↓reduceIte]
        have hevs_sf := skipFieldEnv_nil_of_some (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, b0 :: bs1⟩) hsome
        rw [hsome]
        simp only [sliceCursorAfter]
        apply SepWPp.of_sepWP_ret
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps_sync_pool (s0.readReg64 Reg.lr)
        simp only [State.setMem_setMem]
        apply SepWP.fold (Entails.of_eq (pointsToBytes_cons ptr b0 bs1).symm) (by sep_focus)
        conv => arg 4; rw [hpool_nil]
        wp_done
    · have hbit0 := signExtend64_getLsbD_63_of_gt hb0
      have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (472)) hcl0
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps_sync_pool ((blkPl_1).base + bv% (472))
      simp only [State.setMem_setMem]
      wp_reach
      intro hcl1
      by_cases h11 : 11 ≤ (b0 :: bs1).length
      · have hhi := ult_10_of_ge_11 h11 h
        have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
        apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl1
        conv => arg 4; rw [memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
        wp_steps_sync_pool (lsmpl.base 76)
        simp only [State.setMem_setMem]
        wp_reach
        intro hcl2
        refine call_frame_budget_lscl (spec := decodeVarintSliceSpecX A lim)
          (x := (⟨s0.sp - 96#64, ptr, b0 :: bs1⟩, st))
          (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ ptr = ptr ∧
            (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
            (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1) ∧
            FitsEnv M lim st (DecodeVarintSliceEnv (b0 :: bs1)))
          (ret_pc := (blkPl_1).base + bv% (496)) hSliceCall hcl2
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, arm64_norm]; rfl)
          ⟨rfl, rfl, hlen_toNat, h, hpre_slice, hfits_sl⟩
          (by sep_focus)
          ?_
        intro sm hpcm hrunm hspm hcsm hclm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
        cases hd : decodeVarint (b0 :: bs1) with
        | none =>
          have hnone := himp_none hd
          rw [hnone]
          apply SepWPp.of_sepWP_ret
          simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, hd, varintSliceResultAt,
            sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
          apply SepWP.exists_elim; intro evs
          apply SepWP.exists_elim; intro e_err
          wp_pull_pures
          have hevs_sl : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
          have hevs_sf := skipFieldEnv_of_varintSlice_none
            (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, b0 :: bs1⟩) hd hnone hevs_sl
          apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
          wp_steps_sync_pool (s0.readReg64 Reg.lr)
          simp only [State.setMem_setMem]
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
          apply SepWP.fold (skipSliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
          wp_done
        | some p =>
          rcases p with ⟨len, rest⟩
          have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
          have hrest_lt : rest.length < 2 ^ 63 := by omega
          have hcc := len_ult_consumed_false (rest := rest) h
          have hsub_len := bv_len_sub_consumed hd
          by_cases hlt : rest.length < len.toNat
          · have hule := ule_len_of_lt hlt hrest_lt
            have hnone : skipField (2 * (b0 :: bs1).length + 2) (d + 1) tag .lengthDelimited (b0 :: bs1) = none := by
              rw [skipField_succ_lengthDelimited, hd]; simp [skipBytes, hlt]
            have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none hnone hfits
            rw [hnone]
            apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hclm
            simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, hd, varintSliceResultAt,
              sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
            apply SepWP.exists_elim; intro evs
            wp_pull_pures
            have htrm : sm.trace = s0.trace := by assumption
            have hevs_sl : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
            have hevs0 := varintSliceEnv_some_eq_nil hd hevs_sl
            subst hevs0
            conv => arg 4; rw [show M.stepEvents ([] : List AllocEvent) st = st from rfl]
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps_sync_pool (lsmpl.base 261)
            simp only [State.setMem_setMem]
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (skipSliceTail_entails_memRegion40 s0.sp len (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
            conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hspm]
            wp_reach
            intro hcl3
            refine call_frame_budget_lscl (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
              (x := (s0.sp - 96#64, 0x8000000000000007#64, st))
              (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64 ∧
                FitsEnv M lim st DecodeErrorFromEnv)
              (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl3
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
              (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
              ⟨rfl, by decide, hfits_de⟩
              (by sep_focus)
              ?_
            intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _
            apply SepWPp.of_sepWP_ret
            simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
              arm64_norm, htrm, hspm]
            apply SepWP.exists_elim; intro evs2
            wp_pull_pures
            have hevs_de : DecodeErrorFromEnv evs2 := by assumption
            have hevs_sf := skipFieldEnv_of_decodeErrorFrom
              (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, b0 :: bs1⟩) hnone hevs_de
            apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps_sync_pool (s0.readReg64 Reg.lr)
            simp only [State.setMem_setMem]
            wp_done
          · have hule := ule_len_of_ge hlt hrest_lt
            have hsub := bv_len_sub_skip hlt
            have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
            have hsome : skipField (2 * (b0 :: bs1).length + 2) (d + 1) tag .lengthDelimited (b0 :: bs1) =
                some (rest.drop len.toNat) := by
              rw [skipField_succ_lengthDelimited, hd]; simp [skipBytes, hlt]
            rw [hsome]
            apply SepWPp.of_sepWP_ret
            simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, hd, varintSliceResultAt,
              sliceCursorAfter, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
            apply SepWP.exists_elim; intro evs
            wp_pull_pures
            have hevs_sl : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
            have hevs0 := varintSliceEnv_some_eq_nil hd hevs_sl
            subst hevs0
            have hevs_sf := skipFieldEnv_nil_of_some (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, b0 :: bs1⟩) hsome
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps_sync_pool (s0.readReg64 Reg.lr)
            simp only [State.setMem_setMem]
            apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 len (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
            wp_done
      · have hhi := ult_10_of_lt_11 h11 h
        have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (484)) hcl1
        apply SepWP.fold (Entails.of_eq (pointsToBytes_cons ptr b0 bs1).symm) (by sep_focus)
        conv => arg 4; rw [pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
        wp_steps_sync_pool ((blkPl_1).base + bv% (484))
        simp only [State.setMem_setMem]
        apply SepWP.fold (Entails.of_eq (pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h).symm) (by sep_focus)
        wp_reach
        intro hcl2
        by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
        · have hbit_last := getLsbD_7_of_le hlast
          have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
          apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl2
          conv => arg 4; rw [pointsToBytes_cons, memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
          wp_steps_sync_pool (lsmpl.base 76)
          simp only [State.setMem_setMem]
          wp_reach
          intro hcl3
          refine call_frame_budget_lscl (spec := decodeVarintSliceSpecX A lim)
            (x := (⟨s0.sp - 96#64, ptr, b0 :: bs1⟩, st))
            (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ ptr = ptr ∧
              (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
              (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1) ∧
              FitsEnv M lim st (DecodeVarintSliceEnv (b0 :: bs1)))
            (ret_pc := (blkPl_1).base + bv% (496)) hSliceCall hcl3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, arm64_norm]; rfl)
            ⟨rfl, rfl, hlen_toNat, h, hpre_slice, hfits_sl⟩
            (by sep_focus)
            ?_
          intro sm hpcm hrunm hspm hcsm hclm
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            have hnone := himp_none hd
            rw [hnone]
            apply SepWPp.of_sepWP_ret
            simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, hd, varintSliceResultAt,
              sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
            apply SepWP.exists_elim; intro evs
            apply SepWP.exists_elim; intro e_err
            wp_pull_pures
            have hevs_sl : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
            have hevs_sf := skipFieldEnv_of_varintSlice_none
              (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, b0 :: bs1⟩) hd hnone hevs_sl
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps_sync_pool (s0.readReg64 Reg.lr)
            simp only [State.setMem_setMem]
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
            apply SepWP.fold (skipSliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
            wp_done
          | some p =>
            rcases p with ⟨len, rest⟩
            have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
            have hrest_lt : rest.length < 2 ^ 63 := by omega
            have hcc := len_ult_consumed_false (rest := rest) h
            have hsub_len := bv_len_sub_consumed hd
            by_cases hlt : rest.length < len.toNat
            · have hule := ule_len_of_lt hlt hrest_lt
              have hnone : skipField (2 * (b0 :: bs1).length + 2) (d + 1) tag .lengthDelimited (b0 :: bs1) = none := by
                rw [skipField_succ_lengthDelimited, hd]; simp [skipBytes, hlt]
              have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none hnone hfits
              rw [hnone]
              apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hclm
              simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, hd, varintSliceResultAt,
                sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
              apply SepWP.exists_elim; intro evs
              wp_pull_pures
              have htrm : sm.trace = s0.trace := by assumption
              have hevs_sl : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
              have hevs0 := varintSliceEnv_some_eq_nil hd hevs_sl
              subst hevs0
              conv => arg 4; rw [show M.stepEvents ([] : List AllocEvent) st = st from rfl]
              apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps_sync_pool (lsmpl.base 261)
              simp only [State.setMem_setMem]
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
              apply SepWP.fold (skipSliceTail_entails_memRegion40 s0.sp len (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
              conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hspm]
              wp_reach
              intro hcl4
              refine call_frame_budget_lscl (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
                (x := (s0.sp - 96#64, 0x8000000000000007#64, st))
                (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64 ∧
                  FitsEnv M lim st DecodeErrorFromEnv)
                (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl4
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
                ⟨rfl, by decide, hfits_de⟩
                (by sep_focus)
                ?_
              intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _
              apply SepWPp.of_sepWP_ret
              simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
                arm64_norm, htrm, hspm]
              apply SepWP.exists_elim; intro evs2
              wp_pull_pures
              have hevs_de : DecodeErrorFromEnv evs2 := by assumption
              have hevs_sf := skipFieldEnv_of_decodeErrorFrom
                (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, b0 :: bs1⟩) hnone hevs_de
              apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps_sync_pool (s0.readReg64 Reg.lr)
              simp only [State.setMem_setMem]
              wp_done
            · have hule := ule_len_of_ge hlt hrest_lt
              have hsub := bv_len_sub_skip hlt
              have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
              have hsome : skipField (2 * (b0 :: bs1).length + 2) (d + 1) tag .lengthDelimited (b0 :: bs1) =
                  some (rest.drop len.toNat) := by
                rw [skipField_succ_lengthDelimited, hd]; simp [skipBytes, hlt]
              rw [hsome]
              apply SepWPp.of_sepWP_ret
              simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, hd, varintSliceResultAt,
                sliceCursorAfter, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
              apply SepWP.exists_elim; intro evs
              wp_pull_pures
              have hevs_sl : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
              have hevs0 := varintSliceEnv_some_eq_nil hd hevs_sl
              subst hevs0
              have hevs_sf := skipFieldEnv_nil_of_some (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, b0 :: bs1⟩) hsome
              apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps_sync_pool (s0.readReg64 Reg.lr)
              simp only [State.setMem_setMem]
              apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 len (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
              wp_done
        · have hbit_last := getLsbD_7_of_gt hlast
          apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 293) hcl2
          wp_steps_sync_pool (lsmpl.base 293)
          simp only [State.setMem_setMem]
          conv => arg 4; rw [skipBelowX_slow s0.sp (d + 1) hdepth]
          wp_reach
          intro hcl3
          refine call_frame_budget_lscl (spec := decodeVarintSlowSpecX A lim)
            (x := (⟨bufRef, slot, ptr, b0 :: bs1⟩, st))
            (φ := bufRef = bufRef ∧ (b0 :: bs1).length < 2 ^ 63 ∧
              FitsEnv M lim st (DecodeVarintSlowEnv (b0 :: bs1)))
            (ret_pc := (blkPl_1).base + bv% (772)) hSlowCall hcl3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [decodeVarintSlowSpecX, decodeVarintSlowSpecGen, arm64_norm]; rfl)
            ⟨rfl, h, hfits_slw⟩
            (by simp only [sliceCursorAt]; sep_focus)
            ?_
          intro sm hpcm hrunm hspm hcsm hclm
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            have hnone := himp_none hd
            rw [hnone]
            apply SepWPp.of_sepWP_ret
            simp only [decodeVarintSlowSpecX, decodeVarintSlowSpecGen, hd,
              sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
            apply SepWP.exists_elim; intro evs
            wp_pull_pures
            have hevs_slw : DecodeVarintSlowEnv (b0 :: bs1) evs := by assumption
            have hevs_sf := skipFieldEnv_of_varintSlow_none
              (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, b0 :: bs1⟩) hd hnone hevs_slw
            apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps_sync_pool (s0.readReg64 Reg.lr)
            simp only [State.setMem_setMem]
            wp_done
          | some p =>
            rcases p with ⟨len, rest⟩
            have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
            have hrest_lt : rest.length < 2 ^ 63 := by omega
            by_cases hlt : rest.length < len.toNat
            · have hule := ule_len_of_lt hlt hrest_lt
              have hnone : skipField (2 * (b0 :: bs1).length + 2) (d + 1) tag .lengthDelimited (b0 :: bs1) = none := by
                rw [skipField_succ_lengthDelimited, hd]; simp [skipBytes, hlt]
              have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none hnone hfits
              rw [hnone]
              apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hclm
              simp only [decodeVarintSlowSpecX, decodeVarintSlowSpecGen, hd, sliceCursorAfter,
                sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
              apply SepWP.exists_elim; intro evs
              wp_pull_pures
              have hsm1 : sm.readReg64 (Reg.gpr 1#5) = len := by assumption
              have htrm : sm.trace = s0.trace := by assumption
              have hevs_slw : DecodeVarintSlowEnv (b0 :: bs1) evs := by assumption
              have hevs0 := varintSlowEnv_some_eq_nil hd hevs_slw
              subst hevs0
              conv => arg 4; rw [show M.stepEvents ([] : List AllocEvent) st = st from rfl]
              apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
              conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_err0
              wp_steps_sync_pool (lsmpl.base 261)
              simp only [State.setMem_setMem]
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
              conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hspm]
              wp_reach
              intro hcl4
              refine call_frame_budget_lscl (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
                (x := (s0.sp - 96#64, 0x8000000000000007#64, st))
                (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64 ∧
                  FitsEnv M lim st DecodeErrorFromEnv)
                (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl4
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
                ⟨rfl, by decide, hfits_de⟩
                (by sep_focus)
                ?_
              intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _
              apply SepWPp.of_sepWP_ret
              simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
                arm64_norm, htrm, hspm]
              apply SepWP.exists_elim; intro evs2
              wp_pull_pures
              have hevs_de : DecodeErrorFromEnv evs2 := by assumption
              have hevs_sf := skipFieldEnv_of_decodeErrorFrom
                (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, b0 :: bs1⟩) hnone hevs_de
              apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps_sync_pool (s0.readReg64 Reg.lr)
              simp only [State.setMem_setMem]
              wp_done
            · have hule := ule_len_of_ge hlt hrest_lt
              have hsub := bv_len_sub_skip hlt
              have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
              have hsome : skipField (2 * (b0 :: bs1).length + 2) (d + 1) tag .lengthDelimited (b0 :: bs1) =
                  some (rest.drop len.toNat) := by
                rw [skipField_succ_lengthDelimited, hd]; simp [skipBytes, hlt]
              rw [hsome]
              apply SepWPp.of_sepWP_ret
              simp only [decodeVarintSlowSpecX, decodeVarintSlowSpecGen, hd, sliceCursorAfter,
                sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
              apply SepWP.exists_elim; intro evs
              wp_pull_pures
              have hsm1 : sm.readReg64 (Reg.gpr 1#5) = len := by assumption
              have hevs_slw : DecodeVarintSlowEnv (b0 :: bs1) evs := by assumption
              have hevs0 := varintSlowEnv_some_eq_nil hd hevs_slw
              subst hevs0
              have hevs_sf := skipFieldEnv_nil_of_some (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, b0 :: bs1⟩) hsome
              apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps_sync_pool (s0.readReg64 Reg.lr)
              simp only [State.setMem_setMem]
              wp_done

end LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudget
