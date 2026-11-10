/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.SkipField3BranchesPlaced
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2Placed
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Proof of `CliC` `skip_field [local#6]`

Proves the recursive `startGroup` loop and combines all wire-type branches by induction on `depth`
to establish `withLsCodeLoaded lsmpl (skipField3Spec A)` on Block `546`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Varint

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.RecordCodecs.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Case 7: `depth = d + 1`, `wt = .startGroup` -/

set_option maxHeartbeats 2000000 in
theorem _root_.CryptoVerification.CliC.SpqrV1.Varint.skipField3_startGroup_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_546 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpec A)))
    (hVarintCall : subroutine_ok (lsProg_546 H) (lsmpl.base 559)
      (withLsCl lsmpl (decodeVarint2Spec A)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32)
    (hrec : subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A d (fun _ => True)))) :
    subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A (d + 1) (fun x => x.wt = .startGroup))) := by
  have hrec_cl : subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCl lsmpl (skipField3SpecAt A d (fun _ => True))) :=
    ls_subroutine_ok_cl_of_block (callerProg := lsProg_546 H) hrec
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := by assumption
  have hwt_eq : wt = .startGroup := by assumption
  subst hwt_eq
  have hx0_wt : BitVec.setWidth 8 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 8 WireType.startGroup.toNat := by assumption
  have htag_lt : tag < 2 ^ 32 := by assumption
  have hx3_d : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (d + 1) := by assumption
  have hcbz := cbz_depth_succ hx3_d hdepth
  have hw0 := w0_and_255_eq hx0_wt
  dsimp [WireType.toNat] at hw0
  obtain ⟨htag_zext1, htag_zext2⟩ := bv32_zeroExtend_ofNat htag_lt
  obtain ⟨hd_zext1, hd_zext2⟩ := bv32_zeroExtend_ofNat (by omega : d < 2 ^ 32)
  obtain ⟨hd_sub1, hd_sub2⟩ := bv32_sub_one_zeroExtend hdepth
  rw [skipField_succ_startGroup]
  generalize hres : skipGroup (2 * bs.length + 1) (d + 1) tag bs = res
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  apply SepWPp.of_sepWP_lscl (mid := (blkPl_546).base + 232#64) hcl0
  wp_steps
  wp_reach
  intro hcl_init
  apply SepWPp.weaken_pre (P' := skipGroupLoopPre3 A s0 d bufRef slot ptr v_stk_2 bs bs)
    (Entails.of_eq (by dsimp only [skipGroupLoopPre3]; simp only [sliceCursorAfter, Nat.sub_self,
      BitVec.add_zero]; ac_rfl))
  refine (fun (Q_f Qp_f : State → SepProp → Prop)
      (hloop : ∀ n (cur : List (BitVec 8)) (s : State),
        cur.length ≤ n →
        cur.length ≤ bs.length →
        IsDropSuffix bs cur →
        skipGroup (2 * cur.length + 1) (d + 1) tag cur = res →
        s.pc = (blkPl_546).base + 232#64 →
        s.status = .Running →
        s.sp = s0.sp - 96#64 →
        s.trace = s0.trace →
        s.readReg64 (Reg.gpr 19#5) = bufRef →
        s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
        s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
        HighCalleeSaved3 s0 s →
        LibsignalCodeLoaded lsmpl s.mem →
        SepWPp (lsProg_546 H) (s0.readReg64 Reg.lr) s
          (skipGroupLoopPre3 A s0 d bufRef slot ptr v_stk_2 bs cur) Q_f Qp_f) =>
      hloop bs.length bs _ (Nat.le_refl _) (Nat.le_refl _) (by simp [IsDropSuffix]) hres
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm]⟩
        hcl_init)
    _ _ ?_
  intro n
  induction n with
  | zero =>
    intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hcl_s
    obtain ⟨hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
    have hcur_lt : cur.length < 2 ^ 63 := by omega
    let curPtr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - cur.length)
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 559) hcl_s
    conv => arg 4; rw [skipGroupLoopPre3, sliceCursorAfter_eq_split hcur_le hcur_suf,
      skipBelow3_leaf s0.sp (d + 1) hdepth]
    wp_steps
    wp_reach
    intro hcl1
    refine SepWPp.call_frame_lscl (spec := decodeVarint2Spec A)
      (x := ⟨bufRef, slot, curPtr, cur⟩)
      (ret_pc := (blkPl_546).base + 240#64) hVarintCall hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
      (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeVarint2Spec, arm64_norm, hsp_s]; rfl)
      (⟨rfl, hcur_lt⟩ : bufRef = bufRef ∧ cur.length < 2 ^ 63)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _hcl2
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
    dsimp only [decodeVarint2Spec]
    cases hd : decodeVarint cur with
    | none =>
      have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
      rw [hnone] at hres_cur
      subst hres_cur
      apply SepWPp.of_sepWP_ret
      simp only [sepConj_assoc, arm64_norm, htr_s, hsp_s]
      apply SepWP.pure_elim; intro hsm0
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
      wp_steps
      wp_done
    | some p =>
      have hlt_cur := decodeVarint_length hd
      omega
  | succ n ih =>
    intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hcl_s
    obtain ⟨hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
    have hcur_lt : cur.length < 2 ^ 63 := by omega
    let curPtr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - cur.length)
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 559) hcl_s
    conv => arg 4; rw [skipGroupLoopPre3, sliceCursorAfter_eq_split hcur_le hcur_suf,
      skipBelow3_leaf s0.sp (d + 1) hdepth]
    wp_steps
    wp_reach
    intro hcl1
    refine SepWPp.call_frame_lscl (spec := decodeVarint2Spec A)
      (x := ⟨bufRef, slot, curPtr, cur⟩)
      (ret_pc := (blkPl_546).base + 240#64) hVarintCall hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
      (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeVarint2Spec, arm64_norm, hsp_s]; rfl)
      (⟨rfl, hcur_lt⟩ : bufRef = bufRef ∧ cur.length < 2 ^ 63)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hcl2
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
    dsimp only [decodeVarint2Spec]
    cases hd : decodeVarint cur with
    | none =>
      have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
      rw [hnone] at hres_cur
      subst hres_cur
      apply SepWPp.of_sepWP_ret
      simp only [sepConj_assoc, arm64_norm, htr_s, hsp_s]
      apply SepWP.pure_elim; intro hsm0
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
      wp_steps
      wp_done
    | some p =>
      rcases p with ⟨key, rest⟩
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ bs.length := by omega
      have hrest_lt : rest.length < 2 ^ 63 := by omega
      have hrest_suf : IsDropSuffix bs rest :=
        suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      by_cases hk_ge : 2 ^ 32 ≤ key.toNat
      · have hnone := skipGroup_of_key_ge (d := d) (tag := tag) hd hk_ge
        rw [hnone] at hres_cur
        subst hres_cur
        have hshr := key_shr32_of_ge hk_ge
        apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl2
        conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp_s]
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
          sliceCursorAt, memRegion_48_split2 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply SepWP.exists_elim; intro v_err0
        apply SepWP.exists_elim; intro v_err1
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 := pointsTo64_memRegion32_entails_40 s0.sp key
        rw [← bv_sub_add_lit s0.sp 96 8] at h40
        apply SepWP.fold h40 (by sep_focus)
        conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
        wp_reach
        intro hcl3
        refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpec A)
          (x := (s0.sp - 96#64, 0x8000000000000004#64))
          (ret_pc := (blkPl_546).base + 204#64) hFromCall hcl3
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [decodeErrorFromSpec, arm64_norm]; rfl)
          (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000004#64)
          (by sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex)
          (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr_s]) hpan) ?_
        intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hcl4
        simp only [CalleeSavedPreserved] at hcsm2
        obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
        simp (config := { decide := true }) only [arm64_norm, hspm, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
        apply SepWPp.of_sepWP_ret
        dsimp only [decodeErrorFromSpec, decodeErrorFromSpecWithStack]
        simp only [arm64_norm, htrm, htr_s, hspm]
        apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
        wp_steps
        wp_done
      · have hshr := key_shr32_of_lt hk_ge
        cases hwt : WireType.ofNat? (key.toNat % 8) with
        | none =>
          have hnone := skipGroup_of_wt_none (d := d) (tag := tag) hd hk_ge hwt
          rw [hnone] at hres_cur
          subst hres_cur
          obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
          apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl2
          conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp_s]
          apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
            sliceCursorAt, memRegion_48_split2 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWP.exists_elim; intro v_err0
          apply SepWP.exists_elim; intro v_err1
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          have h40 := pointsTo64_memRegion32_entails_40 s0.sp (key &&& 7#64)
          rw [← bv_sub_add_lit s0.sp 96 8] at h40
          apply SepWP.fold h40 (by sep_focus)
          conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
          wp_reach
          intro hcl3
          refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpec A)
            (x := (s0.sp - 96#64, 0x8000000000000003#64))
            (ret_pc := (blkPl_546).base + 204#64) hFromCall hcl3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [decodeErrorFromSpec, arm64_norm]; rfl)
            (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000003#64)
            (by sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr_s]) hpan) ?_
          intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hcl4
          simp only [CalleeSavedPreserved] at hcsm2
          obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
          simp (config := { decide := true }) only [arm64_norm, hspm, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
          apply SepWPp.of_sepWP_ret
          dsimp only [decodeErrorFromSpec, decodeErrorFromSpecWithStack]
          simp only [arm64_norm, htrm, htr_s, hspm]
          apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
          wp_steps
          wp_done
        | some iwt =>
          obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
          obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
          obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
          by_cases hitag0 : key.toNat / 8 < 1
          · have hnone := skipGroup_of_tag_zero (d := d) (tag := tag) hd hk_ge hwt hitag0
            rw [hnone] at hres_cur
            subst hres_cur
            have htag_zero : key.toNat / 8 = 0 := by omega
            apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl2
            conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp_s]
            apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
            apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
            conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
              sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWP.exists_elim; intro v_err0
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
            conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
            wp_reach
            intro hcl3
            refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpec A)
              (x := (s0.sp - 96#64, 0x8000000000000005#64))
              (ret_pc := (blkPl_546).base + 204#64) hFromCall hcl3
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
              (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [decodeErrorFromSpec, arm64_norm]; rfl)
              (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000005#64)
              (by sep_focus)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr_s]) hpan) ?_
            intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hcl4
            simp only [CalleeSavedPreserved] at hcsm2
            obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
            simp (config := { decide := true }) only [arm64_norm, hspm, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
            apply SepWPp.of_sepWP_ret
            dsimp only [decodeErrorFromSpec, decodeErrorFromSpecWithStack]
            simp only [arm64_norm, htrm, htr_s, hspm]
            apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            wp_done
          · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
            have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
            by_cases hiwt_eg : iwt = .endGroup
            · subst hiwt_eg
              dsimp [WireType.toNat] at hand_wt hcc1_wt hcc2_wt
              have heg := skipGroup_of_endGroup (d := d) (tag := tag) hd hk_ge hwt hitag0
              rw [heg] at hres_cur
              by_cases hitag_eq : key.toNat / 8 = tag
              · simp only [hitag_eq, ↓reduceIte] at hres_cur
                subst hres_cur
                rw [hitag_eq] at hw1 hw1_2 hw1_zext1 hw1_zext2 hcbz_tag1 hcbz_tag2
                apply SepWPp.of_sepWP_ret
                simp only [sepConj_assoc, arm64_norm, htr_s, hsp_s]
                apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
                apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
                apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
                simp only [sliceCursorAfter]
                wp_steps
                wp_done
              · simp only [hitag_eq, ↓reduceIte] at hres_cur
                subst hres_cur
                obtain ⟨hne_bv1, hne_bv2⟩ := itag_beq_tag_false hitag_eq hitag_lt htag_lt
                apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl2
                conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp_s]
                apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
                apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
                apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
                conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
                  sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
                simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
                apply SepWP.exists_elim; intro v_err0
                wp_steps
                apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
                apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
                wp_reach
                intro hcl3
                refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpec A)
                  (x := (s0.sp - 96#64, 0x8000000000000009#64))
                  (ret_pc := (blkPl_546).base + 204#64) hFromCall hcl3
                  (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                  (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
                  (by simp only [arm64_norm])
                  (by simp only [decodeErrorFromSpec, arm64_norm]; rfl)
                  (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000009#64)
                  (by sep_focus)
                  (fun _ _ _ _ hex => allowPanic_not_exited hex)
                  (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr_s]) hpan) ?_
                intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hcl4
                simp only [CalleeSavedPreserved] at hcsm2
                obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
                simp (config := { decide := true }) only [arm64_norm, hspm, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
                apply SepWPp.of_sepWP_ret
                dsimp only [decodeErrorFromSpec, decodeErrorFromSpecWithStack]
                simp only [arm64_norm, htrm, htr_s, hspm]
                apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
                wp_steps
                wp_done
            · have hne_eg := skipGroup_of_ne_endGroup (d := d) (tag := tag) hd hk_ge hwt hitag0 hiwt_eg
              rw [hne_eg] at hres_cur
              have hiwt_ne4 := iwt_beq_4_false hiwt_eg
              obtain ⟨hiwt_w0_1, hiwt_w0_2⟩ := iwt_w0_setWidth8 iwt
              have hd_lt : d < 2 ^ 32 := by omega
              apply SepWPp.of_sepWP_lscl (mid := (blkPl_546).base) hcl2
              conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp_s]
              apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
              apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
                show skipBelow3 s0.sp (d + 1) = stackAt sm.sp (skipField3Stack d) from by
                  rw [hspm]]
              simp only [sepConj_assoc]
              wp_steps
              wp_reach
              intro hcl3
              refine SepWPp.call_frame_lscl
                (spec := skipField3SpecAt A d (fun _ => True))
                (x := ⟨iwt, key.toNat / 8, d, bufRef, slot,
                  ptr + BitVec.ofNat 64 (bs.length - rest.length), rest⟩)
                (ret_pc := (blkPl_546).base + 304#64) hrec_cl hcl3
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [skipField3SpecAt, arm64_norm]; rfl)
                ?_
                (by sep_focus)
                (fun _ _ _ _ hex => allowPanic_not_exited hex)
                (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr_s]) hpan) ?_
              · simp only [arm64_norm, hiwt_w0_2, sf_truncate32_ofNat64]
                exact ⟨hitag_lt, hd_lt, hrest_lt⟩
              intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hcl4
              simp only [CalleeSavedPreserved] at hcsm2
              obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
              simp (config := { decide := true }) only [arm64_norm, hspm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
              dsimp only [skipField3SpecAt]
              cases hs : skipField (2 * rest.length + 2) d (key.toNat / 8) iwt rest with
              | none =>
                rw [hs] at hres_cur
                dsimp only at hres_cur
                subst hres_cur
                apply SepWPp.of_sepWP_ret
                simp only [sepConj_assoc, arm64_norm, htrm, htr_s, hspm]
                apply SepWP.pure_elim; rintro ⟨htrm2, hsm2_0⟩
                have hcbz_sm0 : (sm2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm2_0
                conv => arg 4; rw [show stackAt (s0.sp - 96#64) (skipField3Stack d) = skipBelow3 s0.sp (d + 1) from rfl]
                apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                wp_steps
                wp_done
              | some rest' =>
                rw [hs] at hres_cur
                dsimp only at hres_cur
                have hrest'_le_rest : rest'.length ≤ rest.length :=
                  (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hs
                have hrest'_le_n : rest'.length ≤ n := by omega
                have hrest'_le_bs : rest'.length ≤ bs.length := by omega
                have hrest'_suf : IsDropSuffix bs rest' :=
                  suffix_trans hrest_le hrest_suf hrest'_le_rest
                    ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hs)
                apply SepWPp.of_sepWP_lscl (mid := (blkPl_546).base + 232#64) hcl4
                conv => arg 4; simp only [sepConj_assoc, arm64_norm, hspm]
                apply SepWP.pure_elim; rintro ⟨htrm2, hsm2_0⟩
                conv => arg 4; rw [show stackAt (s0.sp - 96#64) (skipField3Stack d) = skipBelow3 s0.sp (d + 1) from rfl]
                apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le_rest) (by sep_focus)
                wp_steps
                wp_reach
                intro hcl5
                apply SepWPp.weaken_pre (P' := skipGroupLoopPre3 A s0 d bufRef slot ptr v_stk_2 bs rest')
                  (Entails.of_eq (by dsimp only [skipGroupLoopPre3]; ac_rfl))
                refine ih rest' _ hrest'_le_n hrest'_le_bs hrest'_suf hres_cur
                  ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcl5
                · simp only [arm64_norm]
                · simp only [arm64_norm, hrunm2]
                · simp only [arm64_norm, hspm2]
                · simp only [arm64_norm, htrm2, htrm, htr_s]
                · simp only [arm64_norm, hx19_2]
                · simp only [arm64_norm, hx20_2]
                · simp only [arm64_norm, hx21_2]
                · simp only [arm64_norm, hx22_2]
                · simp only [arm64_norm, hx23_2]
                · simp only [arm64_norm, hx24_2]
                · simp only [arm64_norm, hx25_2]
                · simp only [arm64_norm, hx26_2]
                · simp only [arm64_norm, hx27_2]
                · simp only [arm64_norm, hx28_2]
                · simp only [arm64_norm, hvregs_2]

/-! ## Combine all `WireType` cases by induction on `depth` -/

theorem _root_.CryptoVerification.CliC.SpqrV1.Varint.skipField3_at_depth_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_546 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpec A)))
    (hVarintCall : subroutine_ok (lsProg_546 H) (lsmpl.base 559)
      (withLsCl lsmpl (decodeVarint2Spec A)))
    (depth : Nat) (hdepth : depth < 2 ^ 32) :
    subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A depth (fun _ => True))) := by
  induction depth with
  | zero => exact CryptoVerification.CliC.SpqrV1.Varint.skipField3_depth_zero_placed_ok hFromCall
  | succ d ih =>
    have hrec := ih (by omega)
    have hAll :=
      subroutine_ok_skipField3_or_lscl
        (CryptoVerification.CliC.SpqrV1.Varint.skipField3_varint_placed_ok hVarintCall d hdepth)
        (subroutine_ok_skipField3_or_lscl
          (CryptoVerification.CliC.SpqrV1.Varint.skipField3_sixtyFourBit_placed_ok hFromCall d hdepth)
          (subroutine_ok_skipField3_or_lscl
            (CryptoVerification.CliC.SpqrV1.Varint.skipField3_lengthDelimited_placed_ok hFromCall hVarintCall d hdepth)
            (subroutine_ok_skipField3_or_lscl
              (CryptoVerification.CliC.SpqrV1.Varint.skipField3_startGroup_placed_ok hFromCall hVarintCall d hdepth hrec)
              (subroutine_ok_skipField3_or_lscl
                (CryptoVerification.CliC.SpqrV1.Varint.skipField3_endGroup_placed_ok hFromCall d hdepth)
                (CryptoVerification.CliC.SpqrV1.Varint.skipField3_thirtyTwoBit_placed_ok hFromCall d hdepth)))))
    refine subroutine_ok_skipField3_imp_lscl (fun x _ => ?_) hAll
    cases x.wt <;> simp

theorem _root_.CryptoVerification.CliC.SpqrV1.Varint.skipField3_placed_ok_of_contracts
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (blkPl_261).base
      (decodeErrorFromSpec A))
    (hVarint : subroutine_ok (lsProg_559 H) (blkPl_559).base
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A))) :
    subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3Spec A)) :=
  subroutine_ok_skipField3Spec_of_at_depth_lscl
    (CryptoVerification.CliC.SpqrV1.Varint.skipField3_at_depth_placed_ok
      (ls_subroutine_ok_cl_of_plain (callerProg := lsProg_546 H) hFrom)
      (ls_subroutine_ok_cl_of_block (callerProg := lsProg_546 H) hVarint))

theorem _root_.CryptoVerification.CliC.SpqrV1.Varint.skipField3_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3Spec A)) :=
  CryptoVerification.CliC.SpqrV1.Varint.skipField3_placed_ok_of_contracts
    (decode_error_from_placed_ok_gen hshim halloc hpanic)
    (CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_placed_ok hshim halloc hpanic)

end CryptoVerification.SpqrV1.Varint
