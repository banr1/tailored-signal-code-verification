/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


theorem skipField_startGroup_ok_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hSlowCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeVarintSlowSpecX A).inImage img))
    (hSliceCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeVarintSliceSpecX A).inImage img))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32)
    (hrec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName)
      ((skipFieldSpecAtX A d (fun _ => True)).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName)
      ((skipFieldSpecAtX A (d + 1) (fun x => x.wt = .startGroup)).inImage img) := by
  unfold skipFieldSpecAtX
  simp only [sliceCursorAt, stackAt_skipFieldX _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_inImage x s0 hfl0 hsym0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]")
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base H hfn (num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]")) 0 720
  dsimp only [skipFieldName] at *
  have _hpc_e : s0.pc = (CryptoVerification.libsignalSessionCode.rebase img.base H).fnAddr "prost::encoding::skip_field::<&mut &[u8]> [local#1]" := by
    first | exact hpc | exact hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear hpc; have hpc := _hpc_e; clear _hpc_e
  generalize_entry (CryptoVerification.libsignalSessionCode.rebase img.base H).fnAddr "prost::encoding::skip_field::<&mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  obtain ⟨htag_zext1, htag_zext2⟩ := bv32_zeroExtend_ofNat h_5
  obtain ⟨hd_zext1, hd_zext2⟩ := bv32_zeroExtend_ofNat (by omega : d < 2 ^ 32)
  obtain ⟨hd_sub1, hd_sub2⟩ := bv32_sub_one_zeroExtend hdepth
  rw [skipField_succ_startGroup]
  generalize hres : skipGroup (2 * bs.length + 1) (d + 1) tag bs = res
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  apply SepWPp.of_sepWP_inv hfl0 hsym0 (mid := entry + bv% (192))
  wp_steps
  wp_reach
  intro hfl_init hsym_init
  apply SepWPp.weaken_pre (P' := skipGroupLoopPreX A s0 d bufRef slot ptr bs bs)
    (Entails.of_eq (by dsimp only [skipGroupLoopPreX]; simp only [sliceCursorAfter, Nat.sub_self,
      BitVec.add_zero]; ac_rfl))
  refine (fun (Q_f Qp_f : State → SepProp → Prop)
      (hloop : ∀ n (cur : List (BitVec 8)) (s : State),
        cur.length ≤ n →
        cur.length ≤ bs.length →
        IsDropSuffix bs cur →
        skipGroup (2 * cur.length + 1) (d + 1) tag cur = res →
        s.pc = entry + bv% (192) →
        s.status = .Running →
        s.sp = s0.sp - 96#64 →
        s.trace = s0.trace →
        s.readReg64 (Reg.gpr 19#5) = bufRef →
        s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
        s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
        HighCalleeSaved s0 s →
        img.FrozenLoaded s →
        s.symtab = img.symtab →
        SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
          (skipGroupLoopPreX A s0 d bufRef slot ptr bs cur) Q_f Qp_f) =>
      hloop bs.length bs _ (Nat.le_refl _) (Nat.le_refl _) (by simp [IsDropSuffix]) hres
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm]⟩
        hfl_init hsym_init)
    _ _ ?_
  intro n
  induction n with
  | zero =>
    intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hfl_s hsym_s
    obtain ⟨hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
    cases cur with
    | nil =>
      have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) (cur := []) rfl
      rw [hnone] at hres_cur
      subst hres_cur
      apply SepWPp.of_sepWP_inv hfl_s hsym_s (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hcur_le hcur_suf,
        sliceCursorAt, pointsToBytes_nil, sepConj_emp,
        memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
      simp only [List.length_nil, sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - 0)) 0#64) (by sep_focus)
      conv => arg 4; rw [Nat.sub_zero, List.take_length, skipBelowX_err s0.sp (d + 1) hdepth, ← hsp_s]
      wp_reach
      intro hfl_err hsym_err
      refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000001#64))
        (ret_pc := entry + bv% (652)) hFromCall hfl_err hsym_err
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
        (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
        (by simp only [arm64_norm])
        (by simp only [arm64_norm]; rfl)
        (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000001#64)
        (by sep_focus)
        (fun _ _ _ _ hex => allowPanic_not_exited hex)
        (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
      intro sm hpcm hrunm hspm hcsm _ _
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, hsp_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
      apply SepWPp.of_sepWP_ret
      simp only [arm64_norm, htr_s, hsp_s]
      apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps
      wp_done
    | cons b0 bs1 =>
      simp only [List.length_cons] at hcur_n
      omega
  | succ n ih =>
    intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hfl_s hsym_s
    cases cur with
    | nil =>
      exact ih [] s (by simp) hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hfl_s hsym_s
    | cons b0 bs1 =>
      obtain ⟨hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
      have hcur_lt : (b0 :: bs1).length < 2 ^ 63 := by omega
      have hcbz_len := cbz_len_cons_false hcur_lt
      let curPtr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - (b0 :: bs1).length)
      refine (fun (Q_f Qp_f : State → SepProp → Prop)
          (hafter : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
            decodeVarint (b0 :: bs1) = some (key, rest) →
            s1.pc = entry + bv% (296) →
            s1.status = .Running →
            s1.sp = s0.sp - 96#64 →
            s1.trace = s0.trace →
            s1.readReg64 (Reg.gpr 0#5) = key →
            s1.readReg64 (Reg.gpr 19#5) = bufRef →
            s1.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
            s1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
            HighCalleeSaved s0 s1 →
            img.FrozenLoaded s1 →
            s1.symtab = img.symtab →
            SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s1
              (skipGroupLoopPreX A s0 d bufRef slot ptr bs rest) Q_f Qp_f)
          (hbody : (∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
            decodeVarint (b0 :: bs1) = some (key, rest) →
            s1.pc = entry + bv% (296) →
            s1.status = .Running →
            s1.sp = s0.sp - 96#64 →
            s1.trace = s0.trace →
            s1.readReg64 (Reg.gpr 0#5) = key →
            s1.readReg64 (Reg.gpr 19#5) = bufRef →
            s1.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
            s1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
            HighCalleeSaved s0 s1 →
            img.FrozenLoaded s1 →
            s1.symtab = img.symtab →
            SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s1
              (skipGroupLoopPreX A s0 d bufRef slot ptr bs rest) Q_f Qp_f) →
            SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
              (skipGroupLoopPreX A s0 d bufRef slot ptr bs (b0 :: bs1)) Q_f Qp_f) =>
          hbody hafter)
        _ _ ?_ ?_
      · intro key rest s1 hd hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hcs1 hfl1 hsym1
        obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
        have hrest_lt_cur : rest.length < (b0 :: bs1).length := decodeVarint_length hd
        have hrest_le : rest.length ≤ bs.length := by omega
        have hrest_lt : rest.length < 2 ^ 63 := by omega
        have hrest_suf : IsDropSuffix bs rest :=
          suffix_trans hcur_le hcur_suf (Nat.le_of_lt hrest_lt_cur) (decodeVarint_suffix hd)
        by_cases hk_ge : 2 ^ 32 ≤ key.toNat
        · have hnone := skipGroup_of_key_ge (d := d) (tag := tag) hd hk_ge
          rw [hnone] at hres_cur
          subst hres_cur
          have hshr := key_shr32_of_ge hk_ge
          apply SepWPp.of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
          conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
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
          conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hsp1]
          wp_reach
          intro hfl_err hsym_err
          refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000004#64))
            (ret_pc := entry + bv% (652)) hFromCall hfl_err hsym_err
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
            (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000004#64)
            (by sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
          intro sm hpcm hrunm hspm hcsm _ _
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm, hsp1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          apply SepWPp.of_sepWP_ret
          simp only [arm64_norm, htr1, hsp1]
          apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
          wp_steps
          wp_done
        · have hshr := key_shr32_of_lt hk_ge
          cases hwt : WireType.ofNat? (key.toNat % 8) with
          | none =>
            have hnone := skipGroup_of_wt_none (d := d) (tag := tag) hd hk_ge hwt
            rw [hnone] at hres_cur
            subst hres_cur
            obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
            apply SepWPp.of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
            conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
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
            conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hsp1]
            wp_reach
            intro hfl_err hsym_err
            refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000003#64))
              (ret_pc := entry + bv% (652)) hFromCall hfl_err hsym_err
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
              (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [arm64_norm]; rfl)
              (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000003#64)
              (by sep_focus)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
            intro sm hpcm hrunm hspm hcsm _ _
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm, hsp1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            apply SepWPp.of_sepWP_ret
            simp only [arm64_norm, htr1, hsp1]
            apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
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
              apply SepWPp.of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
              conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
                sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_err0
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
              conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hsp1]
              wp_reach
              intro hfl_err hsym_err
              refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000005#64))
                (ret_pc := entry + bv% (652)) hFromCall hfl_err hsym_err
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
                (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [arm64_norm]; rfl)
                (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000005#64)
                (by sep_focus)
                (fun _ _ _ _ hex => allowPanic_not_exited hex)
                (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
              intro sm hpcm hrunm hspm hcsm _ _
              simp only [CalleeSavedPreserved] at hcsm
              obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
              simp (config := { decide := true }) only [arm64_norm, hsp1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
              apply SepWPp.of_sepWP_ret
              simp only [arm64_norm, htr1, hsp1]
              apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
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
                  simp only [skipGroupLoopPreX, sliceCursorAfter]
                  wp_steps
                  wp_done
                · simp only [hitag_eq, ↓reduceIte] at hres_cur
                  subst hres_cur
                  obtain ⟨hne_bv1, hne_bv2⟩ := itag_beq_tag_false hitag_eq hitag_lt h_5
                  apply SepWPp.of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
                  conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
                    sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
                  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
                  apply SepWP.exists_elim; intro v_err0
                  wp_steps
                  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
                  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                  conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hsp1]
                  wp_reach
                  intro hfl_err hsym_err
                  refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000009#64))
                    (ret_pc := entry + bv% (652)) hFromCall hfl_err hsym_err
                    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
                    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
                    (by simp only [arm64_norm])
                    (by simp only [arm64_norm]; rfl)
                    (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000009#64)
                    (by sep_focus)
                    (fun _ _ _ _ hex => allowPanic_not_exited hex)
                    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
                  intro sm hpcm hrunm hspm hcsm _ _
                  simp only [CalleeSavedPreserved] at hcsm
                  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
                  simp (config := { decide := true }) only [arm64_norm, hsp1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
                  apply SepWPp.of_sepWP_ret
                  simp only [arm64_norm, htr1, hsp1]
                  apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
                  wp_steps
                  wp_done
              · have hne_eg := skipGroup_of_ne_endGroup (d := d) (tag := tag) hd hk_ge hwt hitag0 hiwt_eg
                rw [hne_eg] at hres_cur
                have hiwt_ne4 := iwt_beq_4_false hiwt_eg
                obtain ⟨hiwt_w0_1, hiwt_w0_2⟩ := iwt_w0_setWidth8 iwt
                have hd_lt : d < 2 ^ 32 := by omega
                apply SepWPp.of_sepWP_inv hfl1 hsym1 (mid := entry)
                conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
                  show skipBelowX s0.sp (d + 1) = stackAt s1.sp (skipFieldStackX d) from by
                    rw [hsp1]]
                simp only [sepConj_assoc]
                wp_steps
                wp_reach
                intro hfl_rec hsym_rec
                refine SepWPp.call_frame_inv
                  (x := ⟨iwt, key.toNat / 8, d, bufRef, slot,
                    ptr + BitVec.ofNat 64 (bs.length - rest.length), rest⟩)
                  (ret_pc := entry + bv% (348)) hrec hfl_rec hsym_rec
                  (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
                  (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
                  (by simp only [arm64_norm])
                  (by simp only [arm64_norm]; rfl)
                  ?_
                  (by sep_focus)
                  (fun _ _ _ _ hex => allowPanic_not_exited hex)
                  (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
                · simp only [arm64_norm, hiwt_w0_2, sf_truncate32_ofNat64]
                  exact ⟨hitag_lt, hd_lt, hrest_lt⟩
                intro sm hpcm hrunm hspm hcsm hflm hsymm
                simp only [CalleeSavedPreserved] at hcsm
                obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
                simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
                cases hs : skipField (2 * rest.length + 2) d (key.toNat / 8) iwt rest with
                | none =>
                  rw [hs] at hres_cur
                  dsimp only at hres_cur
                  subst hres_cur
                  apply SepWPp.of_sepWP_ret
                  simp only [hs, sepConj_assoc, arm64_norm, hsp1]
                  apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
                  have hcbz_sm0 : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
                  conv => arg 4; rw [show stackAt (s0.sp - 96#64) (skipFieldStackX d) = skipBelowX s0.sp (d + 1) from rfl]
                  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                  wp_steps
                  wp_done
                | some rest' =>
                  rw [hs] at hres_cur
                  dsimp only at hres_cur
                  have hrest'_le_rest : rest'.length ≤ rest.length :=
                    (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hs
                  have hrest'_le_n : rest'.length ≤ n := by
                    simp only [List.length_cons] at hcur_n hrest_lt_cur
                    omega
                  have hrest'_le_bs : rest'.length ≤ bs.length := by omega
                  have hrest'_suf : IsDropSuffix bs rest' :=
                    suffix_trans hrest_le hrest_suf hrest'_le_rest
                      ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hs)
                  apply SepWPp.of_sepWP_inv hflm hsymm (mid := entry + bv% (192))
                  conv => arg 4; simp only [skipFieldSpecAtX, hs, sepConj_assoc, arm64_norm, hsp1]
                  apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
                  conv => arg 4; rw [show stackAt (s0.sp - 96#64) (skipFieldStackX d) = skipBelowX s0.sp (d + 1) from rfl]
                  apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le_rest) (by sep_focus)
                  wp_steps
                  wp_reach
                  intro hfl_next hsym_next
                  apply SepWPp.weaken_pre (P' := skipGroupLoopPreX A s0 d bufRef slot ptr bs rest')
                    (Entails.of_eq (by dsimp only [skipGroupLoopPreX]; ac_rfl))
                  refine ih rest' _ hrest'_le_n hrest'_le_bs hrest'_suf hres_cur
                    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hfl_next hsym_next
                  · simp only [arm64_norm]
                  · simp only [arm64_norm, hrunm]
                  · simp only [arm64_norm, hspm]
                  · simp only [arm64_norm, htrm, htr1]
                  · simp only [arm64_norm, hx19]
                  · simp only [arm64_norm, hx20]
                  · simp only [arm64_norm, hx21]
                  · simp only [arm64_norm, hx23]
                  · simp only [arm64_norm, hx24]
                  · simp only [arm64_norm, hx25]
                  · simp only [arm64_norm, hx26]
                  · simp only [arm64_norm, hx27]
                  · simp only [arm64_norm, hx28]
                  · simp only [arm64_norm, hvregs]
      · intro hafter
        by_cases hb0 : b0 ≤ 0x7f#8
        · have hbit0 := signExtend64_getLsbD_63_of_le hb0
          have hd := decodeVarint_1 bs1 hb0
          have hbs1_le : bs1.length ≤ (b0 :: bs1).length := by simp
          apply SepWPp.of_sepWP_inv hfl_s hsym_s (mid := entry + bv% (296))
          conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hcur_le hcur_suf,
            sliceCursorAt, pointsToBytes_cons]
          wp_steps
          conv => arg 4; rw [len_cons_sub_one b0 bs1, ← pointsToBytes_cons]
          have hcur_after :
              (slot ↦₆₄ (curPtr + 1#64)) ∗
                ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
                (curPtr ↦ₛ (b0 :: bs1)) ⊢
                sliceCursorAfter slot curPtr (b0 :: bs1) bs1 := by
            simp only [sliceCursorAfter, List.length_cons, Nat.add_sub_cancel_left]
            exact Entails.refl _
          apply SepWP.fold hcur_after (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hbs1_le) (by sep_focus)
          wp_reach
          intro hfl1 hsym1
          apply SepWPp.weaken_pre (P' := skipGroupLoopPreX A s0 d bufRef slot ptr bs bs1)
            (Entails.of_eq (by dsimp only [skipGroupLoopPreX]; ac_rfl))
          refine hafter ((b0 &&& 0x7f#8).zeroExtend 64) bs1 _ hd
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hfl1 hsym1
          · simp only [arm64_norm]
          · simp only [arm64_norm, hrun_s]
          · simp only [arm64_norm, hsp_s]
          · simp only [arm64_norm, htr_s]
          · simp only [arm64_norm, signExtend64_eq_and_0x7f hb0]
          · simp only [arm64_norm, hx19_s]
          · simp only [arm64_norm, hx20_s]
          · simp only [arm64_norm, hx21_s]
          · simp only [arm64_norm, hx23_s]
          · simp only [arm64_norm, hx24_s]
          · simp only [arm64_norm, hx25_s]
          · simp only [arm64_norm, hx26_s]
          · simp only [arm64_norm, hx27_s]
          · simp only [arm64_norm, hx28_s]
          · simp only [arm64_norm, hvregs_s]
        · have hbit0 := signExtend64_getLsbD_63_of_gt hb0
          have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          by_cases h11 : 11 ≤ (b0 :: bs1).length
          · have hhi := ult_10_of_ge_11 h11 hcur_lt
            have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
            apply SepWPp.of_sepWP_inv hfl_s hsym_s (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
            conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hcur_le hcur_suf,
              sliceCursorAt, pointsToBytes_cons, memRegion_48_skipSlice s0.sp,
              skipBelowX_leaf s0.sp (d + 1) hdepth]
            wp_steps
            wp_reach
            intro hfl_sl hsym_sl
            refine SepWPp.call_frame_inv (x := ⟨s0.sp - 96#64, curPtr, b0 :: bs1⟩)
              (ret_pc := entry + bv% (256)) hSliceCall hfl_sl hsym_sl
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
              (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [arm64_norm, hsp_s, curPtr]; rfl)
              (⟨rfl, rfl, hlen_toNat, hcur_lt, hpre_slice⟩ :
                s0.sp - 96#64 = s0.sp - 96#64 ∧ curPtr = curPtr ∧
                  (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                  (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
              (by sep_focus)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
            intro sm hpcm hrunm hspm hcsm hflm hsymm
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            cases hd : decodeVarint (b0 :: bs1) with
            | none =>
              have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
              rw [hnone] at hres_cur
              subst hres_cur
              apply SepWPp.of_sepWP_ret
              simp only [hd, varintSliceResultAt, sepExists_sepConj_left, arm64_norm, htr_s, hsp_s]
              apply SepWP.exists_elim; intro e_err
              apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot curPtr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
              apply SepWP.fold (skipSliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
              wp_done
            | some p =>
              rcases p with ⟨key, rest⟩
              have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
              have hcc := len_ult_consumed_false (rest := rest) hcur_lt
              have hsub_len := bv_len_sub_consumed hd
              apply SepWPp.of_sepWP_inv hflm hsymm (mid := entry + bv% (296))
              conv => arg 4; simp only [hd, varintSliceResultAt, sepConj_assoc, arm64_norm, hsp_s]
              apply SepWP.pure_elim; intro htrm
              apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
              apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 key (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
              have hcur_after :
                  (slot ↦₆₄ (curPtr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) ∗
                    ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
                    (curPtr ↦ₛ (b0 :: bs1)) ⊢
                    sliceCursorAfter slot curPtr (b0 :: bs1) rest :=
                Entails.refl _
              apply SepWP.fold hcur_after (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le) (by sep_focus)
              wp_reach
              intro hfl1 hsym1
              apply SepWPp.weaken_pre (P' := skipGroupLoopPreX A s0 d bufRef slot ptr bs rest)
                (Entails.of_eq (by dsimp only [skipGroupLoopPreX]; ac_rfl))
              refine hafter key rest _ hd
                ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hfl1 hsym1
              · simp only [arm64_norm]
              · simp only [arm64_norm, hrunm]
              · simp only [arm64_norm, hspm]
              · simp only [arm64_norm, htrm, htr_s]
              · simp only [arm64_norm]
              · simp only [arm64_norm, hx19]
              · simp only [arm64_norm, hx20]
              · simp only [arm64_norm, hx21]
              · simp only [arm64_norm, hx23]
              · simp only [arm64_norm, hx24]
              · simp only [arm64_norm, hx25]
              · simp only [arm64_norm, hx26]
              · simp only [arm64_norm, hx27]
              · simp only [arm64_norm, hx28]
              · simp only [arm64_norm, hvregs]
          · have hhi := ult_10_of_lt_11 h11 hcur_lt
            have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
            apply SepWPp.of_sepWP_inv hfl_s hsym_s (mid := entry + bv% (244))
            conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hcur_le hcur_suf,
              sliceCursorAt, pointsToBytes_cons]
            wp_steps
            conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last curPtr (b0 :: bs1) hne_cons hcur_lt]
            wp_steps
            conv => arg 4; rw [← pointsToBytes_split_last curPtr (b0 :: bs1) hne_cons hcur_lt]
            wp_reach
            intro hfl_244 hsym_244
            by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
            · have hbit_last := getLsbD_7_of_le hlast
              have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
              apply SepWPp.of_sepWP_inv hfl_244 hsym_244 (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
              conv => arg 4; rw [pointsToBytes_cons, memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
              wp_steps
              wp_reach
              intro hfl_sl hsym_sl
              refine SepWPp.call_frame_inv (x := ⟨s0.sp - 96#64, curPtr, b0 :: bs1⟩)
                (ret_pc := entry + bv% (256)) hSliceCall hfl_sl hsym_sl
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
                (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [arm64_norm, hsp_s, curPtr]; rfl)
                (⟨rfl, rfl, hlen_toNat, hcur_lt, hpre_slice⟩ :
                  s0.sp - 96#64 = s0.sp - 96#64 ∧ curPtr = curPtr ∧
                    (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                    (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
                (by sep_focus)
                (fun _ _ _ _ hex => allowPanic_not_exited hex)
                (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
              intro sm hpcm hrunm hspm hcsm hflm hsymm
              simp only [CalleeSavedPreserved] at hcsm
              obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
              simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
              cases hd : decodeVarint (b0 :: bs1) with
              | none =>
                have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
                rw [hnone] at hres_cur
                subst hres_cur
                apply SepWPp.of_sepWP_ret
                simp only [hd, varintSliceResultAt, sepExists_sepConj_left, arm64_norm, htr_s, hsp_s]
                apply SepWP.exists_elim; intro e_err
                apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
                wp_steps
                apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
                apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot curPtr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
                apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
                apply SepWP.fold (skipSliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
                wp_done
              | some p =>
                rcases p with ⟨key, rest⟩
                have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
                have hcc := len_ult_consumed_false (rest := rest) hcur_lt
                have hsub_len := bv_len_sub_consumed hd
                apply SepWPp.of_sepWP_inv hflm hsymm (mid := entry + bv% (296))
                conv => arg 4; simp only [hd, varintSliceResultAt, sepConj_assoc, arm64_norm, hsp_s]
                apply SepWP.pure_elim; intro htrm
                apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
                wp_steps
                apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
                apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 key (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
                have hcur_after :
                    (slot ↦₆₄ (curPtr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) ∗
                      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
                      (curPtr ↦ₛ (b0 :: bs1)) ⊢
                      sliceCursorAfter slot curPtr (b0 :: bs1) rest :=
                  Entails.refl _
                apply SepWP.fold hcur_after (by sep_focus)
                apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le) (by sep_focus)
                wp_reach
                intro hfl1 hsym1
                apply SepWPp.weaken_pre (P' := skipGroupLoopPreX A s0 d bufRef slot ptr bs rest)
                  (Entails.of_eq (by dsimp only [skipGroupLoopPreX]; ac_rfl))
                refine hafter key rest _ hd
                  ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hfl1 hsym1
                · simp only [arm64_norm]
                · simp only [arm64_norm, hrunm]
                · simp only [arm64_norm, hspm]
                · simp only [arm64_norm, htrm, htr_s]
                · simp only [arm64_norm]
                · simp only [arm64_norm, hx19]
                · simp only [arm64_norm, hx20]
                · simp only [arm64_norm, hx21]
                · simp only [arm64_norm, hx23]
                · simp only [arm64_norm, hx24]
                · simp only [arm64_norm, hx25]
                · simp only [arm64_norm, hx26]
                · simp only [arm64_norm, hx27]
                · simp only [arm64_norm, hx28]
                · simp only [arm64_norm, hvregs]
            · have hbit_last := getLsbD_7_of_gt hlast
              apply SepWPp.of_sepWP_inv hfl_244 hsym_244 (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
              wp_steps
              conv => arg 4; rw [skipBelowX_slow s0.sp (d + 1) hdepth]
              simp only [sepConj_assoc]
              wp_reach
              intro hfl_slw hsym_slw
              refine SepWPp.call_frame_inv (x := ⟨bufRef, slot, curPtr, b0 :: bs1⟩)
                (ret_pc := entry + bv% (364)) hSlowCall hfl_slw hsym_slw
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
                (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [arm64_norm, hsp_s]; rfl)
                (⟨rfl, hcur_lt⟩ : bufRef = bufRef ∧ (b0 :: bs1).length < 2 ^ 63)
                (by simp only [sliceCursorAt]; sep_focus)
                (fun _ _ _ _ hex => allowPanic_not_exited hex)
                (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
              intro sm hpcm hrunm hspm hcsm hflm hsymm
              simp only [CalleeSavedPreserved] at hcsm
              obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
              simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
              cases hd : decodeVarint (b0 :: bs1) with
              | none =>
                have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
                rw [hnone] at hres_cur
                subst hres_cur
                apply SepWPp.of_sepWP_ret
                simp only [hd, sepConj_assoc, arm64_norm, htr_s, hsp_s]
                apply SepWP.pure_elim; intro hsm0
                apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
                apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
                apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
                wp_steps
                wp_done
              | some p =>
                rcases p with ⟨key, rest⟩
                have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
                apply SepWPp.of_sepWP_inv hflm hsymm (mid := entry + bv% (296))
                conv => arg 4; simp only [decodeVarintSlowSpecX, hd, sepConj_assoc, arm64_norm, hsp_s]
                apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
                apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
                apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le) (by sep_focus)
                wp_steps
                wp_reach
                intro hfl1 hsym1
                apply SepWPp.weaken_pre (P' := skipGroupLoopPreX A s0 d bufRef slot ptr bs rest)
                  (Entails.of_eq (by dsimp only [skipGroupLoopPreX]; ac_rfl))
                refine hafter key rest _ hd
                  ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hfl1 hsym1
                · simp only [arm64_norm]
                · simp only [arm64_norm, hrunm]
                · simp only [arm64_norm, hspm]
                · simp only [arm64_norm, htrm, htr_s]
                · simp only [arm64_norm]
                · simp only [arm64_norm, hx19]
                · simp only [arm64_norm, hx20]
                · simp only [arm64_norm, hx21]
                · simp only [arm64_norm, hx23]
                · simp only [arm64_norm, hx24]
                · simp only [arm64_norm, hx25]
                · simp only [arm64_norm, hx26]
                · simp only [arm64_norm, hx27]
                · simp only [arm64_norm, hx28]
                · simp only [arm64_norm, hvregs]

private theorem call_inv_lscl {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hclm : LibsignalCodeLoaded pl sm.mem := hcl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hclm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact (hoom sm _ hoom_s hpost).elim

private theorem call_frame_inv_lscl {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T) ∗ ⌜LibsignalCodeLoaded pl s.mem⌝)
    (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  refine call_inv_lscl (x := x) (F := F) hcall hcl hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, sepConj_left_comm (⌜φ⌝ ∗ T), satisfies_pure_sepConj]
  refine ⟨hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

theorem skipField_startGroup_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (hSlowCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 293)
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A)))
    (hSliceCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 76)
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32)
    (hrec : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A d (fun _ => True)))) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A (d + 1) (fun x => x.wt = .startGroup))) := by
  unfold skipFieldSpecAtX
  simp only [sliceCursorAt, stackAt_skipFieldX _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_lscl x s0 hcl0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  obtain ⟨htag_zext1, htag_zext2⟩ := bv32_zeroExtend_ofNat h_5
  obtain ⟨hd_zext1, hd_zext2⟩ := bv32_zeroExtend_ofNat (by omega : d < 2 ^ 32)
  obtain ⟨hd_sub1, hd_sub2⟩ := bv32_sub_one_zeroExtend hdepth
  rw [skipField_succ_startGroup]
  generalize hres : skipGroup (2 * bs.length + 1) (d + 1) tag bs = res
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (192)) hcl0
  wp_steps
  wp_reach
  intro hcl_init
  apply SepWPp.weaken_pre (P' := skipGroupLoopPreX A s0 d bufRef slot ptr bs bs)
    (Entails.of_eq (by dsimp only [skipGroupLoopPreX]; simp only [sliceCursorAfter, Nat.sub_self,
      BitVec.add_zero]; ac_rfl))
  refine (fun (Q_f Qp_f : State → SepProp → Prop)
      (hloop : ∀ n (cur : List (BitVec 8)) (s : State),
        cur.length ≤ n →
        cur.length ≤ bs.length →
        IsDropSuffix bs cur →
        skipGroup (2 * cur.length + 1) (d + 1) tag cur = res →
        s.pc = (blkPl_1).base + bv% (192) →
        s.status = .Running →
        s.sp = s0.sp - 96#64 →
        s.trace = s0.trace →
        s.readReg64 (Reg.gpr 19#5) = bufRef →
        s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
        s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
        HighCalleeSaved s0 s →
        LibsignalCodeLoaded lsmpl s.mem →
        SepWPp ((blkPC_1).rebase (blkPl_1).base H) (s0.readReg64 Reg.lr) s
          (skipGroupLoopPreX A s0 d bufRef slot ptr bs cur) Q_f Qp_f) =>
      hloop bs.length bs _ (Nat.le_refl _) (Nat.le_refl _) (by simp [IsDropSuffix]) hres
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm]⟩
        hcl_init)
    _ _ ?_
  intro n
  induction n with
  | zero =>
    intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hcl_s
    obtain ⟨hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
    cases cur with
    | nil =>
      have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) (cur := []) rfl
      rw [hnone] at hres_cur
      subst hres_cur
      apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl_s
      conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hcur_le hcur_suf,
        sliceCursorAt, pointsToBytes_nil, sepConj_emp,
        memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
      simp only [List.length_nil, sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - 0)) 0#64) (by sep_focus)
      conv => arg 4; rw [Nat.sub_zero, List.take_length, skipBelowX_err s0.sp (d + 1) hdepth, ← hsp_s]
      wp_reach
      intro hcl_err
      refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000001#64))
        (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl_err
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
        (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
        (by simp only [arm64_norm])
        (by simp only [arm64_norm]; rfl)
        (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000001#64)
        (by sep_focus)
        (fun _ _ _ _ hex => allowPanic_not_exited hex)
        (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
      intro sm hpcm hrunm hspm hcsm _
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, hsp_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
      apply SepWPp.of_sepWP_ret
      simp only [arm64_norm, htr_s, hsp_s]
      apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps
      wp_done
    | cons b0 bs1 =>
      simp only [List.length_cons] at hcur_n
      omega
  | succ n ih =>
    intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hcl_s
    cases cur with
    | nil =>
      exact ih [] s (by simp) hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hcl_s
    | cons b0 bs1 =>
      obtain ⟨hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
      have hcur_lt : (b0 :: bs1).length < 2 ^ 63 := by omega
      have hcbz_len := cbz_len_cons_false hcur_lt
      let curPtr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - (b0 :: bs1).length)
      refine (fun (Q_f Qp_f : State → SepProp → Prop)
          (hafter : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
            decodeVarint (b0 :: bs1) = some (key, rest) →
            s1.pc = (blkPl_1).base + bv% (296) →
            s1.status = .Running →
            s1.sp = s0.sp - 96#64 →
            s1.trace = s0.trace →
            s1.readReg64 (Reg.gpr 0#5) = key →
            s1.readReg64 (Reg.gpr 19#5) = bufRef →
            s1.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
            s1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
            HighCalleeSaved s0 s1 →
            LibsignalCodeLoaded lsmpl s1.mem →
            SepWPp ((blkPC_1).rebase (blkPl_1).base H) (s0.readReg64 Reg.lr) s1
              (skipGroupLoopPreX A s0 d bufRef slot ptr bs rest) Q_f Qp_f)
          (hbody : (∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
            decodeVarint (b0 :: bs1) = some (key, rest) →
            s1.pc = (blkPl_1).base + bv% (296) →
            s1.status = .Running →
            s1.sp = s0.sp - 96#64 →
            s1.trace = s0.trace →
            s1.readReg64 (Reg.gpr 0#5) = key →
            s1.readReg64 (Reg.gpr 19#5) = bufRef →
            s1.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
            s1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
            HighCalleeSaved s0 s1 →
            LibsignalCodeLoaded lsmpl s1.mem →
            SepWPp ((blkPC_1).rebase (blkPl_1).base H) (s0.readReg64 Reg.lr) s1
              (skipGroupLoopPreX A s0 d bufRef slot ptr bs rest) Q_f Qp_f) →
            SepWPp ((blkPC_1).rebase (blkPl_1).base H) (s0.readReg64 Reg.lr) s
              (skipGroupLoopPreX A s0 d bufRef slot ptr bs (b0 :: bs1)) Q_f Qp_f) =>
          hbody hafter)
        _ _ ?_ ?_
      · intro key rest s1 hd hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hcs1 hcl1
        obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
        have hrest_lt_cur : rest.length < (b0 :: bs1).length := decodeVarint_length hd
        have hrest_le : rest.length ≤ bs.length := by omega
        have hrest_lt : rest.length < 2 ^ 63 := by omega
        have hrest_suf : IsDropSuffix bs rest :=
          suffix_trans hcur_le hcur_suf (Nat.le_of_lt hrest_lt_cur) (decodeVarint_suffix hd)
        by_cases hk_ge : 2 ^ 32 ≤ key.toNat
        · have hnone := skipGroup_of_key_ge (d := d) (tag := tag) hd hk_ge
          rw [hnone] at hres_cur
          subst hres_cur
          have hshr := key_shr32_of_ge hk_ge
          apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl1
          conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
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
          conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hsp1]
          wp_reach
          intro hcl_err
          refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000004#64))
            (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl_err
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
            (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000004#64)
            (by sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
          intro sm hpcm hrunm hspm hcsm _
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm, hsp1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          apply SepWPp.of_sepWP_ret
          simp only [arm64_norm, htr1, hsp1]
          apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
          wp_steps
          wp_done
        · have hshr := key_shr32_of_lt hk_ge
          cases hwt : WireType.ofNat? (key.toNat % 8) with
          | none =>
            have hnone := skipGroup_of_wt_none (d := d) (tag := tag) hd hk_ge hwt
            rw [hnone] at hres_cur
            subst hres_cur
            obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
            apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl1
            conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
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
            conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hsp1]
            wp_reach
            intro hcl_err
            refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000003#64))
              (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl_err
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
              (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [arm64_norm]; rfl)
              (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000003#64)
              (by sep_focus)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
            intro sm hpcm hrunm hspm hcsm _
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm, hsp1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            apply SepWPp.of_sepWP_ret
            simp only [arm64_norm, htr1, hsp1]
            apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
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
              apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl1
              conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
                sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_err0
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
              conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hsp1]
              wp_reach
              intro hcl_err
              refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000005#64))
                (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl_err
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
                (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [arm64_norm]; rfl)
                (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000005#64)
                (by sep_focus)
                (fun _ _ _ _ hex => allowPanic_not_exited hex)
                (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
              intro sm hpcm hrunm hspm hcsm _
              simp only [CalleeSavedPreserved] at hcsm
              obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
              simp (config := { decide := true }) only [arm64_norm, hsp1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
              apply SepWPp.of_sepWP_ret
              simp only [arm64_norm, htr1, hsp1]
              apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
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
                  simp only [skipGroupLoopPreX, sliceCursorAfter]
                  wp_steps
                  wp_done
                · simp only [hitag_eq, ↓reduceIte] at hres_cur
                  subst hres_cur
                  obtain ⟨hne_bv1, hne_bv2⟩ := itag_beq_tag_false hitag_eq hitag_lt h_5
                  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl1
                  conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
                    sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
                  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
                  apply SepWP.exists_elim; intro v_err0
                  wp_steps
                  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
                  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                  conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hsp1]
                  wp_reach
                  intro hcl_err
                  refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000009#64))
                    (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl_err
                    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
                    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
                    (by simp only [arm64_norm])
                    (by simp only [arm64_norm]; rfl)
                    (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000009#64)
                    (by sep_focus)
                    (fun _ _ _ _ hex => allowPanic_not_exited hex)
                    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
                  intro sm hpcm hrunm hspm hcsm _
                  simp only [CalleeSavedPreserved] at hcsm
                  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
                  simp (config := { decide := true }) only [arm64_norm, hsp1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
                  apply SepWPp.of_sepWP_ret
                  simp only [arm64_norm, htr1, hsp1]
                  apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
                  wp_steps
                  wp_done
              · have hne_eg := skipGroup_of_ne_endGroup (d := d) (tag := tag) hd hk_ge hwt hitag0 hiwt_eg
                rw [hne_eg] at hres_cur
                have hiwt_ne4 := iwt_beq_4_false hiwt_eg
                obtain ⟨hiwt_w0_1, hiwt_w0_2⟩ := iwt_w0_setWidth8 iwt
                have hd_lt : d < 2 ^ 32 := by omega
                apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base) hcl1
                conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
                  show skipBelowX s0.sp (d + 1) = stackAt s1.sp (skipFieldStackX d) from by
                    rw [hsp1]]
                simp only [sepConj_assoc]
                wp_steps
                wp_reach
                intro hcl_rec
                refine call_frame_inv_lscl
                  (x := ⟨iwt, key.toNat / 8, d, bufRef, slot,
                    ptr + BitVec.ofNat 64 (bs.length - rest.length), rest⟩)
                  (ret_pc := (blkPl_1).base + bv% (348)) hrec hcl_rec
                  (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
                  (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
                  (by simp only [arm64_norm])
                  (by simp only [arm64_norm]; rfl)
                  ?_
                  (by sep_focus)
                  (fun _ _ _ _ hex => allowPanic_not_exited hex)
                  (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
                · simp only [arm64_norm, hiwt_w0_2, sf_truncate32_ofNat64]
                  exact ⟨hitag_lt, hd_lt, hrest_lt⟩
                intro sm hpcm hrunm hspm hcsm hclm
                simp only [CalleeSavedPreserved] at hcsm
                obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
                simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
                cases hs : skipField (2 * rest.length + 2) d (key.toNat / 8) iwt rest with
                | none =>
                  rw [hs] at hres_cur
                  dsimp only at hres_cur
                  subst hres_cur
                  apply SepWPp.of_sepWP_ret
                  simp only [hs, sepConj_assoc, arm64_norm, hsp1]
                  apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
                  have hcbz_sm0 : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
                  conv => arg 4; rw [show stackAt (s0.sp - 96#64) (skipFieldStackX d) = skipBelowX s0.sp (d + 1) from rfl]
                  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                  wp_steps
                  wp_done
                | some rest' =>
                  rw [hs] at hres_cur
                  dsimp only at hres_cur
                  have hrest'_le_rest : rest'.length ≤ rest.length :=
                    (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hs
                  have hrest'_le_n : rest'.length ≤ n := by
                    simp only [List.length_cons] at hcur_n hrest_lt_cur
                    omega
                  have hrest'_le_bs : rest'.length ≤ bs.length := by omega
                  have hrest'_suf : IsDropSuffix bs rest' :=
                    suffix_trans hrest_le hrest_suf hrest'_le_rest
                      ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hs)
                  apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (192)) hclm
                  conv => arg 4; simp only [skipFieldSpecAtX, hs, sepConj_assoc, arm64_norm, hsp1]
                  apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
                  conv => arg 4; rw [show stackAt (s0.sp - 96#64) (skipFieldStackX d) = skipBelowX s0.sp (d + 1) from rfl]
                  apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le_rest) (by sep_focus)
                  wp_steps
                  wp_reach
                  intro hcl_next
                  apply SepWPp.weaken_pre (P' := skipGroupLoopPreX A s0 d bufRef slot ptr bs rest')
                    (Entails.of_eq (by dsimp only [skipGroupLoopPreX]; ac_rfl))
                  refine ih rest' _ hrest'_le_n hrest'_le_bs hrest'_suf hres_cur
                    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcl_next
                  · simp only [arm64_norm]
                  · simp only [arm64_norm, hrunm]
                  · simp only [arm64_norm, hspm]
                  · simp only [arm64_norm, htrm, htr1]
                  · simp only [arm64_norm, hx19]
                  · simp only [arm64_norm, hx20]
                  · simp only [arm64_norm, hx21]
                  · simp only [arm64_norm, hx23]
                  · simp only [arm64_norm, hx24]
                  · simp only [arm64_norm, hx25]
                  · simp only [arm64_norm, hx26]
                  · simp only [arm64_norm, hx27]
                  · simp only [arm64_norm, hx28]
                  · simp only [arm64_norm, hvregs]
      · intro hafter
        by_cases hb0 : b0 ≤ 0x7f#8
        · have hbit0 := signExtend64_getLsbD_63_of_le hb0
          have hd := decodeVarint_1 bs1 hb0
          have hbs1_le : bs1.length ≤ (b0 :: bs1).length := by simp
          apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (296)) hcl_s
          conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hcur_le hcur_suf,
            sliceCursorAt, pointsToBytes_cons]
          wp_steps
          conv => arg 4; rw [len_cons_sub_one b0 bs1, ← pointsToBytes_cons]
          have hcur_after :
              (slot ↦₆₄ (curPtr + 1#64)) ∗
                ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
                (curPtr ↦ₛ (b0 :: bs1)) ⊢
                sliceCursorAfter slot curPtr (b0 :: bs1) bs1 := by
            simp only [sliceCursorAfter, List.length_cons, Nat.add_sub_cancel_left]
            exact Entails.refl _
          apply SepWP.fold hcur_after (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hbs1_le) (by sep_focus)
          wp_reach
          intro hcl1
          apply SepWPp.weaken_pre (P' := skipGroupLoopPreX A s0 d bufRef slot ptr bs bs1)
            (Entails.of_eq (by dsimp only [skipGroupLoopPreX]; ac_rfl))
          refine hafter ((b0 &&& 0x7f#8).zeroExtend 64) bs1 _ hd
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcl1
          · simp only [arm64_norm]
          · simp only [arm64_norm, hrun_s]
          · simp only [arm64_norm, hsp_s]
          · simp only [arm64_norm, htr_s]
          · simp only [arm64_norm, signExtend64_eq_and_0x7f hb0]
          · simp only [arm64_norm, hx19_s]
          · simp only [arm64_norm, hx20_s]
          · simp only [arm64_norm, hx21_s]
          · simp only [arm64_norm, hx23_s]
          · simp only [arm64_norm, hx24_s]
          · simp only [arm64_norm, hx25_s]
          · simp only [arm64_norm, hx26_s]
          · simp only [arm64_norm, hx27_s]
          · simp only [arm64_norm, hx28_s]
          · simp only [arm64_norm, hvregs_s]
        · have hbit0 := signExtend64_getLsbD_63_of_gt hb0
          have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          by_cases h11 : 11 ≤ (b0 :: bs1).length
          · have hhi := ult_10_of_ge_11 h11 hcur_lt
            have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
            apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl_s
            conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hcur_le hcur_suf,
              sliceCursorAt, pointsToBytes_cons, memRegion_48_skipSlice s0.sp,
              skipBelowX_leaf s0.sp (d + 1) hdepth]
            wp_steps
            wp_reach
            intro hcl_sl
            refine call_frame_inv_lscl (x := ⟨s0.sp - 96#64, curPtr, b0 :: bs1⟩)
              (ret_pc := (blkPl_1).base + bv% (256)) hSliceCall hcl_sl
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
              (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [arm64_norm, hsp_s, curPtr]; rfl)
              (⟨rfl, rfl, hlen_toNat, hcur_lt, hpre_slice⟩ :
                s0.sp - 96#64 = s0.sp - 96#64 ∧ curPtr = curPtr ∧
                  (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                  (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
              (by sep_focus)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
            intro sm hpcm hrunm hspm hcsm hclm
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            cases hd : decodeVarint (b0 :: bs1) with
            | none =>
              have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
              rw [hnone] at hres_cur
              subst hres_cur
              apply SepWPp.of_sepWP_ret
              simp only [hd, varintSliceResultAt, sepExists_sepConj_left, arm64_norm, htr_s, hsp_s]
              apply SepWP.exists_elim; intro e_err
              apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot curPtr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
              apply SepWP.fold (skipSliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
              wp_done
            | some p =>
              rcases p with ⟨key, rest⟩
              have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
              have hcc := len_ult_consumed_false (rest := rest) hcur_lt
              have hsub_len := bv_len_sub_consumed hd
              apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (296)) hclm
              conv => arg 4; simp only [hd, varintSliceResultAt, sepConj_assoc, arm64_norm, hsp_s]
              apply SepWP.pure_elim; intro htrm
              apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
              apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 key (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
              have hcur_after :
                  (slot ↦₆₄ (curPtr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) ∗
                    ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
                    (curPtr ↦ₛ (b0 :: bs1)) ⊢
                    sliceCursorAfter slot curPtr (b0 :: bs1) rest :=
                Entails.refl _
              apply SepWP.fold hcur_after (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le) (by sep_focus)
              wp_reach
              intro hcl1
              apply SepWPp.weaken_pre (P' := skipGroupLoopPreX A s0 d bufRef slot ptr bs rest)
                (Entails.of_eq (by dsimp only [skipGroupLoopPreX]; ac_rfl))
              refine hafter key rest _ hd
                ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcl1
              · simp only [arm64_norm]
              · simp only [arm64_norm, hrunm]
              · simp only [arm64_norm, hspm]
              · simp only [arm64_norm, htrm, htr_s]
              · simp only [arm64_norm]
              · simp only [arm64_norm, hx19]
              · simp only [arm64_norm, hx20]
              · simp only [arm64_norm, hx21]
              · simp only [arm64_norm, hx23]
              · simp only [arm64_norm, hx24]
              · simp only [arm64_norm, hx25]
              · simp only [arm64_norm, hx26]
              · simp only [arm64_norm, hx27]
              · simp only [arm64_norm, hx28]
              · simp only [arm64_norm, hvregs]
          · have hhi := ult_10_of_lt_11 h11 hcur_lt
            have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
            apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (244)) hcl_s
            conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hcur_le hcur_suf,
              sliceCursorAt, pointsToBytes_cons]
            wp_steps
            conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last curPtr (b0 :: bs1) hne_cons hcur_lt]
            wp_steps
            conv => arg 4; rw [← pointsToBytes_split_last curPtr (b0 :: bs1) hne_cons hcur_lt]
            wp_reach
            intro hcl_244
            by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
            · have hbit_last := getLsbD_7_of_le hlast
              have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
              apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl_244
              conv => arg 4; rw [pointsToBytes_cons, memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
              wp_steps
              wp_reach
              intro hcl_sl
              refine call_frame_inv_lscl (x := ⟨s0.sp - 96#64, curPtr, b0 :: bs1⟩)
                (ret_pc := (blkPl_1).base + bv% (256)) hSliceCall hcl_sl
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
                (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [arm64_norm, hsp_s, curPtr]; rfl)
                (⟨rfl, rfl, hlen_toNat, hcur_lt, hpre_slice⟩ :
                  s0.sp - 96#64 = s0.sp - 96#64 ∧ curPtr = curPtr ∧
                    (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                    (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
                (by sep_focus)
                (fun _ _ _ _ hex => allowPanic_not_exited hex)
                (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
              intro sm hpcm hrunm hspm hcsm hclm
              simp only [CalleeSavedPreserved] at hcsm
              obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
              simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
              cases hd : decodeVarint (b0 :: bs1) with
              | none =>
                have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
                rw [hnone] at hres_cur
                subst hres_cur
                apply SepWPp.of_sepWP_ret
                simp only [hd, varintSliceResultAt, sepExists_sepConj_left, arm64_norm, htr_s, hsp_s]
                apply SepWP.exists_elim; intro e_err
                apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
                wp_steps
                apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
                apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot curPtr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
                apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
                apply SepWP.fold (skipSliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
                wp_done
              | some p =>
                rcases p with ⟨key, rest⟩
                have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
                have hcc := len_ult_consumed_false (rest := rest) hcur_lt
                have hsub_len := bv_len_sub_consumed hd
                apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (296)) hclm
                conv => arg 4; simp only [hd, varintSliceResultAt, sepConj_assoc, arm64_norm, hsp_s]
                apply SepWP.pure_elim; intro htrm
                apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
                wp_steps
                apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
                apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 key (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
                have hcur_after :
                    (slot ↦₆₄ (curPtr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) ∗
                      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
                      (curPtr ↦ₛ (b0 :: bs1)) ⊢
                      sliceCursorAfter slot curPtr (b0 :: bs1) rest :=
                  Entails.refl _
                apply SepWP.fold hcur_after (by sep_focus)
                apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le) (by sep_focus)
                wp_reach
                intro hcl1
                apply SepWPp.weaken_pre (P' := skipGroupLoopPreX A s0 d bufRef slot ptr bs rest)
                  (Entails.of_eq (by dsimp only [skipGroupLoopPreX]; ac_rfl))
                refine hafter key rest _ hd
                  ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcl1
                · simp only [arm64_norm]
                · simp only [arm64_norm, hrunm]
                · simp only [arm64_norm, hspm]
                · simp only [arm64_norm, htrm, htr_s]
                · simp only [arm64_norm]
                · simp only [arm64_norm, hx19]
                · simp only [arm64_norm, hx20]
                · simp only [arm64_norm, hx21]
                · simp only [arm64_norm, hx23]
                · simp only [arm64_norm, hx24]
                · simp only [arm64_norm, hx25]
                · simp only [arm64_norm, hx26]
                · simp only [arm64_norm, hx27]
                · simp only [arm64_norm, hx28]
                · simp only [arm64_norm, hvregs]
            · have hbit_last := getLsbD_7_of_gt hlast
              apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 293) hcl_244
              wp_steps
              conv => arg 4; rw [skipBelowX_slow s0.sp (d + 1) hdepth]
              simp only [sepConj_assoc]
              wp_reach
              intro hcl_slw
              refine call_frame_inv_lscl (x := ⟨bufRef, slot, curPtr, b0 :: bs1⟩)
                (ret_pc := (blkPl_1).base + bv% (364)) hSlowCall hcl_slw
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
                (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [arm64_norm, hsp_s]; rfl)
                (⟨rfl, hcur_lt⟩ : bufRef = bufRef ∧ (b0 :: bs1).length < 2 ^ 63)
                (by simp only [sliceCursorAt]; sep_focus)
                (fun _ _ _ _ hex => allowPanic_not_exited hex)
                (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
              intro sm hpcm hrunm hspm hcsm hclm
              simp only [CalleeSavedPreserved] at hcsm
              obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
              simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
              cases hd : decodeVarint (b0 :: bs1) with
              | none =>
                have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
                rw [hnone] at hres_cur
                subst hres_cur
                apply SepWPp.of_sepWP_ret
                simp only [hd, sepConj_assoc, arm64_norm, htr_s, hsp_s]
                apply SepWP.pure_elim; intro hsm0
                apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
                apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
                apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
                wp_steps
                wp_done
              | some p =>
                rcases p with ⟨key, rest⟩
                have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
                apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (296)) hclm
                conv => arg 4; simp only [decodeVarintSlowSpecX, hd, sepConj_assoc, arm64_norm, hsp_s]
                apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
                apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
                apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le) (by sep_focus)
                wp_steps
                wp_reach
                intro hcl1
                apply SepWPp.weaken_pre (P' := skipGroupLoopPreX A s0 d bufRef slot ptr bs rest)
                  (Entails.of_eq (by dsimp only [skipGroupLoopPreX]; ac_rfl))
                refine hafter key rest _ hd
                  ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcl1
                · simp only [arm64_norm]
                · simp only [arm64_norm, hrunm]
                · simp only [arm64_norm, hspm]
                · simp only [arm64_norm, htrm, htr_s]
                · simp only [arm64_norm]
                · simp only [arm64_norm, hx19]
                · simp only [arm64_norm, hx20]
                · simp only [arm64_norm, hx21]
                · simp only [arm64_norm, hx23]
                · simp only [arm64_norm, hx24]
                · simp only [arm64_norm, hx25]
                · simp only [arm64_norm, hx26]
                · simp only [arm64_norm, hx27]
                · simp only [arm64_norm, hx28]
                · simp only [arm64_norm, hvregs]

end CryptoVerification.LibsignalTripleRatchet.Prost
