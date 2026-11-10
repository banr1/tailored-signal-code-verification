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
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


theorem skipField_depth_zero_ok_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName)
      ((skipFieldSpecAtX A 0 (fun _ => True)).inImage img) := by
  unfold skipFieldSpecAtX
  simp only [sliceCursorAt, stackAt_skipFieldX _ 0 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_inImage x s0 hfl0 hsym0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]")
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base H hfn (num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]")) 0 720
  dsimp only [skipFieldName] at *
  have _hpc_e : s0.pc = (CryptoVerification.libsignalSessionCode.rebase img.base H).fnAddr "prost::encoding::skip_field::<&mut &[u8]> [local#1]" := by
    first | exact hpc | exact hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear hpc; have hpc := _hpc_e; clear _hpc_e
  generalize_entry (CryptoVerification.libsignalSessionCode.rebase img.base H).fnAddr "prost::encoding::skip_field::<&mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have hcbz := cbz_depth_zero h_6
  rw [skipField_depth_zero]
  apply SepWPp.of_sepWP_inv hfl0 hsym0 (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
  conv => arg 4; rw [skipBelowX_err s0.sp 0 (by decide)]
  wp_reach
  intro hfl1 hsym1
  refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000002#64))
    (ret_pc := entry + bv% (652)) hFromCall hfl1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000002#64)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _ _
  apply SepWPp.of_sepWP_ret
  simp only [arm64_norm]
  apply SepWP.fold (skipBelowX_err_entails s0.sp 0 (by decide)) (by sep_focus)
  wp_steps
  wp_done

theorem skipField_endGroup_ok_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName)
      ((skipFieldSpecAtX A (d + 1) (fun x => x.wt = .endGroup)).inImage img) := by
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
  rw [skipField_succ_endGroup]
  apply SepWPp.of_sepWP_inv hfl0 hsym0 (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
  conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
  wp_reach
  intro hfl1 hsym1
  refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000009#64))
    (ret_pc := entry + bv% (652)) hFromCall hfl1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000009#64)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _ _
  apply SepWPp.of_sepWP_ret
  simp only [arm64_norm]
  apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
  wp_steps
  wp_done

theorem skipField_sixtyFourBit_ok_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName)
      ((skipFieldSpecAtX A (d + 1) (fun x => x.wt = .sixtyFourBit)).inImage img) := by
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
  rw [skipField_succ_sixtyFourBit]
  by_cases hlt : bs.length < 8
  · have hule := ule_len_of_lt (n := 8#64) hlt h
    simp only [skipBytes, hlt, ↓reduceIte]
    apply SepWPp.of_sepWP_inv hfl0 hsym0 (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hfl1 hsym1
    refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000007#64))
      (ret_pc := entry + bv% (652)) hFromCall hfl1 hsym1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _ _
    apply SepWPp.of_sepWP_ret
    simp only [arm64_norm]
    apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  · have hule := ule_len_of_ge (n := 8#64) hlt h
    have hsub := bv_len_sub_skip (n := 8#64) hlt
    have hadd := bv_ptr_add_skip_top (ptr := ptr) (n := 8#64) hlt
    simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem skipField_thirtyTwoBit_ok_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName)
      ((skipFieldSpecAtX A (d + 1) (fun x => x.wt = .thirtyTwoBit)).inImage img) := by
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
  rw [skipField_succ_thirtyTwoBit]
  by_cases hlt : bs.length < 4
  · have hule := ule_len_of_lt (n := 4#64) hlt h
    simp only [skipBytes, hlt, ↓reduceIte]
    apply SepWPp.of_sepWP_inv hfl0 hsym0 (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hfl1 hsym1
    refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000007#64))
      (ret_pc := entry + bv% (652)) hFromCall hfl1 hsym1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _ _
    apply SepWPp.of_sepWP_ret
    simp only [arm64_norm]
    apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  · have hule := ule_len_of_ge (n := 4#64) hlt h
    have hsub := bv_len_sub_skip (n := 4#64) hlt
    have hadd := bv_ptr_add_skip_top (ptr := ptr) (n := 4#64) hlt
    simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem skipField_varint_ok_x {img : Obj.Image} {A : RustAlloc}
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
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName)
      ((skipFieldSpecAtX A (d + 1) (fun x => x.wt = .varint)).inImage img) := by
  unfold skipFieldSpecAtX
  simp only [sliceCursorAt, stackAt_skipFieldX _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_inImage x s0 hfl0 hsym0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]")
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base H hfn (num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]")) 0 772
  dsimp only [skipFieldName] at *
  have _hpc_e : s0.pc = (CryptoVerification.libsignalSessionCode.rebase img.base H).fnAddr "prost::encoding::skip_field::<&mut &[u8]> [local#1]" := by
    first | exact hpc | exact hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear hpc; have hpc := _hpc_e; clear _hpc_e
  generalize_entry (CryptoVerification.libsignalSessionCode.rebase img.base H).fnAddr "prost::encoding::skip_field::<&mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_varint]
  cases bs with
  | nil =>
    simp only [decodeVarint, decodeVarintAux, Option.map]
    apply SepWPp.of_sepWP_inv hfl0 hsym0 (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr 0#64) (by sep_focus)
    conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hfl1 hsym1
    refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000001#64))
      (ret_pc := entry + bv% (652)) hFromCall hfl1 hsym1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000001#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _ _
    apply SepWPp.of_sepWP_ret
    simp only [arm64_norm]
    apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  | cons b0 bs1 =>
    have hcbz_len := cbz_len_cons_false h
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := getLsbD_7_of_le hb0
      rw [decodeVarint_1 bs1 hb0]
      dsimp only [Option.map]
      apply SepWPp.of_sepWP_ret
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      conv => arg 4; rw [len_cons_sub_one b0 bs1, ← pointsToBytes_cons]
      simp only [sliceCursorAfter, List.length_cons, Nat.add_sub_cancel_left]
      wp_done
    · have hbit0 := getLsbD_7_of_gt hb0
      have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      apply SepWPp.of_sepWP_inv hfl0 hsym0 (mid := entry + bv% (392))
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      wp_reach
      intro hfl1 hsym1
      by_cases h11 : 11 ≤ (b0 :: bs1).length
      · have hhi := ult_10_of_ge_11 h11 h
        have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
        apply SepWPp.of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
        conv => arg 4; rw [memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
        wp_steps
        wp_reach
        intro hfl2 hsym2
        refine SepWPp.call_frame_inv (x := ⟨s0.sp - 96#64, ptr, b0 :: bs1⟩)
          (ret_pc := entry + bv% (416)) hSliceCall hfl2 hsym2
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]; rfl)
          (⟨rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
            s0.sp - 96#64 = s0.sp - 96#64 ∧ ptr = ptr ∧
              (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
              (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
          (by sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex)
          (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
        intro sm hpcm hrunm hspm hcsm _ _
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
        apply SepWPp.of_sepWP_ret
        cases hd : decodeVarint (b0 :: bs1) with
        | none =>
          simp only [hd, Option.map, varintSliceResultAt,
            sepExists_sepConj_left, arm64_norm]
          apply SepWP.exists_elim; intro e_err
          apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
          apply SepWP.fold (skipSliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
          wp_done
        | some p =>
          rcases p with ⟨v, rest⟩
          have hcc := len_ult_consumed_false (rest := rest) h
          have hsub_len := bv_len_sub_consumed hd
          simp only [hd, Option.map, varintSliceResultAt, sliceCursorAfter, arm64_norm]
          apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
          wp_steps
          apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 v (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
          wp_done
      · have hhi := ult_10_of_lt_11 h11 h
        have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
        apply SepWPp.of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (404))
        conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
        wp_reach
        intro hfl2 hsym2
        by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
        · have hbit_last := getLsbD_7_of_le hlast
          have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
          apply SepWPp.of_sepWP_inv hfl2 hsym2 (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
          conv => arg 4; rw [pointsToBytes_cons, memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
          wp_steps
          wp_reach
          intro hfl3 hsym3
          refine SepWPp.call_frame_inv (x := ⟨s0.sp - 96#64, ptr, b0 :: bs1⟩)
            (ret_pc := entry + bv% (416)) hSliceCall hfl3 hsym3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
              s0.sp - 96#64 = s0.sp - 96#64 ∧ ptr = ptr ∧
                (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
            (by sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm _ _
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          apply SepWPp.of_sepWP_ret
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            simp only [hd, Option.map, varintSliceResultAt,
              sepExists_sepConj_left, arm64_norm]
            apply SepWP.exists_elim; intro e_err
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
            apply SepWP.fold (skipSliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
            wp_done
          | some p =>
            rcases p with ⟨v, rest⟩
            have hcc := len_ult_consumed_false (rest := rest) h
            have hsub_len := bv_len_sub_consumed hd
            simp only [hd, Option.map, varintSliceResultAt, sliceCursorAfter, arm64_norm]
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 v (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
            wp_done
        · have hbit_last := getLsbD_7_of_gt hlast
          apply SepWPp.of_sepWP_inv hfl2 hsym2 (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
          wp_steps
          conv => arg 4; rw [skipBelowX_slow s0.sp (d + 1) hdepth]
          wp_reach
          intro hfl3 hsym3
          refine SepWPp.call_frame_inv (x := ⟨bufRef, slot, ptr, b0 :: bs1⟩)
            (ret_pc := entry + bv% (732)) hSlowCall hfl3 hsym3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, h⟩ : bufRef = bufRef ∧ (b0 :: bs1).length < 2 ^ 63)
            (by simp only [sliceCursorAt]; sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm _ _
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          apply SepWPp.of_sepWP_ret
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            simp only [hd, Option.map, sepConj_assoc, arm64_norm]
            apply SepWP.pure_elim; intro hsm0
            apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            wp_done
          | some p =>
            rcases p with ⟨v, rest⟩
            simp only [hd, Option.map, sliceCursorAfter, sepConj_assoc, arm64_norm]
            apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
            apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            wp_done

theorem skipField_lengthDelimited_ok_x {img : Obj.Image} {A : RustAlloc}
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
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName)
      ((skipFieldSpecAtX A (d + 1) (fun x => x.wt = .lengthDelimited)).inImage img) := by
  unfold skipFieldSpecAtX
  simp only [sliceCursorAt, stackAt_skipFieldX _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_inImage x s0 hfl0 hsym0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]")
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base H hfn (num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]")) 0 800
  dsimp only [skipFieldName] at *
  have _hpc_e : s0.pc = (CryptoVerification.libsignalSessionCode.rebase img.base H).fnAddr "prost::encoding::skip_field::<&mut &[u8]> [local#1]" := by
    first | exact hpc | exact hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear hpc; have hpc := _hpc_e; clear _hpc_e
  generalize_entry (CryptoVerification.libsignalSessionCode.rebase img.base H).fnAddr "prost::encoding::skip_field::<&mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_lengthDelimited]
  cases bs with
  | nil =>
    simp only [decodeVarint, decodeVarintAux]
    apply SepWPp.of_sepWP_inv hfl0 hsym0 (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr 0#64) (by sep_focus)
    conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hfl1 hsym1
    refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000001#64))
      (ret_pc := entry + bv% (652)) hFromCall hfl1 hsym1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000001#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _ _
    apply SepWPp.of_sepWP_ret
    simp only [arm64_norm]
    apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  | cons b0 bs1 =>
    have hcbz_len := cbz_len_cons_false h
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := signExtend64_getLsbD_63_of_le hb0
      have hse := signExtend64_eq_and_0x7f hb0
      have hsub1 := len_cons_sub_one b0 bs1
      rw [decodeVarint_1 bs1 hb0]
      dsimp only
      by_cases hlt : bs1.length < ((b0 &&& 0x7f#8).zeroExtend 64).toNat
      · have hule := ule_len_of_lt hlt (by simp at h; omega)
        simp only [skipBytes, hlt, ↓reduceIte]
        apply SepWPp.of_sepWP_inv hfl0 hsym0 (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
        conv => arg 4; rw [pointsToBytes_cons, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply SepWP.exists_elim; intro v_err0
        wp_steps
        conv => arg 4; rw [← pointsToBytes_cons]
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + 1#64) (BitVec.ofNat 64 bs1.length)) (by sep_focus)
        conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
        wp_reach
        intro hfl1 hsym1
        refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000007#64))
          (ret_pc := entry + bv% (652)) hFromCall hfl1 hsym1
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]; rfl)
          (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
          (by sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex)
          (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
        intro sm hpcm hrunm hspm hcsm _ _
        apply SepWPp.of_sepWP_ret
        simp only [arm64_norm]
        apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
        wp_steps
        wp_done
      · have hule := ule_len_of_ge hlt (by simp at h; omega)
        have hsub := bv_len_sub_skip (rest := bs1) (n := (b0 &&& 0x7f#8).zeroExtend 64) hlt
        have hadd : ptr + 1#64 + (b0 &&& 0x7f#8).zeroExtend 64 =
            ptr + BitVec.ofNat 64 ((b0 :: bs1).length - (bs1.drop ((b0 &&& 0x7f#8).zeroExtend 64).toNat).length) := by
          have := bv_ptr_add_skip (bs := b0 :: bs1) (rest := bs1) (ptr := ptr)
            (n := (b0 &&& 0x7f#8).zeroExtend 64) (by simp) hlt
          simpa only [List.length_cons, Nat.add_sub_cancel_left] using this
        simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
        apply SepWPp.of_sepWP_ret
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_cons]
        wp_done
    · have hbit0 := signExtend64_getLsbD_63_of_gt hb0
      have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      apply SepWPp.of_sepWP_inv hfl0 hsym0 (mid := entry + bv% (472))
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      wp_reach
      intro hfl1 hsym1
      by_cases h11 : 11 ≤ (b0 :: bs1).length
      · have hhi := ult_10_of_ge_11 h11 h
        have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
        apply SepWPp.of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
        conv => arg 4; rw [memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
        wp_steps
        wp_reach
        intro hfl2 hsym2
        refine SepWPp.call_frame_inv (x := ⟨s0.sp - 96#64, ptr, b0 :: bs1⟩)
          (ret_pc := entry + bv% (496)) hSliceCall hfl2 hsym2
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]; rfl)
          (⟨rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
            s0.sp - 96#64 = s0.sp - 96#64 ∧ ptr = ptr ∧
              (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
              (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
          (by sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex)
          (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
        intro sm hpcm hrunm hspm hcsm hflm hsymm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
        cases hd : decodeVarint (b0 :: bs1) with
        | none =>
          apply SepWPp.of_sepWP_ret
          simp only [hd, varintSliceResultAt, sepExists_sepConj_left, arm64_norm]
          apply SepWP.exists_elim; intro e_err
          apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
          wp_steps
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
            simp only [hd, skipBytes, hlt, ↓reduceIte, varintSliceResultAt, sepConj_assoc, arm64_norm]
            apply SepWPp.of_sepWP_inv hflm hsymm (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
            apply SepWP.pure_elim; intro htrm
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (skipSliceTail_entails_memRegion40 s0.sp len (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
            conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hspm]
            wp_reach
            intro hfl3 hsym3
            refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000007#64))
              (ret_pc := entry + bv% (652)) hFromCall hfl3 hsym3
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
              (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [arm64_norm]; rfl)
              (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
              (by sep_focus)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm]) hpan) ?_
            intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _ _
            apply SepWPp.of_sepWP_ret
            simp only [arm64_norm, htrm, hspm]
            apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            wp_done
          · have hule := ule_len_of_ge hlt hrest_lt
            have hsub := bv_len_sub_skip hlt
            have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
            simp only [hd, skipBytes, hlt, ↓reduceIte, varintSliceResultAt, sliceCursorAfter, arm64_norm]
            apply SepWPp.of_sepWP_ret
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 len (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
            wp_done
      · have hhi := ult_10_of_lt_11 h11 h
        have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
        apply SepWPp.of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (484))
        conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
        wp_reach
        intro hfl2 hsym2
        by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
        · have hbit_last := getLsbD_7_of_le hlast
          have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
          apply SepWPp.of_sepWP_inv hfl2 hsym2 (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
          conv => arg 4; rw [pointsToBytes_cons, memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
          wp_steps
          wp_reach
          intro hfl3 hsym3
          refine SepWPp.call_frame_inv (x := ⟨s0.sp - 96#64, ptr, b0 :: bs1⟩)
            (ret_pc := entry + bv% (496)) hSliceCall hfl3 hsym3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
              s0.sp - 96#64 = s0.sp - 96#64 ∧ ptr = ptr ∧
                (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
            (by sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm hflm hsymm
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            apply SepWPp.of_sepWP_ret
            simp only [hd, varintSliceResultAt, sepExists_sepConj_left, arm64_norm]
            apply SepWP.exists_elim; intro e_err
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
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
              simp only [hd, skipBytes, hlt, ↓reduceIte, varintSliceResultAt, sepConj_assoc, arm64_norm]
              apply SepWPp.of_sepWP_inv hflm hsymm (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
              apply SepWP.pure_elim; intro htrm
              apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
              apply SepWP.fold (skipSliceTail_entails_memRegion40 s0.sp len (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
              conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hspm]
              wp_reach
              intro hfl4 hsym4
              refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000007#64))
                (ret_pc := entry + bv% (652)) hFromCall hfl4 hsym4
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [arm64_norm]; rfl)
                (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
                (by sep_focus)
                (fun _ _ _ _ hex => allowPanic_not_exited hex)
                (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm]) hpan) ?_
              intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _ _
              apply SepWPp.of_sepWP_ret
              simp only [arm64_norm, htrm, hspm]
              apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              wp_done
            · have hule := ule_len_of_ge hlt hrest_lt
              have hsub := bv_len_sub_skip hlt
              have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
              simp only [hd, skipBytes, hlt, ↓reduceIte, varintSliceResultAt, sliceCursorAfter, arm64_norm]
              apply SepWPp.of_sepWP_ret
              apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 len (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
              wp_done
        · have hbit_last := getLsbD_7_of_gt hlast
          apply SepWPp.of_sepWP_inv hfl2 hsym2 (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
          wp_steps
          conv => arg 4; rw [skipBelowX_slow s0.sp (d + 1) hdepth]
          wp_reach
          intro hfl3 hsym3
          refine SepWPp.call_frame_inv (x := ⟨bufRef, slot, ptr, b0 :: bs1⟩)
            (ret_pc := entry + bv% (772)) hSlowCall hfl3 hsym3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, h⟩ : bufRef = bufRef ∧ (b0 :: bs1).length < 2 ^ 63)
            (by simp only [sliceCursorAt]; sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm hflm hsymm
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            apply SepWPp.of_sepWP_ret
            simp only [hd, sepConj_assoc, arm64_norm]
            apply SepWP.pure_elim; intro hsm0
            apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            wp_done
          | some p =>
            rcases p with ⟨len, rest⟩
            have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
            have hrest_lt : rest.length < 2 ^ 63 := by omega
            by_cases hlt : rest.length < len.toNat
            · have hule := ule_len_of_lt hlt hrest_lt
              simp only [hd, skipBytes, hlt, ↓reduceIte, sliceCursorAfter, sepConj_assoc, arm64_norm]
              apply SepWPp.of_sepWP_inv hflm hsymm (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
              apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
              apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
              conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_err0
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
              conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hspm]
              wp_reach
              intro hfl4 hsym4
              refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000007#64))
                (ret_pc := entry + bv% (652)) hFromCall hfl4 hsym4
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [arm64_norm]; rfl)
                (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
                (by sep_focus)
                (fun _ _ _ _ hex => allowPanic_not_exited hex)
                (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm]) hpan) ?_
              intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _ _
              apply SepWPp.of_sepWP_ret
              simp only [arm64_norm, htrm, hspm]
              apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              wp_done
            · have hule := ule_len_of_ge hlt hrest_lt
              have hsub := bv_len_sub_skip hlt
              have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
              simp only [hd, skipBytes, hlt, ↓reduceIte, sliceCursorAfter, sepConj_assoc, arm64_norm]
              apply SepWPp.of_sepWP_ret
              apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
              apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              wp_done

/-! ## Relocatable per-block branch lemmas (block 1) -/

theorem call_inv_lscl {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
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

theorem call_frame_inv_lscl {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
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

theorem skipField_depth_zero_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX))) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A 0 (fun _ => True))) := by
  unfold skipFieldSpecAtX
  simp only [sliceCursorAt, stackAt_skipFieldX _ 0 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_lscl x s0 hcl0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  have hcbz := cbz_depth_zero h_6
  rw [skipField_depth_zero]
  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
  conv => arg 4; rw [skipBelowX_err s0.sp 0 (by decide)]
  wp_reach
  intro hcl1
  refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000002#64))
    (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000002#64)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _
  apply SepWPp.of_sepWP_ret
  simp only [arm64_norm]
  apply SepWP.fold (skipBelowX_err_entails s0.sp 0 (by decide)) (by sep_focus)
  wp_steps
  wp_done

theorem skipField_endGroup_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A (d + 1) (fun x => x.wt = .endGroup))) := by
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
  rw [skipField_succ_endGroup]
  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
  conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
  wp_reach
  intro hcl1
  refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000009#64))
    (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000009#64)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _
  apply SepWPp.of_sepWP_ret
  simp only [arm64_norm]
  apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
  wp_steps
  wp_done

theorem skipField_sixtyFourBit_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A (d + 1) (fun x => x.wt = .sixtyFourBit))) := by
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
  rw [skipField_succ_sixtyFourBit]
  by_cases hlt : bs.length < 8
  · have hule := ule_len_of_lt (n := 8#64) hlt h
    simp only [skipBytes, hlt, ↓reduceIte]
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hcl1
    refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000007#64))
      (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _
    apply SepWPp.of_sepWP_ret
    simp only [arm64_norm]
    apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  · have hule := ule_len_of_ge (n := 8#64) hlt h
    have hsub := bv_len_sub_skip (n := 8#64) hlt
    have hadd := bv_ptr_add_skip_top (ptr := ptr) (n := 8#64) hlt
    simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem skipField_thirtyTwoBit_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A (d + 1) (fun x => x.wt = .thirtyTwoBit))) := by
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
  rw [skipField_succ_thirtyTwoBit]
  by_cases hlt : bs.length < 4
  · have hule := ule_len_of_lt (n := 4#64) hlt h
    simp only [skipBytes, hlt, ↓reduceIte]
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hcl1
    refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000007#64))
      (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _
    apply SepWPp.of_sepWP_ret
    simp only [arm64_norm]
    apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  · have hule := ule_len_of_ge (n := 4#64) hlt h
    have hsub := bv_len_sub_skip (n := 4#64) hlt
    have hadd := bv_ptr_add_skip_top (ptr := ptr) (n := 4#64) hlt
    simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem skipField_varint_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
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
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A (d + 1) (fun x => x.wt = .varint))) := by
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
  rw [skipField_succ_varint]
  cases bs with
  | nil =>
    simp only [decodeVarint, decodeVarintAux, Option.map]
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr 0#64) (by sep_focus)
    conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hcl1
    refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000001#64))
      (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000001#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _
    apply SepWPp.of_sepWP_ret
    simp only [arm64_norm]
    apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  | cons b0 bs1 =>
    have hcbz_len := cbz_len_cons_false h
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := getLsbD_7_of_le hb0
      rw [decodeVarint_1 bs1 hb0]
      dsimp only [Option.map]
      apply SepWPp.of_sepWP_ret
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      conv => arg 4; rw [len_cons_sub_one b0 bs1, ← pointsToBytes_cons]
      simp only [sliceCursorAfter, List.length_cons, Nat.add_sub_cancel_left]
      wp_done
    · have hbit0 := getLsbD_7_of_gt hb0
      have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (392)) hcl0
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      wp_reach
      intro hcl1
      by_cases h11 : 11 ≤ (b0 :: bs1).length
      · have hhi := ult_10_of_ge_11 h11 h
        have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
        apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl1
        conv => arg 4; rw [memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
        wp_steps
        wp_reach
        intro hcl2
        refine call_frame_inv_lscl (x := ⟨s0.sp - 96#64, ptr, b0 :: bs1⟩)
          (ret_pc := (blkPl_1).base + bv% (416)) hSliceCall hcl2
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]; rfl)
          (⟨rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
            s0.sp - 96#64 = s0.sp - 96#64 ∧ ptr = ptr ∧
              (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
              (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
          (by sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex)
          (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
        intro sm hpcm hrunm hspm hcsm _
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
        apply SepWPp.of_sepWP_ret
        cases hd : decodeVarint (b0 :: bs1) with
        | none =>
          simp only [hd, Option.map, varintSliceResultAt,
            sepExists_sepConj_left, arm64_norm]
          apply SepWP.exists_elim; intro e_err
          apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
          apply SepWP.fold (skipSliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
          wp_done
        | some p =>
          rcases p with ⟨v, rest⟩
          have hcc := len_ult_consumed_false (rest := rest) h
          have hsub_len := bv_len_sub_consumed hd
          simp only [hd, Option.map, varintSliceResultAt, sliceCursorAfter, arm64_norm]
          apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
          wp_steps
          apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 v (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
          wp_done
      · have hhi := ult_10_of_lt_11 h11 h
        have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (404)) hcl1
        conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
        wp_reach
        intro hcl2
        by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
        · have hbit_last := getLsbD_7_of_le hlast
          have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
          apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl2
          conv => arg 4; rw [pointsToBytes_cons, memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
          wp_steps
          wp_reach
          intro hcl3
          refine call_frame_inv_lscl (x := ⟨s0.sp - 96#64, ptr, b0 :: bs1⟩)
            (ret_pc := (blkPl_1).base + bv% (416)) hSliceCall hcl3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
              s0.sp - 96#64 = s0.sp - 96#64 ∧ ptr = ptr ∧
                (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
            (by sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm _
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          apply SepWPp.of_sepWP_ret
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            simp only [hd, Option.map, varintSliceResultAt,
              sepExists_sepConj_left, arm64_norm]
            apply SepWP.exists_elim; intro e_err
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
            apply SepWP.fold (skipSliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
            wp_done
          | some p =>
            rcases p with ⟨v, rest⟩
            have hcc := len_ult_consumed_false (rest := rest) h
            have hsub_len := bv_len_sub_consumed hd
            simp only [hd, Option.map, varintSliceResultAt, sliceCursorAfter, arm64_norm]
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 v (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
            wp_done
        · have hbit_last := getLsbD_7_of_gt hlast
          apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 293) hcl2
          wp_steps
          conv => arg 4; rw [skipBelowX_slow s0.sp (d + 1) hdepth]
          wp_reach
          intro hcl3
          refine call_frame_inv_lscl (x := ⟨bufRef, slot, ptr, b0 :: bs1⟩)
            (ret_pc := (blkPl_1).base + bv% (732)) hSlowCall hcl3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, h⟩ : bufRef = bufRef ∧ (b0 :: bs1).length < 2 ^ 63)
            (by simp only [sliceCursorAt]; sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm _
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          apply SepWPp.of_sepWP_ret
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            simp only [hd, Option.map, sepConj_assoc, arm64_norm]
            apply SepWP.pure_elim; intro hsm0
            apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            wp_done
          | some p =>
            rcases p with ⟨v, rest⟩
            simp only [hd, Option.map, sliceCursorAfter, sepConj_assoc, arm64_norm]
            apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
            apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            wp_done

theorem skipField_lengthDelimited_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
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
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A (d + 1) (fun x => x.wt = .lengthDelimited))) := by
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
  rw [skipField_succ_lengthDelimited]
  cases bs with
  | nil =>
    simp only [decodeVarint, decodeVarintAux]
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr 0#64) (by sep_focus)
    conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hcl1
    refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000001#64))
      (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000001#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _
    apply SepWPp.of_sepWP_ret
    simp only [arm64_norm]
    apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  | cons b0 bs1 =>
    have hcbz_len := cbz_len_cons_false h
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := signExtend64_getLsbD_63_of_le hb0
      have hse := signExtend64_eq_and_0x7f hb0
      have hsub1 := len_cons_sub_one b0 bs1
      rw [decodeVarint_1 bs1 hb0]
      dsimp only
      by_cases hlt : bs1.length < ((b0 &&& 0x7f#8).zeroExtend 64).toNat
      · have hule := ule_len_of_lt hlt (by simp at h; omega)
        simp only [skipBytes, hlt, ↓reduceIte]
        apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
        conv => arg 4; rw [pointsToBytes_cons, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply SepWP.exists_elim; intro v_err0
        wp_steps
        conv => arg 4; rw [← pointsToBytes_cons]
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + 1#64) (BitVec.ofNat 64 bs1.length)) (by sep_focus)
        conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth]
        wp_reach
        intro hcl1
        refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000007#64))
          (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl1
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]; rfl)
          (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
          (by sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex)
          (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
        intro sm hpcm hrunm hspm hcsm _
        apply SepWPp.of_sepWP_ret
        simp only [arm64_norm]
        apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
        wp_steps
        wp_done
      · have hule := ule_len_of_ge hlt (by simp at h; omega)
        have hsub := bv_len_sub_skip (rest := bs1) (n := (b0 &&& 0x7f#8).zeroExtend 64) hlt
        have hadd : ptr + 1#64 + (b0 &&& 0x7f#8).zeroExtend 64 =
            ptr + BitVec.ofNat 64 ((b0 :: bs1).length - (bs1.drop ((b0 &&& 0x7f#8).zeroExtend 64).toNat).length) := by
          have := bv_ptr_add_skip (bs := b0 :: bs1) (rest := bs1) (ptr := ptr)
            (n := (b0 &&& 0x7f#8).zeroExtend 64) (by simp) hlt
          simpa only [List.length_cons, Nat.add_sub_cancel_left] using this
        simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
        apply SepWPp.of_sepWP_ret
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_cons]
        wp_done
    · have hbit0 := signExtend64_getLsbD_63_of_gt hb0
      have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (472)) hcl0
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      wp_reach
      intro hcl1
      by_cases h11 : 11 ≤ (b0 :: bs1).length
      · have hhi := ult_10_of_ge_11 h11 h
        have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
        apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl1
        conv => arg 4; rw [memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
        wp_steps
        wp_reach
        intro hcl2
        refine call_frame_inv_lscl (x := ⟨s0.sp - 96#64, ptr, b0 :: bs1⟩)
          (ret_pc := (blkPl_1).base + bv% (496)) hSliceCall hcl2
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]; rfl)
          (⟨rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
            s0.sp - 96#64 = s0.sp - 96#64 ∧ ptr = ptr ∧
              (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
              (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
          (by sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex)
          (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
        intro sm hpcm hrunm hspm hcsm hclm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
        cases hd : decodeVarint (b0 :: bs1) with
        | none =>
          apply SepWPp.of_sepWP_ret
          simp only [hd, varintSliceResultAt, sepExists_sepConj_left, arm64_norm]
          apply SepWP.exists_elim; intro e_err
          apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
          wp_steps
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
            simp only [hd, skipBytes, hlt, ↓reduceIte, varintSliceResultAt, sepConj_assoc, arm64_norm]
            apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hclm
            apply SepWP.pure_elim; intro htrm
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (skipSliceTail_entails_memRegion40 s0.sp len (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
            conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hspm]
            wp_reach
            intro hcl3
            refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000007#64))
              (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl3
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
              (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [arm64_norm]; rfl)
              (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
              (by sep_focus)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm]) hpan) ?_
            intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _
            apply SepWPp.of_sepWP_ret
            simp only [arm64_norm, htrm, hspm]
            apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            wp_done
          · have hule := ule_len_of_ge hlt hrest_lt
            have hsub := bv_len_sub_skip hlt
            have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
            simp only [hd, skipBytes, hlt, ↓reduceIte, varintSliceResultAt, sliceCursorAfter, arm64_norm]
            apply SepWPp.of_sepWP_ret
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 len (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
            wp_done
      · have hhi := ult_10_of_lt_11 h11 h
        have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (484)) hcl1
        conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
        wp_reach
        intro hcl2
        by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
        · have hbit_last := getLsbD_7_of_le hlast
          have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
          apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl2
          conv => arg 4; rw [pointsToBytes_cons, memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
          wp_steps
          wp_reach
          intro hcl3
          refine call_frame_inv_lscl (x := ⟨s0.sp - 96#64, ptr, b0 :: bs1⟩)
            (ret_pc := (blkPl_1).base + bv% (496)) hSliceCall hcl3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
              s0.sp - 96#64 = s0.sp - 96#64 ∧ ptr = ptr ∧
                (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1))
            (by sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm hclm
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            apply SepWPp.of_sepWP_ret
            simp only [hd, varintSliceResultAt, sepExists_sepConj_left, arm64_norm]
            apply SepWP.exists_elim; intro e_err
            apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
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
              simp only [hd, skipBytes, hlt, ↓reduceIte, varintSliceResultAt, sepConj_assoc, arm64_norm]
              apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hclm
              apply SepWP.pure_elim; intro htrm
              apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
              apply SepWP.fold (skipSliceTail_entails_memRegion40 s0.sp len (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
              conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hspm]
              wp_reach
              intro hcl4
              refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000007#64))
                (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl4
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [arm64_norm]; rfl)
                (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
                (by sep_focus)
                (fun _ _ _ _ hex => allowPanic_not_exited hex)
                (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm]) hpan) ?_
              intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _
              apply SepWPp.of_sepWP_ret
              simp only [arm64_norm, htrm, hspm]
              apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              wp_done
            · have hule := ule_len_of_ge hlt hrest_lt
              have hsub := bv_len_sub_skip hlt
              have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
              simp only [hd, skipBytes, hlt, ↓reduceIte, varintSliceResultAt, sliceCursorAfter, arm64_norm]
              apply SepWPp.of_sepWP_ret
              apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 len (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
              wp_done
        · have hbit_last := getLsbD_7_of_gt hlast
          apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 293) hcl2
          wp_steps
          conv => arg 4; rw [skipBelowX_slow s0.sp (d + 1) hdepth]
          wp_reach
          intro hcl3
          refine call_frame_inv_lscl (x := ⟨bufRef, slot, ptr, b0 :: bs1⟩)
            (ret_pc := (blkPl_1).base + bv% (772)) hSlowCall hcl3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, h⟩ : bufRef = bufRef ∧ (b0 :: bs1).length < 2 ^ 63)
            (by simp only [sliceCursorAt]; sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm hclm
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            apply SepWPp.of_sepWP_ret
            simp only [hd, sepConj_assoc, arm64_norm]
            apply SepWP.pure_elim; intro hsm0
            apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps
            wp_done
          | some p =>
            rcases p with ⟨len, rest⟩
            have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
            have hrest_lt : rest.length < 2 ^ 63 := by omega
            by_cases hlt : rest.length < len.toNat
            · have hule := ule_len_of_lt hlt hrest_lt
              simp only [hd, skipBytes, hlt, ↓reduceIte, sliceCursorAfter, sepConj_assoc, arm64_norm]
              apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hclm
              apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
              apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
              conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_err0
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
              conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hspm]
              wp_reach
              intro hcl4
              refine call_frame_inv_lscl (x := (s0.sp - 96#64, 0x8000000000000007#64))
                (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl4
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [arm64_norm]; rfl)
                (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
                (by sep_focus)
                (fun _ _ _ _ hex => allowPanic_not_exited hex)
                (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm]) hpan) ?_
              intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _
              apply SepWPp.of_sepWP_ret
              simp only [arm64_norm, htrm, hspm]
              apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              wp_done
            · have hule := ule_len_of_ge hlt hrest_lt
              have hsub := bv_len_sub_skip hlt
              have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
              simp only [hd, skipBytes, hlt, ↓reduceIte, sliceCursorAfter, sepConj_assoc, arm64_norm]
              apply SepWPp.of_sepWP_ret
              apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
              apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps
              wp_done

end CryptoVerification.LibsignalTripleRatchet.Prost
