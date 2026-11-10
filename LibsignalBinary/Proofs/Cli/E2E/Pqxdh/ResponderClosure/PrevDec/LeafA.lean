/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.HandshakeProstDecode
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Handshake `prost::encoding::skip_field::<&mut &[u8]> [local#6]` (Non-Group Cases 1–6)

Verifies the six non-group dispatch branches (`depth = 0`, `.endGroup`, `.sixtyFourBit`,
`.thirtyTwoBit`, `.varint`, and `.lengthDelimited`) of
`prost::encoding::skip_field::<&mut &[u8]> [local#6]`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

/-! ## Case 1: `depth = 0` (`RecursionLimitReached`) -/

theorem skipField6_depth_zero_ok {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name +
        bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name)
      ((skipField3SpecAt A 0 (fun _ => True)).inImage img) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ 0 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_inImage x s0 hfl0 hsym0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#5]")
  code_fetches CryptoVerification.libsignalSessionCode skipField6 img.base H hfn
    (num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]")) 420
  examples_generalize_entry
  examples_hide_fetches
  have hcbz := cbz_depth_zero h_6
  rw [skipField_depth_zero]
  apply SepWPp.of_sepWP_inv hfl0 hsym0
    (mid := entry + bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
                          ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
  conv => arg 4; rw [skipBelow3_err s0.sp 0 (by decide)]
  wp_reach
  intro hfl1 hsym1
  refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000002#64))
    (ret_pc := entry + bv% (204)) hFromCall hfl1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000002#64)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _ _
  simp only [CalleeSavedPreserved, arm64_norm] at hcsm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
  apply SepWPp.of_sepWP_ret
  simp only [arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 0 (by decide)) (by sep_focus)
  wp_steps
  wp_done

/-! ## Case 2: `depth = d + 1`, `wt = .endGroup` (`UnexpectedEndGroupTag`) -/

theorem skipField6_endGroup_ok {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name +
        bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name)
      ((skipField3SpecAt A (d + 1) (fun x => x.wt = .endGroup)).inImage img) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_inImage x s0 hfl0 hsym0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#5]")
  code_fetches CryptoVerification.libsignalSessionCode skipField6 img.base H hfn
    (num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]")) 420
  examples_generalize_entry
  examples_hide_fetches
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_endGroup]
  apply SepWPp.of_sepWP_inv hfl0 hsym0
    (mid := entry + bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
                          ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
  conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth]
  wp_reach
  intro hfl1 hsym1
  refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000009#64))
    (ret_pc := entry + bv% (204)) hFromCall hfl1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000009#64)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _ _
  simp only [CalleeSavedPreserved, arm64_norm] at hcsm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
  apply SepWPp.of_sepWP_ret
  simp only [arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
  wp_steps
  wp_done

/-! ## Case 3: `depth = d + 1`, `wt = .sixtyFourBit` (`skipBytes 8`) -/

theorem skipField6_sixtyFourBit_ok {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name +
        bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name)
      ((skipField3SpecAt A (d + 1) (fun x => x.wt = .sixtyFourBit)).inImage img) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_inImage x s0 hfl0 hsym0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#5]")
  code_fetches CryptoVerification.libsignalSessionCode skipField6 img.base H hfn
    (num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]")) 420
  examples_generalize_entry
  examples_hide_fetches
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_sixtyFourBit]
  by_cases hlt : bs.length < 8
  · have hule := ule_len_of_lt (n := 8#64) hlt h
    simp only [skipBytes, hlt, ↓reduceIte]
    apply SepWPp.of_sepWP_inv hfl0 hsym0
      (mid := entry + bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
                            ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hfl1 hsym1
    refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000007#64))
      (ret_pc := entry + bv% (204)) hFromCall hfl1 hsym1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _ _
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
    apply SepWPp.of_sepWP_ret
    simp only [arm64_norm]
    apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  · have hule := ule_len_of_ge (n := 8#64) hlt h
    have hsub := bv_len_sub_skip (n := 8#64) hlt
    have hadd := bv_ptr_add_skip_top (ptr := ptr) (n := 8#64) hlt
    simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

/-! ## Case 4: `depth = d + 1`, `wt = .thirtyTwoBit` (`skipBytes 4`) -/

theorem skipField6_thirtyTwoBit_ok {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name +
        bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name)
      ((skipField3SpecAt A (d + 1) (fun x => x.wt = .thirtyTwoBit)).inImage img) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_inImage x s0 hfl0 hsym0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#5]")
  code_fetches CryptoVerification.libsignalSessionCode skipField6 img.base H hfn
    (num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]")) 420
  examples_generalize_entry
  examples_hide_fetches
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_thirtyTwoBit]
  by_cases hlt : bs.length < 4
  · have hule := ule_len_of_lt (n := 4#64) hlt h
    simp only [skipBytes, hlt, ↓reduceIte]
    apply SepWPp.of_sepWP_inv hfl0 hsym0
      (mid := entry + bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
                            ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hfl1 hsym1
    refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000007#64))
      (ret_pc := entry + bv% (204)) hFromCall hfl1 hsym1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _ _
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
    apply SepWPp.of_sepWP_ret
    simp only [arm64_norm]
    apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  · have hule := ule_len_of_ge (n := 4#64) hlt h
    have hsub := bv_len_sub_skip (n := 4#64) hlt
    have hadd := bv_ptr_add_skip_top (ptr := ptr) (n := 4#64) hlt
    simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

/-! ## Case 5: `depth = d + 1`, `wt = .varint` -/

theorem skipField6_varint_ok {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name +
        bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
      ((decodeVarint2SpecX A).inImage img))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name)
      ((skipField3SpecAt A (d + 1) (fun x => x.wt = .varint)).inImage img) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_inImage x s0 hfl0 hsym0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#5]")
  code_fetches CryptoVerification.libsignalSessionCode skipField6 img.base H hfn
    (num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]")) 420
  examples_generalize_entry
  examples_hide_fetches
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_varint]
  apply SepWPp.of_sepWP_inv hfl0 hsym0
    (mid := entry + bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]" -
                          ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
  conv => arg 4; rw [skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps
  wp_reach
  intro hfl1 hsym1
  refine SepWPp.call_frame_inv (x := ⟨bufRef, slot, ptr, bs⟩)
    (ret_pc := entry + bv% (112)) hVarintCall hfl1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (⟨rfl, h⟩ : bufRef = bufRef ∧ bs.length < 2 ^ 63)
    (by simp only [sliceCursorAt]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _ _
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  apply SepWPp.of_sepWP_ret
  cases hd : decodeVarint bs with
  | none =>
    simp only [hd, Option.map, sepConj_assoc, arm64_norm]
    apply SepWP.pure_elim; intro hsm0
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  | some p =>
    rcases p with ⟨v, rest⟩
    simp only [hd, Option.map, sliceCursorAfter, sepConj_assoc, arm64_norm]
    apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done

/-! ## Case 6: `depth = d + 1`, `wt = .lengthDelimited` -/

theorem skipField6_lengthDelimited_ok {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name +
        bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name +
        bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
      ((decodeVarint2SpecX A).inImage img))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField6Name)
      ((skipField3SpecAt A (d + 1) (fun x => x.wt = .lengthDelimited)).inImage img) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_inImage x s0 hfl0 hsym0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#5]")
  code_fetches CryptoVerification.libsignalSessionCode skipField6 img.base H hfn
    (num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]")) 420
  examples_generalize_entry
  examples_hide_fetches
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_lengthDelimited]
  apply SepWPp.of_sepWP_inv hfl0 hsym0
    (mid := entry + bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]" -
                          ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
  conv => arg 4; rw [skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps
  wp_reach
  intro hfl1 hsym1
  refine SepWPp.call_frame_inv (x := ⟨bufRef, slot, ptr, bs⟩)
    (ret_pc := entry + bv% (160)) hVarintCall hfl1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (⟨rfl, h⟩ : bufRef = bufRef ∧ bs.length < 2 ^ 63)
    (by simp only [sliceCursorAt]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hflm hsymm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  cases hd : decodeVarint bs with
  | none =>
    apply SepWPp.of_sepWP_ret
    simp only [hd, sepConj_assoc, arm64_norm]
    apply SepWP.pure_elim; intro hsm0
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  | some p =>
    rcases p with ⟨len, rest⟩
    have hrest_le : rest.length ≤ bs.length := Nat.le_of_lt (decodeVarint_length hd)
    have hrest_lt : rest.length < 2 ^ 63 := by omega
    by_cases hlt : rest.length < len.toNat
    · have hule := ule_len_of_lt hlt hrest_lt
      simp only [hd, skipBytes, hlt, ↓reduceIte, sliceCursorAfter, sepConj_assoc, arm64_norm]
      apply SepWPp.of_sepWP_inv hflm hsymm
        (mid := entry + bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
                              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") % 2 ^ 64))
      apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
      conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
      wp_reach
      intro hfl2 hsym2
      refine SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000007#64))
        (ret_pc := entry + bv% (204)) hFromCall hfl2 hsym2
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
        (by simp only [arm64_norm])
        (by simp only [arm64_norm]; rfl)
        (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
        (by sep_focus)
        (fun _ _ _ _ hex => allowPanic_not_exited hex)
        (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm]) hpan) ?_
      intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _ _
      simp only [CalleeSavedPreserved] at hcsm2
      obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
      simp (config := { decide := true }) only [arm64_norm, hspm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      apply SepWPp.of_sepWP_ret
      simp only [arm64_norm, htrm, hspm]
      apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps
      wp_done
    · have hule := ule_len_of_ge hlt hrest_lt
      have hsub := bv_len_sub_skip hlt
      have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
      simp only [hd, skipBytes, hlt, ↓reduceIte, sliceCursorAfter, sepConj_assoc, arm64_norm]
      apply SepWPp.of_sepWP_ret
      apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps
      wp_done

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
