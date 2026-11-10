/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.SkipField7A
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.VarintDrop7
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.DecodeErrorFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# X-Form Crate-10 `skip_field::<&mut &[u8]> [local#7]` Group Loop and Top-Level Spec

Proves `skipField7_startGroup_ok` by length induction over `cur`, combines all `WireType` cases by
induction on `depth` (`skipField7_at_depth_ok`), and derives `skipField7_ok_of_alloc_x` against
`(PrevDec.skipField3Spec A).inImage img` under `AllocContractsX img A ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.SkipField7

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open scoped CryptoVerification.CodeLayout
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocFailedIn)
open CryptoVerification.LibsignalProtoCodec
  (WireType skipField skipGroup decodeVarint decodeVarint_length skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorFromName decodeErrorFromSpecWithStack
   AllocContractsX tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (decodeErrorHookStackX decodeErrorFromSpecWithStack_inImage_mono
   pointsTo64_pair_entails_memRegion16 sliceCursorAt sliceCursorAfter
   memRegion_48_split memRegion_48_split2 pointsTo64_memRegion32_entails_40
   allowPanic_frame' cbz_depth_succ w0_and_255_eq skipField_succ_startGroup
   IsDropSuffix decodeVarint_suffix suffix_trans skip_suffix
   sliceCursorAfter_eq_split sliceCursorAfter_join pointsToBytes_prefix_join
   skipGroup_of_decodeVarint_none skipGroup_of_key_ge skipGroup_of_wt_none
   skipGroup_of_tag_zero skipGroup_of_endGroup skipGroup_of_ne_endGroup
   sf_truncate32_ofNat64 bv32_zeroExtend_ofNat bv32_sub_one_zeroExtend
   key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some w1_tag_eq tag_cbz_false
   iwt_beq_4_false itag_beq_tag_false iwt_w0_setWidth8)
open CryptoVerification.SpqrV1.Varint (decodeVarint2SpecX)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
  (skipField3Stack skipField3Spec skipField3SpecAt stackAt_skipField3
   skipBelow3 skipLeafRest3 skipBelow3_leaf skipBelow3_leaf_entails skipBelow3_err skipBelow3_err_entails
   HighCalleeSaved3 skipGroupLoopPre3 subroutine_ok_skipField3_or subroutine_ok_skipField3_imp
   subroutine_ok_skipField3Spec_of_at_depth)
open CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers (decodeErrorFrom_ok_ext_x)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.SkipField7A
  (skipField7Name skipField7_depth_zero_ok skipField7_endGroup_ok skipField7_sixtyFourBit_ok
   skipField7_thirtyTwoBit_ok skipField7_varint_ok skipField7_lengthDelimited_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.VarintDrop7
  (decodeVarint6_ok_of_alloc_x)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

abbrev decodeVarint6Name : String :=
  CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name

/-! ## Case 7: `depth = d + 1`, `wt = .startGroup` -/

private abbrev skipGroupLoopPost7 (A : RustAlloc) (s0 : State) (d : Nat)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    (res : Option (List (BitVec 8))) (R : SepProp) (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R →
      sf.mem ⊨
        (∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ x_4, ∃∗ x_5,
          ⌜sf.trace = s0.trace⌝ ∗
            (bufRef ↦₆₄ slot) ∗
              A.pool ∗
                skipBelow3 s0.sp (d + 1) ∗
                  memRegion (s0.sp - 96#64) 48 ∗
                    ((s0.sp - 48#64) ↦₆₄ x_5) ∗
                      ((s0.sp - 40#64) ↦₆₄ x_4) ∗
                        ((s0.sp - 32#64) ↦₆₄ x_3) ∗
                          ((s0.sp - 24#64) ↦₆₄ x_2) ∗
                            ((s0.sp - 16#64) ↦₆₄ x_1) ∗
                              ((s0.sp - 8#64) ↦₆₄ x) ∗
                                match res with
                                | some rest =>
                                  ⌜sf.readReg64 Reg.x0 = 0#64⌝ ∗
                                    sliceCursorAfter slot ptr bs rest
                                | none =>
                                  ⌜sf.readReg64 Reg.x0 ≠ 0#64⌝ ∗
                                    decodeErrorAtStackLen A (sf.readReg64 Reg.x0) 0 ∗
                                      memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev skipGroupLoopPanic7 (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  sf.mem ⊨ P_f ∗ R → (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) ∧ sf.mem ⊨ anyHeap ∗ R

private abbrev SkipGroupLoopStmt7 (img : Obj.Image) (A : RustAlloc)
    (H : String → Option (State → State)) (s0 : State) (d tag : Nat)
    (bufRef slot ptr v_stk_2 : BitVec 64) (bs : List (BitVec 8))
    (res : Option (List (BitVec 8))) (R : SepProp) (n : Nat) : Prop :=
  ∀ (cur : List (BitVec 8)) (s : State),
    cur.length ≤ n →
    cur.length ≤ bs.length →
    IsDropSuffix bs cur →
    skipGroup (2 * cur.length + 1) (d + 1) tag cur = res →
    s.pc = (libsignalSessionCode.rebase img.base H).fnAddr skipField7Name + 232#64 →
    s.status = .Running →
    s.sp = s0.sp - 96#64 →
    s.trace = s0.trace →
    s.readReg64 (Reg.gpr 19#5) = bufRef →
    s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
    s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
    HighCalleeSaved3 s0 s →
    img.FrozenLoaded s →
    s.symtab = img.symtab →
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (skipGroupLoopPre3 A s0 d bufRef slot ptr v_stk_2 bs cur)
      (skipGroupLoopPost7 A s0 d bufRef slot ptr bs res R)
      (skipGroupLoopPanic7 s0 R)

set_option maxHeartbeats 400000 in
private theorem skipField7_startGroup_zero {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name +
        bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      ((decodeVarint2SpecX A).inImage img))
    (s0 : State) (hsp_align : s0.spAligned)
    (d tag : Nat) (hdepth : d + 1 < 2 ^ 32)
    (bufRef slot ptr v_stk_2 : BitVec 64)
    (bs : List (BitVec 8)) (_h : bs.length < 2 ^ 63)
    (res : Option (List (BitVec 8))) (R : SepProp) :
    SkipGroupLoopStmt7 img A H s0 d tag bufRef slot ptr v_stk_2 bs res R 0 := by
  intro cur s _hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hfl_s hsym_s
  dsimp only [Spec.inImage, decodeVarint2SpecX] at hVarintCall
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#6]")
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Varint.skipField3CliC img.base H hfn
    (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") 124 20
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Varint.skipField3CliC img.base H hfn
    (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") 192 228
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
  have hcur_lt : cur.length < 2 ^ 63 := by omega
  let curPtr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - cur.length)
  apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.of_sepWP_inv hfl_s hsym_s
    (mid := entry + bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" -
                          ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
  conv => arg 4; rw [skipGroupLoopPre3, sliceCursorAfter_eq_split hcur_le hcur_suf,
    skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps
  wp_reach
  intro hfl1 hsym1
  refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.call_frame_inv (x := ⟨bufRef, slot, curPtr, cur⟩)
    (ret_pc := entry + bv% (240)) hVarintCall hfl1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
    (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hsp_s]; rfl)
    (⟨rfl, hcur_lt⟩ : bufRef = bufRef ∧ cur.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _ _
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  cases hd : decodeVarint cur with
  | none =>
    have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
    rw [hnone] at hres_cur
    subst hres_cur
    apply SepWPp.of_sepWP_ret
    simp only [hd, sepConj_assoc, arm64_norm, htr_s, hsp_s]
    apply SepWP.pure_elim; intro hsm0
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_steps
    wp_done
  | some p =>
    have hlt_cur := decodeVarint_length hd
    omega

set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
private theorem skipField7_startGroup_succ_err {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name +
        bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name +
        bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      ((decodeVarint2SpecX A).inImage img))
    (s0 : State) (hsp_align : s0.spAligned)
    (d tag : Nat) (hdepth : d + 1 < 2 ^ 32)
    (bufRef slot ptr v_stk_2 : BitVec 64)
    (bs : List (BitVec 8)) (_h : bs.length < 2 ^ 63)
    (res : Option (List (BitVec 8))) (R : SepProp) (n : Nat)
    (cur : List (BitVec 8)) (s : State)
    (hcase : ∀ key rest, decodeVarint cur = some (key, rest) →
      2 ^ 32 ≤ key.toNat ∨ WireType.ofNat? (key.toNat % 8) = none ∨ key.toNat / 8 < 1)
    (_hcur_n : cur.length ≤ n + 1) (hcur_le : cur.length ≤ bs.length)
    (hcur_suf : IsDropSuffix bs cur)
    (hres_cur : skipGroup (2 * cur.length + 1) (d + 1) tag cur = res)
    (hpc_s : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr skipField7Name + 232#64)
    (hrun_s : s.status = .Running) (hsp_s : s.sp = s0.sp - 96#64)
    (htr_s : s.trace = s0.trace)
    (hx19_s : s.readReg64 (Reg.gpr 19#5) = bufRef)
    (hx20_s : s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d)
    (hx21_s : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag)
    (hcs_s : HighCalleeSaved3 s0 s) (hfl_s : img.FrozenLoaded s)
    (hsym_s : s.symtab = img.symtab) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (skipGroupLoopPre3 A s0 d bufRef slot ptr v_stk_2 bs cur)
      (skipGroupLoopPost7 A s0 d bufRef slot ptr bs res R)
      (skipGroupLoopPanic7 s0 R) := by
  dsimp only [Spec.inImage, decodeErrorFromSpecWithStack] at hFromCall
  dsimp only [Spec.inImage, decodeVarint2SpecX] at hVarintCall
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#6]")
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Varint.skipField3CliC img.base H hfn
    (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") 124 20
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Varint.skipField3CliC img.base H hfn
    (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") 192 184
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
  have hcur_lt : cur.length < 2 ^ 63 := by omega
  let curPtr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - cur.length)
  apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.of_sepWP_inv hfl_s hsym_s
    (mid := entry + bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" -
                          ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
  conv => arg 4; rw [skipGroupLoopPre3, sliceCursorAfter_eq_split hcur_le hcur_suf,
    skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps
  wp_reach
  intro hfl1 hsym1
  refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.call_frame_inv (x := ⟨bufRef, slot, curPtr, cur⟩)
    (ret_pc := entry + bv% (240)) hVarintCall hfl1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
    (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hsp_s]; rfl)
    (⟨rfl, hcur_lt⟩ : bufRef = bufRef ∧ cur.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hflm hsymm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  cases hd : decodeVarint cur with
  | none =>
    have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
    rw [hnone] at hres_cur
    subst hres_cur
    apply SepWPp.of_sepWP_ret
    simp only [hd, sepConj_assoc, arm64_norm, htr_s, hsp_s]
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
      apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.of_sepWP_inv hflm hsymm
        (mid := entry + bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
                              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm, hsp_s]
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
      intro hfl2 hsym2
      refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000004#64))
        (ret_pc := entry + bv% (204)) hFromCall hfl2 hsym2
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
        (by simp only [arm64_norm])
        (by simp only [arm64_norm]; rfl)
        (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000004#64)
        (by sep_focus)
        (fun _ _ _ _ hex => allowPanic_not_exited hex)
        (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr_s]) hpan) ?_
      intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _ _
      simp only [CalleeSavedPreserved] at hcsm2
      obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
      simp (config := { decide := true }) only [arm64_norm, hspm, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      apply SepWPp.of_sepWP_ret
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
        apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.of_sepWP_inv hflm hsymm
          (mid := entry + bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
                                ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
        conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm, hsp_s]
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
        intro hfl2 hsym2
        refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000003#64))
          (ret_pc := entry + bv% (204)) hFromCall hfl2 hsym2
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]; rfl)
          (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000003#64)
          (by sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex)
          (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr_s]) hpan) ?_
        intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _ _
        simp only [CalleeSavedPreserved] at hcsm2
        obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
        simp (config := { decide := true }) only [arm64_norm, hspm, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
        apply SepWPp.of_sepWP_ret
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
          apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.of_sepWP_inv hflm hsymm
            (mid := entry + bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
                                  ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
          conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm, hsp_s]
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
          intro hfl2 hsym2
          refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000005#64))
            (ret_pc := entry + bv% (204)) hFromCall hfl2 hsym2
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000005#64)
            (by sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr_s]) hpan) ?_
          intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _ _
          simp only [CalleeSavedPreserved] at hcsm2
          obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
          simp (config := { decide := true }) only [arm64_norm, hspm, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
          apply SepWPp.of_sepWP_ret
          simp only [arm64_norm, htrm, htr_s, hspm]
          apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
          wp_steps
          wp_done
        · rcases hcase key rest hd with h1 | h2 | h3
          · exact absurd h1 hk_ge
          · rw [hwt] at h2; cases h2
          · exact absurd h3 hitag0

set_option linter.unusedVariables false in
set_option maxHeartbeats 400000 in
private theorem skipField7_startGroup_succ_endGroup {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name +
        bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (s0 : State) (hsp_align : s0.spAligned)
    (d tag : Nat) (hdepth : d + 1 < 2 ^ 32) (h_5 : tag < 2 ^ 32)
    (bufRef slot ptr v_stk_2 : BitVec 64)
    (bs : List (BitVec 8))
    (res : Option (List (BitVec 8))) (R : SepProp)
    (cur : List (BitVec 8)) (s sm : State)
    (key : BitVec 64) (rest : List (BitVec 8))
    (hd : decodeVarint cur = some (key, rest))
    (hk_ge : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some .endGroup)
    (hitag0 : ¬ key.toNat / 8 < 1)
    (hcur_le : cur.length ≤ bs.length)
    (hcur_suf : IsDropSuffix bs cur)
    (hres_cur : skipGroup (2 * cur.length + 1) (d + 1) tag cur = res)
    (hsp_s : s.sp = s0.sp - 96#64) (htr_s : s.trace = s0.trace)
    (hx19_s : s.readReg64 (Reg.gpr 19#5) = bufRef)
    (hx20_s : s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d)
    (hx21_s : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag)
    (hcs_s : HighCalleeSaved3 s0 s)
    (hpcm : sm.pc = (libsignalSessionCode.rebase img.base H).fnAddr skipField7Name + 240#64)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s.sp)
    (hcsm : CalleeSavedPreserved s sm)
    (hflm : img.FrozenLoaded sm) (hsymm : sm.symtab = img.symtab) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) sm
      (((decodeVarint2SpecX A).post ⟨bufRef, slot, ptr + BitVec.ofNat 64 (bs.length - cur.length), cur⟩ s sm) ∗
        ptr ↦ₛ bs.take (bs.length - cur.length) ∗
        memRegion (s0.sp - 96#64) 48 ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 24#64) ↦₆₄ v_stk_2 ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
        skipLeafRest3 s0.sp (d + 1))
      (skipGroupLoopPost7 A s0 d bufRef slot ptr bs res R)
      (skipGroupLoopPanic7 s0 R) := by
  dsimp only [Spec.inImage, decodeErrorFromSpecWithStack] at hFromCall
  dsimp only [decodeVarint2SpecX]
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#6]")
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Varint.skipField3CliC img.base H hfn
    (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") 92 12
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Varint.skipField3CliC img.base H hfn
    (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") 192 32
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Varint.skipField3CliC img.base H hfn
    (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") 240 180
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
  have hrest_le : rest.length ≤ bs.length := by omega
  have hrest_suf : IsDropSuffix bs rest :=
    suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
  have hshr := key_shr32_of_lt hk_ge
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
  have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
  dsimp [WireType.toNat] at hand_wt hcc1_wt hcc2_wt
  have heg := skipGroup_of_endGroup (d := d) (tag := tag) hd hk_ge hwt hitag0
  rw [heg] at hres_cur
  by_cases hitag_eq : key.toNat / 8 = tag
  · simp only [hitag_eq, ↓reduceIte] at hres_cur
    subst hres_cur
    rw [hitag_eq] at hw1 hw1_2 hw1_zext1 hw1_zext2 hcbz_tag1 hcbz_tag2
    conv => arg 5; ext sf P_f; dsimp only [skipGroupLoopPost7, sliceCursorAfter]
    apply SepWPp.of_sepWP_ret
    simp only [hd, sepConj_assoc, arm64_norm, htr_s, hsp_s]
    apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join (slot := slot) hcur_le hcur_suf hrest_le_cur) (by sep_focus)
    conv => arg 4; simp only [sliceCursorAfter]
    wp_steps
    wp_done
  · simp only [hitag_eq, ↓reduceIte] at hres_cur
    subst hres_cur
    obtain ⟨hne_bv1, hne_bv2⟩ := itag_beq_tag_false hitag_eq hitag_lt h_5
    apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.of_sepWP_inv hflm hsymm
      (mid := entry + bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
                            ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
    conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm, hsp_s]
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
    intro hfl2 hsym2
    refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.call_frame_inv (x := (s0.sp - 96#64, 0x8000000000000009#64))
      (ret_pc := entry + bv% (204)) hFromCall hfl2 hsym2
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000009#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr_s]) hpan) ?_
    intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _ _
    simp only [CalleeSavedPreserved] at hcsm2
    obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
    simp (config := { decide := true }) only [arm64_norm, hspm, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
    apply SepWPp.of_sepWP_ret
    simp only [arm64_norm, htrm, htr_s, hspm]
    apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done

set_option linter.unusedVariables false in
set_option maxHeartbeats 400000 in
private theorem skipField7_startGroup_succ_ok {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name +
        bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name +
        bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      ((decodeVarint2SpecX A).inImage img))
    (s0 : State) (hsp_align : s0.spAligned)
    (d tag : Nat) (hdepth : d + 1 < 2 ^ 32) (h_5 : tag < 2 ^ 32)
    (hrec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name)
      ((skipField3SpecAt A d (fun _ => True)).inImage img))
    (bufRef slot ptr v_stk_2 : BitVec 64)
    (bs : List (BitVec 8)) (_h : bs.length < 2 ^ 63)
    (res : Option (List (BitVec 8))) (R : SepProp) (n : Nat)
    (ih : SkipGroupLoopStmt7 img A H s0 d tag bufRef slot ptr v_stk_2 bs res R n)
    (cur : List (BitVec 8)) (s : State)
    (hcase : ∃ key rest iwt, decodeVarint cur = some (key, rest) ∧
      ¬ 2 ^ 32 ≤ key.toNat ∧ WireType.ofNat? (key.toNat % 8) = some iwt ∧ ¬ key.toNat / 8 < 1)
    (_hcur_n : cur.length ≤ n + 1) (hcur_le : cur.length ≤ bs.length)
    (hcur_suf : IsDropSuffix bs cur)
    (hres_cur : skipGroup (2 * cur.length + 1) (d + 1) tag cur = res)
    (hpc_s : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr skipField7Name + 232#64)
    (hrun_s : s.status = .Running) (hsp_s : s.sp = s0.sp - 96#64)
    (htr_s : s.trace = s0.trace)
    (hx19_s : s.readReg64 (Reg.gpr 19#5) = bufRef)
    (hx20_s : s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d)
    (hx21_s : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag)
    (hcs_s : HighCalleeSaved3 s0 s) (hfl_s : img.FrozenLoaded s)
    (hsym_s : s.symtab = img.symtab) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (skipGroupLoopPre3 A s0 d bufRef slot ptr v_stk_2 bs cur)
      (skipGroupLoopPost7 A s0 d bufRef slot ptr bs res R)
      (skipGroupLoopPanic7 s0 R) := by
  dsimp only [Spec.inImage] at hVarintCall
  dsimp only [Spec.inImage, skipField3SpecAt] at hrec
  dsimp only [SkipGroupLoopStmt7] at ih
  have hEndGroup := skipField7_startGroup_succ_endGroup hFromCall s0 hsp_align d tag hdepth h_5
    bufRef slot ptr v_stk_2 bs res R cur s
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#6]")
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Varint.skipField3CliC img.base H hfn
    (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") 124 20
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Varint.skipField3CliC img.base H hfn
    (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") 232 84
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
  have hcur_lt : cur.length < 2 ^ 63 := by omega
  let curPtr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - cur.length)
  apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.of_sepWP_inv hfl_s hsym_s
    (mid := entry + bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" -
                          ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
  conv => arg 4; rw [skipGroupLoopPre3, sliceCursorAfter_eq_split hcur_le hcur_suf,
    skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps
  wp_reach
  intro hfl1 hsym1
  refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.call_frame_inv (x := ⟨bufRef, slot, curPtr, cur⟩)
    (ret_pc := entry + bv% (240)) hVarintCall hfl1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
    (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2SpecX]; simp only [arm64_norm, hsp_s]; rfl)
    (⟨rfl, hcur_lt⟩ : bufRef = bufRef ∧ cur.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeVarint2SpecX] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hflm hsymm
  rcases hcase with ⟨key, rest, iwt, hd, hk_ge, hwt, hitag0⟩
  by_cases hiwt_eg : iwt = .endGroup
  · subst hiwt_eg
    refine SepWPp.weaken_pre ?_ (hEndGroup sm key rest hd hk_ge hwt hitag0
      hcur_le hcur_suf hres_cur hsp_s htr_s hx19_s hx20_s hx21_s
      ⟨hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩
      hpcm hrunm hspm hcsm hflm hsymm)
    refine sepConj_mono (Entails.of_eq ?_) (by sep_frame)
    dsimp only [decodeVarint2SpecX, curPtr]
    simp only [arm64_norm, hsp_s]
  · dsimp only [decodeVarint2SpecX, curPtr]
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ bs.length := by omega
    have hrest_lt : rest.length < 2 ^ 63 := by omega
    have hrest_suf : IsDropSuffix bs rest :=
      suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    have hshr := key_shr32_of_lt hk_ge
    obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
    obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
    obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
    obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
    have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
    have hne_eg := skipGroup_of_ne_endGroup (d := d) (tag := tag) hd hk_ge hwt hitag0 hiwt_eg
    rw [hne_eg] at hres_cur
    have hiwt_ne4 := iwt_beq_4_false hiwt_eg
    obtain ⟨hiwt_w0_1, hiwt_w0_2⟩ := iwt_w0_setWidth8 iwt
    have hd_lt : d < 2 ^ 32 := by omega
    apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.of_sepWP_inv hflm hsymm (mid := entry)
    conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm, hsp_s]
    apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
    conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
      show skipBelow3 s0.sp (d + 1) = stackAt sm.sp (skipField3Stack d) from by
        rw [hspm]]
    simp only [sepConj_assoc]
    wp_steps
    wp_reach
    intro hfl2 hsym2
    refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.call_frame_inv
      (x := ⟨iwt, key.toNat / 8, d, bufRef, slot,
        ptr + BitVec.ofNat 64 (bs.length - rest.length), rest⟩)
      (ret_pc := entry + bv% (304)) hrec hfl2 hsym2
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      ?_
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr_s]) hpan) ?_
    · simp only [arm64_norm, hiwt_w0_2, sf_truncate32_ofNat64]
      exact ⟨hitag_lt, hd_lt, hrest_lt⟩
    intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hflm2 hsymm2
    simp only [CalleeSavedPreserved] at hcsm2
    obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
    simp (config := { decide := true }) only [arm64_norm, hspm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
    cases hs : skipField (2 * rest.length + 2) d (key.toNat / 8) iwt rest with
    | none =>
      rw [hs] at hres_cur
      dsimp only at hres_cur
      subst hres_cur
      apply SepWPp.of_sepWP_ret
      simp only [hs, sepConj_assoc, arm64_norm, htrm, htr_s, hspm]
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
      apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.of_sepWP_inv hflm2 hsymm2 (mid := entry + bv% (232))
      conv => arg 4; simp only [hs, sepConj_assoc, arm64_norm, hspm]
      apply SepWP.pure_elim; rintro ⟨htrm2, hsm2_0⟩
      conv => arg 4; rw [show stackAt (s0.sp - 96#64) (skipField3Stack d) = skipBelow3 s0.sp (d + 1) from rfl]
      apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le_rest) (by sep_focus)
      wp_steps
      wp_reach
      intro hfl3 hsym3
      apply SepWPp.weaken_pre (P' := skipGroupLoopPre3 A s0 d bufRef slot ptr v_stk_2 bs rest')
        (by dsimp only [skipGroupLoopPre3]; sep_frame)
      refine ih rest' _ hrest'_le_n hrest'_le_bs hrest'_suf hres_cur
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hfl3 hsym3
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

set_option maxHeartbeats 400000 in
theorem skipField7_startGroup_ok {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name +
        bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name +
        bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      ((decodeVarint2SpecX A).inImage img))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32)
    (hrec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name)
      ((skipField3SpecAt A d (fun _ => True)).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name)
      ((skipField3SpecAt A (d + 1) (fun x => x.wt = .startGroup)).inImage img) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init_inImage x s0 hfl0 hsym0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hloop : ∀ n, SkipGroupLoopStmt7 img A H s0 d tag bufRef slot ptr v_stk_2 bs
      (skipGroup (2 * bs.length + 1) (d + 1) tag bs) R n := by
    intro n
    induction n with
    | zero =>
      exact skipField7_startGroup_zero hVarintCall s0 hsp_align d tag hdepth
        bufRef slot ptr v_stk_2 bs h _ R
    | succ n ih =>
      intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hfl_s hsym_s
      by_cases hok : ∃ key rest iwt, decodeVarint cur = some (key, rest) ∧
          ¬ 2 ^ 32 ≤ key.toNat ∧ WireType.ofNat? (key.toNat % 8) = some iwt ∧ ¬ key.toNat / 8 < 1
      · exact skipField7_startGroup_succ_ok hFromCall hVarintCall s0 hsp_align d tag hdepth h_5 hrec
          bufRef slot ptr v_stk_2 bs h _ R n ih cur s hok
          hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hfl_s hsym_s
      · refine skipField7_startGroup_succ_err hFromCall hVarintCall s0 hsp_align d tag hdepth
          bufRef slot ptr v_stk_2 bs h _ R n cur s (fun key rest hd => ?_)
          hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hfl_s hsym_s
        by_cases hk : 2 ^ 32 ≤ key.toNat
        · exact Or.inl hk
        · cases hwt : WireType.ofNat? (key.toNat % 8) with
          | none => exact Or.inr (Or.inl rfl)
          | some iwt =>
            by_cases ht : key.toNat / 8 < 1
            · exact Or.inr (Or.inr ht)
            · exact absurd ⟨key, rest, iwt, hd, hk, hwt, ht⟩ hok
  dsimp only [SkipGroupLoopStmt7] at hloop
  have hfn := (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#6]")
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Varint.skipField3CliC img.base H hfn
    (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") 0 92
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Varint.skipField3CliC img.base H hfn
    (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") 224 12
  examples_generalize_entry
  examples_hide_fetches
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  obtain ⟨htag_zext1, htag_zext2⟩ := bv32_zeroExtend_ofNat h_5
  obtain ⟨hd_zext1, hd_zext2⟩ := bv32_zeroExtend_ofNat (by omega : d < 2 ^ 32)
  obtain ⟨hd_sub1, hd_sub2⟩ := bv32_sub_one_zeroExtend hdepth
  rw [skipField_succ_startGroup]
  generalize hres : skipGroup (2 * bs.length + 1) (d + 1) tag bs = res at hloop ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.of_sepWP_inv hfl0 hsym0 (mid := entry + bv% (232))
  wp_steps
  wp_reach
  intro hfl_init hsym_init
  apply SepWPp.weaken_pre (P' := skipGroupLoopPre3 A s0 d bufRef slot ptr v_stk_2 bs bs)
    (by
      dsimp only [skipGroupLoopPre3, sliceCursorAfter]
      rw [Nat.sub_self, BitVec.add_zero]
      sep_frame)
  exact hloop bs.length bs _ (Nat.le_refl _) (Nat.le_refl _) (by simp [IsDropSuffix]) hres
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm]⟩
    hfl_init hsym_init

/-! ## Combine all `WireType` cases by induction on `depth` -/

theorem skipField7_at_depth_ok {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name +
        bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name +
        bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      ((decodeVarint2SpecX A).inImage img))
    (depth : Nat) (hdepth : depth < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name)
      ((skipField3SpecAt A depth (fun _ => True)).inImage img) := by
  induction depth with
  | zero => exact skipField7_depth_zero_ok hFromCall
  | succ d ih =>
    have hrec := ih (by omega)
    have hAll :=
      subroutine_ok_skipField3_or (skipField7_varint_ok hVarintCall d hdepth)
        (subroutine_ok_skipField3_or (skipField7_sixtyFourBit_ok hFromCall d hdepth)
          (subroutine_ok_skipField3_or (skipField7_lengthDelimited_ok hFromCall hVarintCall d hdepth)
            (subroutine_ok_skipField3_or (skipField7_startGroup_ok hFromCall hVarintCall d hdepth hrec)
              (subroutine_ok_skipField3_or (skipField7_endGroup_ok hFromCall d hdepth)
                (skipField7_thirtyTwoBit_ok hFromCall d hdepth)))))
    refine subroutine_ok_skipField3_imp (fun x _ => ?_) hAll
    cases x.wt <;> simp

theorem skipField7_add_from_eq_fnAddr (b : BitVec 64) (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr skipField7Name +
      bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
            ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64) =
      (libsignalSessionCode.rebase b H).fnAddr decodeErrorFromName := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#6]",
    ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from",
    BitVec.add_assoc]
  congr 1

theorem skipField7_add_varint_eq_fnAddr (b : BitVec 64) (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr skipField7Name +
      bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" -
            ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64) =
      (libsignalSessionCode.rebase b H).fnAddr decodeVarint6Name := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#6]",
    ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]",
    BitVec.add_assoc]
  congr 1

theorem skipField7_ok_of_contracts {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name +
        bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hVarint : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarint6Name)
      ((decodeVarint2SpecX A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name)
      ((skipField3Spec A).inImage img) := by
  have hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField7Name +
        bv% ((2 ^ 64 + ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" -
              ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") % 2 ^ 64))
      ((decodeVarint2SpecX A).inImage img) := by
    rw [skipField7_add_varint_eq_fnAddr]
    exact hVarint
  exact subroutine_ok_skipField3Spec_of_at_depth
    (skipField7_at_depth_ok hFromCall hVarintCall)

/-- `prost::encoding::skip_field::<&mut &[u8]> [local#7]` meets `(skipField3Spec A).inImage img`
on `tripleRatchetProgAtExt img.base ext` under `AllocContractsX img A ext`. -/
theorem skipField7_ok_of_alloc_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr skipField7Name)
      ((skipField3Spec A).inImage img) := by
  refine skipField7_ok_of_contracts ?_ (decodeVarint6_ok_of_alloc_x hA)
  rw [skipField7_add_from_eq_fnAddr]
  exact decodeErrorFromSpecWithStack_inImage_mono (s2 := decodeErrorHookStackX)
    (decodeErrorFrom_ok_ext_x hA)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.SkipField7
