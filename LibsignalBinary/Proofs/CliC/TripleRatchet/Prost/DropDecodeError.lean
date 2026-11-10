/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CliC.TripleRatchet.Prost.Defs
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `drop_glue<DecodeError>` Verification for `CliC`

Proves `dropDecodeErrorSpec` and `(dropDecodeErrorSpecX A).inImage img` for
`core::ptr::drop_glue::<prost::error::DecodeError>` in `CliC`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

def _root_.CryptoVerification.CliC.LibsignalTripleRatchet.Prost.DropDecodeErrorOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeErrorName)
    (dropDecodeErrorSpec A)

theorem _root_.CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_ok_of_contract {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeErrorName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]") % 2^64))
      (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeErrorName)
      (dropDecodeErrorSpec A) := by
  unfold dropDecodeErrorSpec
  simp only [decodeErrorAt, decodeErrorAtStackLen, vecOf, vecAt, vecHeader, vecBuf,
    stackAt_dropDecodeError, sepExists_sepConj_left, sepExists_sepConj_right, List.length_replicate]
  have hfn := (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]")
  tripleRatchet_fetches b H hfn (num% (ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]")) 164
  wp_init e s0
  examples_generalize_entry
  examples_hide_fetches
  have hbr := kindNoHeap_branch_false h
  by_cases hcap0 : v_stk_6 = 0
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e 0 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeError_tail s0.sp _ _ _ _) (by sep_focus)
    wp_apply
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeError_post s0.sp)) (by sep_focus)
    wp_done
  · have hcap_beq : (v_stk_6 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hshl : (v_stk_6 <<< 5).toNat = v_stk_6.toNat * 32 := shl5_toNat h_4
    simp only [hcap0, ite_false, stackVec_buf_memRegion h_3 h_4]
    wp_steps
    wp_apply
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e v_stk_6 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeError_tail s0.sp _ _ _ _) (by sep_focus)
    wp_apply
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeError_post s0.sp)) (by sep_focus)
    wp_done

theorem _root_.CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    CryptoVerification.CliC.LibsignalTripleRatchet.Prost.DropDecodeErrorOkExt b A ext :=
  CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_ok_of_contract
    (hA.dealloc_ok_at CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeErrorName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]"))
      (by rw [(ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]")]; simp only [arm64_norm]))

theorem _root_.CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    CryptoVerification.CliC.LibsignalTripleRatchet.Prost.DropDecodeErrorOk b C A ctl abs :=
  CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_ok_of_contract
    (dealloc_ok_at (b := b) (C := C) (ctl := ctl)
      hA (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]") (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]")) (by simp only [arm64_norm]))

/-! ## `AllocContractsX` `.inImage` Variants -/

def _root_.CryptoVerification.CliC.LibsignalTripleRatchet.Prost.DropDecodeErrorOkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeErrorName)
    ((dropDecodeErrorSpecX A).inImage img)

theorem _root_.CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_ok_of_contract_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeErrorName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]") % 2^64))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeErrorName)
      ((dropDecodeErrorSpecX A).inImage img) := by
  simp only [Spec.inImage, dropDecodeErrorSpecX, decodeErrorAt, decodeErrorAtStackLen, vecOf, vecAt,
    vecHeader, vecBuf, stackAt_dropDecodeErrorX, sepExists_sepConj_left, sepExists_sepConj_right,
    List.length_replicate, pure_sepConj_pure_assoc]
  simp only [Spec.inImage, rustDeallocExternSpecWithStack] at hdealloc
  have hfn := (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]")
  tripleRatchet_fetches img.base H hfn (num% (ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]")) 164
  wp_init e s0
  examples_generalize_entry
  examples_hide_fetches
  have hbr := kindNoHeap_branch_false h
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have h_len_le : v_stk_4 ≤ v_stk_6.toNat := by assumption
  have h_cap_lt : v_stk_6.toNat * 32 < 2 ^ 63 := by assumption
  by_cases hcap0 : v_stk_6 = 0
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    apply SepWP.seq_callInv (mid_pc := entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]") % 2^64)) (by assumption) (by assumption)
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e 0 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorX_tail s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.done (by rfl) (by simp only [arm64_norm, hrun])
    intro hfl1 hsym1
    wp_call hdealloc (e, 72, 8)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorX_post s0.sp)) (by sep_focus)
    wp_done
  · have hcap_beq : (v_stk_6 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hshl : (v_stk_6 <<< 5).toNat = v_stk_6.toNat * 32 := shl5_toNat h_cap_lt
    have hlay_vec : LayoutOk (v_stk_6.toNat * 32) 8 := layoutOk_mul32_8 hcap0 h_cap_lt
    have hpos_vec : 0 < v_stk_6.toNat * 32 := hlay_vec.1
    have hsum_vec : v_stk_6.toNat * 32 + 8 ≤ 2 ^ 63 := hlay_vec.2.2
    simp only [hcap0, ite_false, stackVec_buf_memRegion h_len_le h_cap_lt]
    apply SepWP.seq_callInv (mid_pc := entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]") % 2^64)) (by assumption) (by assumption)
    wp_steps
    apply SepWP.done (by rfl) (by simp only [arm64_norm, hrun])
    intro hfl1 hsym1
    apply SepWP.seq_callInv (mid_pc := entry + bv% (72)) hfl1 hsym1
    wp_call hdealloc (v_stk_7, v_stk_6.toNat * 32, 8)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hfl1' hsym1'
    apply SepWP.seq_callInv (mid_pc := entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]") % 2^64)) hfl1' hsym1'
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e v_stk_6 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorX_tail s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.done (by rfl) (by simp only [arm64_norm, *])
    intro hfl2 hsym2
    wp_call hdealloc (e, 72, 8)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorX_post s0.sp)) (by sep_focus)
    wp_done

theorem _root_.CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    CryptoVerification.CliC.LibsignalTripleRatchet.Prost.DropDecodeErrorOkExtX img A ext :=
  CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_ok_of_contract_x
    (hA.dealloc_ok_at CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeErrorName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]"))
      (by rw [(ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]")]; simp only [arm64_norm]))

end CryptoVerification.LibsignalTripleRatchet.Prost
