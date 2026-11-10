/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7b
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7f
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for `Variant7f`

Lifts `Variant7f.lean`'s `AllocContracts`-parameterized theorems to `AllocContracts4K`
inside `CryptoVerification.SpqrV1.States.FromPb.Ext4K`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.FromPb.Ext4K

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.FromPb

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

theorem v7_uc_err_3552_to_4632
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (e : StatesError)
    (optEnc : Option ProtoPolynomialEncoder)
    (optDec : Option ProtoPolynomialDecoder)
    (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ct1SentResultAt A (F := F) ((s0.sp - 2400#64) + 1888#64) (.error e) ∗
        optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
          memRegion (pbA + 128#64) 56 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        (sm.readReg64 .x28).extractLsb' 0 8 = 0#8 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hpre :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ct1SentResultAt A (F := F) ((s0.sp - 2400#64) + 1888#64) (.error e) ∗
        optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗ Frame ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64,
        ⌜w8.extractLsb' 0 8 = 0#8⌝ ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         ((s0.sp - 2400#64) + 1888#64) ↦₆₄ noneCap ∗
         ((s0.sp - 2400#64) + 1896#64) ↦₆₄ w8 ∗
         ((s0.sp - 2400#64) + 1904#64) ↦₆₄ w16 ∗
         ((s0.sp - 2400#64) + 1912#64) ↦₆₄ w24 ∗
         memRegion ((s0.sp - 2400#64) + 1920#64) 96 ∗
         optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
         (((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
         A.pool ∗ Frame) := by
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left
        (v7_ct1SentResult_err_unpack A (F := F) (s0.sp - 2400#64) e))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w8
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w24
    refine Entails.sepExists_right w8 (Entails.sepExists_right w16 (Entails.sepExists_right w24 ?_))
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16
  apply ProofLib.SepWP.exists_left; intro w24
  apply ProofLib.SepWP.pure_elim; intro hw8
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5444#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
      A.pool ∗
      (memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = w8 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have h1888 : (s0.sp - 2400#64) + 1888#64 = s0.sp - 512#64 := by bv_omega
    have h1896 : (s0.sp - 2400#64) + 1896#64 = s0.sp - 504#64 := by bv_omega
    have h1904 : (s0.sp - 2400#64) + 1904#64 = s0.sp - 496#64 := by bv_omega
    have h1912 : (s0.sp - 2400#64) + 1912#64 = s0.sp - 488#64 := by bv_omega
    have hjoin := v7_1888_words_to_memRegion_128 (s0.sp - 2400#64) noneCap w8 w16 w24
    rw [h1888, h1896, h1904, h1912] at hjoin ⊢
    dsimp only [noneCap] at hjoin ⊢
    states_from_pb_fetches_range b (Rust.withPanics ext) 3552 24
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · refine Entails.trans
        (Entails.of_eq (show _ =
          (((s0.sp - 512#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
           ((s0.sp - 504#64) ↦₆₄ w8) ∗
           ((s0.sp - 496#64) ↦₆₄ w16) ∗
           ((s0.sp - 488#64) ↦₆₄ w24) ∗
           memRegion ((s0.sp - 2400#64) + 1920#64) 96) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
           A.pool ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hjoin) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    have h5444 := Ext4K.v7_cleanup_5444 hA s0 s2 out pbA cap_dec w8 optEnc optDec
      (memRegion (s0.sp - 512#64) 128 ∗ Frame)
      hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
    have h1888 : (s0.sp - 2400#64) + 1888#64 = s0.sp - 512#64 := by bv_omega
    rw [h1888]
    refine SepWP.mono h5444 ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx28_f, htr_f⟩
    rw [hx28_f]
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, hw8, htr_f⟩

end CryptoVerification.SpqrV1.States.FromPb.Ext4K
