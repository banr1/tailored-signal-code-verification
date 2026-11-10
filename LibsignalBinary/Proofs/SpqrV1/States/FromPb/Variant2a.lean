/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-! # `<spqr::v1::chunked::states::States>::from_pb`: Variant 1 (`KeysSampled`, `+1104`) — Part A -/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-! ## Callee Relocation Lemmas for `States::from_pb` (`0x5a0a4`) -/

theorem v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName +
        18446744073709495388#64)
      (dropProtoPolyEncoderSpec A) := by
  have h := drop_glue_proto_poly_encoder_ok_ext hA.dealloc
  have haddr : (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName +
      18446744073709495388#64 =
      (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName := by
    simp only [tripleRatchetProgAtExt, dropProgAtExt, Program.fnAddr_rebase,
      statesFromPbName, dropProtoPolyEncoderName,
      statesFromPb_fnOff, fnOff_drop_proto_poly_encoder]
    bv_omega
  rw [haddr]
  exact h

theorem v1_encoder_from_pb_ok_at_statesFromPb {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (henc : EncoderFromPbOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 32996#64)
      (encoderFromPbSpec A) := by
  have haddr : (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 32996#64 =
      (contractProg b ext).fnAddr encoderFromPbName := by
    simp only [contractProg, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      statesFromPbName, encoderFromPbName,
      statesFromPb_fnOff, fnOff_poly_encoder_from_pb]
    bv_omega
  rw [haddr]
  exact henc

theorem v1_dealloc_ok_at_statesFromPb {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff stubOff_rust_dealloc (by decide))
    hA.dealloc

/-- Shared `Err(Error::StateDecode)` exit at `+5940` (`0x5b7d8 -> +60 -> s0.x30`):
    when `x26` has low byte `0#8` (`spqrErrorByte .stateDecode`) and `x19 = out`,
    writes `[out + 16..32] = (x22, x8)`, `x8 = noneCap`, `[out + 8] = x26`, and branches to `+60`. -/
theorem v1_err_5940
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5940#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rw [memRegion_out_928_split_32 out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v24
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v0
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 60#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (out ↦₆₄ v0) ∗
      ((out + 8#64) ↦₈ spqrErrorByte .stateDecode) ∗
      memRegion (out + 9#64) 919 ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x8 = noneCap ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 5940 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htail := out_8_32_entails_err_tail out (s1.readReg64 .x26)
        (s1.readReg64 .x22) (s1.readReg64 .x8)
      rw [hx26_1] at htail
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ s1.readReg64 .x26) ∗
           ((out + 16#64) ↦₆₄ s1.readReg64 .x22) ∗
           ((out + 24#64) ↦₆₄ s1.readReg64 .x8) ∗
           memRegion (out + 32#64) 896) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60 s0 s2 out .stateDecode v0 Rest hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

/-- Seven 64-bit words of a 56-byte `Option<ProtoPolynomialEncoder>` at `a`. -/
def v1_optProtoPolyEncoderWordsAt (a w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
  ((a + 48#64) ↦₆₄ w48)

/-- Heap and pure constraints of `Option<ProtoPolynomialEncoder>` associated with words `w0..w48`. -/
def v1_optProtoPolyEncoderHeap (A : RustAlloc) :
    Option ProtoPolynomialEncoder → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some pb, w0, w8, w16, w24, w32, w40, w48 =>
    ⌜w0.toNat < 2 ^ 63 ∧ w16 = BitVec.ofNat 64 pb.pts.length ∧
      w40 = BitVec.ofNat 64 pb.polys.length ∧ w48.extractLsb' 0 32 = pb.idx⌝ ∗
    vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ∗
    vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys

theorem v1_optProtoPolyEncoderWordsAt_entails_56 (a w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v1_optProtoPolyEncoderWordsAt a w0 w8 w16 w24 w32 w40 w48 ⊢ memRegion a 56 := by
  unfold v1_optProtoPolyEncoderWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v1_pointsTo32_4_entails_pointsTo64 (a : BitVec 64) (lo : BitVec 32) :
    (a ↦₃₂ lo) ∗ memRegion (a + 4#64) 4 ⊢
      ∃∗ w : BitVec 64, ⌜w.extractLsb' 0 32 = lo⌝ ∗ (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_four (a + 4#64), sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro hi
  refine Entails.sepExists_right (hi ++ lo) ?_
  have hlo : (hi ++ lo).extractLsb' 0 32 = lo := by bv_kernel
  refine Entails.pure_right hlo ?_
  rw [ProofLib.pointsTo32_pair a lo hi]
  exact Entails.refl _

theorem v1_pointsTo64_entails_pointsTo32_4 (a w : BitVec 64) (lo : BitVec 32)
    (hlo : w.extractLsb' 0 32 = lo) :
    (a ↦₆₄ w) ⊢ (a ↦₃₂ lo) ∗ memRegion (a + 4#64) 4 := by
  have hw : w = w.extractLsb' 32 32 ++ lo := by
    rw [← hlo]
    bv_kernel
  rw [hw, ← ProofLib.pointsTo32_pair a lo (w.extractLsb' 32 32)]
  exact sepConj_mono_right (ProofLib.pointsTo32_entails_memRegion _ _)

theorem v1_optProtoPolyEncoderAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) :
    optProtoPolynomialEncoderAt A a optEnc ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64,
        v1_optProtoPolyEncoderWordsAt a w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 := by
  cases optEnc with
  | none =>
    dsimp only [optProtoPolynomialEncoderAt, optProtoPolynomialEncoderNoneTailSize,
      v1_optProtoPolyEncoderHeap]
    have hsplit : memRegion (a + 8#64) 48 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
        (∃∗ w40 : BitVec 64, (a + 40#64) ↦₆₄ w40) ∗
        (∃∗ w48 : BitVec 64, (a + 48#64) ↦₆₄ w48) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w48
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40
          (Entails.sepExists_right w48 ?_))))))
    unfold v1_optProtoPolyEncoderWordsAt
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some pb =>
    dsimp only [optProtoPolynomialEncoderAt, protoPolynomialEncoderAt,
      vecVecU8At, vecOf, vecAt, vecHeader,
      protoPolynomialEncoderPolysOff, protoPolynomialEncoderIdxOff,
      protoPolynomialEncoderPadOff, protoPolynomialEncoderPadSize,
      v1_optProtoPolyEncoderHeap]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w8
    have h48 := v1_pointsTo32_4_entails_pointsTo64 (a + 48#64) pb.idx
    have ha48 : (a + 48#64) + 4#64 = a + 52#64 := by bv_omega
    rw [ha48] at h48
    have hcap : vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ⊢
        ⌜w0.toNat < 2 ^ 63⌝ ∗ vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts := by
      unfold vecBuf
      apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
      exact Entails.pure_right (by omega) (Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _))
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hcap (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right h48)))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w48
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    rw [ha32, ha40]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜w0.toNat < 2 ^ 63⌝ ∗ ⌜w48.extractLsb' 0 32 = pb.idx⌝ ∗
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗
       ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗ ((a + 48#64) ↦₆₄ w48) ∗
       vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ∗
       vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys) by ac_rfl)) ?_
    apply Entails.pure_left; intro hw0
    apply Entails.pure_left; intro hw48
    refine Entails.sepExists_right w0 (Entails.sepExists_right w8
      (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length)
        (Entails.sepExists_right w24 (Entails.sepExists_right w32
          (Entails.sepExists_right (BitVec.ofNat 64 pb.polys.length)
            (Entails.sepExists_right w48 ?_))))))
    unfold v1_optProtoPolyEncoderWordsAt
    have hpure : w0.toNat < 2 ^ 63 ∧ BitVec.ofNat 64 pb.pts.length = BitVec.ofNat 64 pb.pts.length ∧
        BitVec.ofNat 64 pb.polys.length = BitVec.ofNat 64 pb.polys.length ∧
        w48.extractLsb' 0 32 = pb.idx := ⟨hw0, rfl, rfl, hw48⟩
    exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v1_optProtoPolyEncoderAt_pack_some (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v1_optProtoPolyEncoderWordsAt a w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A (some pb) w0 w8 w16 w24 w32 w40 w48 ⊢
      protoPolynomialEncoderAt A a pb := by
  dsimp only [v1_optProtoPolyEncoderWordsAt, v1_optProtoPolyEncoderHeap,
    protoPolynomialEncoderAt, vecVecU8At, vecOf, vecAt, vecHeader,
    protoPolynomialEncoderPolysOff, protoPolynomialEncoderIdxOff,
    protoPolynomialEncoderPadOff, protoPolynomialEncoderPadSize]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w0.toNat < 2 ^ 63 ∧ w16 = BitVec.ofNat 64 pb.pts.length ∧
      w40 = BitVec.ofNat 64 pb.polys.length ∧ w48.extractLsb' 0 32 = pb.idx⌝ ∗
    (((a + 48#64) ↦₆₄ w48) ∗
     ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
      ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
      vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ∗
      vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨_, rfl, rfl, hw48⟩
  have h48 := v1_pointsTo64_entails_pointsTo32_4 (a + 48#64) w48 pb.idx hw48
  have ha48 : (a + 48#64) + 4#64 = a + 52#64 := by bv_omega
  rw [ha48] at h48
  refine Entails.trans (sepConj_mono_left h48) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_right w24 (Entails.sepExists_right w32
    (Entails.sepExists_right w0 (Entails.sepExists_right w8 ?_)))
  have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  rw [ha32, ha40]
  exact Entails.of_eq (by ac_rfl)

theorem v1_optProtoPolyEncoderHeap_extract_w0 (A : RustAlloc)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ⊢
      ⌜match optEnc with | none => w0 = noneCap | some _ => w0.toNat < 2 ^ 63⌝ ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 := by
  cases optEnc with
  | none =>
    dsimp only [v1_optProtoPolyEncoderHeap]
    conv => lhs; rw [← sepConj_emp ⌜w0 = noneCap⌝]
    apply Entails.pure_left; intro hw0
    exact Entails.pure_right hw0 (Entails.trans (Entails.pure_right hw0 (Entails.refl _)) (Entails.of_eq (sepConj_emp _)))
  | some pb =>
    dsimp only [v1_optProtoPolyEncoderHeap]
    apply Entails.pure_left; rintro ⟨hw0, hw16, hw40, hw48⟩
    have hp : w0.toNat < 2 ^ 63 ∧ w16 = BitVec.ofNat 64 pb.pts.length ∧
        w40 = BitVec.ofNat 64 pb.polys.length ∧ w48.extractLsb' 0 32 = pb.idx :=
      ⟨hw0, hw16, hw40, hw48⟩
    exact Entails.pure_right hw0 (Entails.pure_right hp (Entails.refl _))

theorem v1_tbz_63_of_lt {w : BitVec 64} (h : w.toNat < 2 ^ 63) :
    ((w >>> 63) &&& 1#64 == 0#64) = true := by
  have h1 : (w >>> 63) &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt h, Nat.zero_and]
    rfl
  simp [h1]

theorem v1_stackAt_encoder_split_dropStack48 (sp : BitVec 64) :
    stackAt sp encoderFromPbStack =
      memRegion (sp - 5152#64) 1008 ∗ stackAt sp dropStack48 :=
  stackAt_split_bottom sp dropStack48 1008 (by decide)

theorem v1_memRegion_1496_split_232 (fsp : BitVec 64) :
    memRegion fsp 1496 ⊢
      memRegion fsp 232 ∗
      (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 1256 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v1_merge_stack_1496_56_752 (fsp w232 : BitVec 64) :
    memRegion fsp 232 ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 1256 ∗
      memRegion (fsp + 1496#64) 56 ∗
      memRegion (fsp + 1552#64) 752 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

/-- Drop `Option<ProtoPolynomialEncoder>` at `fsp + 1496` and return `Err(StateDecode)` (`+4332 -> s0.x30`). -/
theorem v1_drop_sendingHdr_4332
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4332#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hex := v1_optProtoPolyEncoderHeap_extract_w0 A optEnc w0 w8 w16 w24 w32 w40 w48
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono (v1_memRegion_1496_split_232 (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_left hex)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
  apply ProofLib.SepWP.exists_left; intro w232
  apply SepWP.pure_elim; intro hw0_cond
  have hmerge := v1_merge_stack_1496_56_752 (s0.sp - 2400#64) w232
  cases optEnc with
  | none =>
    subst hw0_cond
    dsimp only [v1_optProtoPolyEncoderHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5940#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (A.pool ∗ Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        (sm.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 4332 32
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, v1_optProtoPolyEncoderWordsAt,
        noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hw_mem := v1_optProtoPolyEncoderWordsAt_entails_56
          (s0.sp - 2400#64 + 1496#64) 18446744073709551615#64 w8 w16 w24 w32 w40 w48
        dsimp only [v1_optProtoPolyEncoderWordsAt] at hw_mem
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 232 ∗
           ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
           memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
           (((s0.sp - 2400#64 + 1496#64) ↦₆₄ 18446744073709551615#64) ∗
            ((s0.sp - 2400#64 + 1496#64 + 8#64) ↦₆₄ w8) ∗
            ((s0.sp - 2400#64 + 1496#64 + 16#64) ↦₆₄ w16) ∗
            ((s0.sp - 2400#64 + 1496#64 + 24#64) ↦₆₄ w24) ∗
            ((s0.sp - 2400#64 + 1496#64 + 32#64) ↦₆₄ w32) ∗
            ((s0.sp - 2400#64 + 1496#64 + 40#64) ↦₆₄ w40) ∗
            ((s0.sp - 2400#64 + 1496#64 + 48#64) ↦₆₄ w48)) ∗
           memRegion (s0.sp - 2400#64 + 1552#64) 752) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left hw_mem))))) ?_
        exact Entails.trans (sepConj_mono_left hmerge) (Entails.of_eq (by ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
      have herr := v1_err_5940 (A := A) (F := F) s0 s2 out (A.pool ∗ Rest)
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2
      refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩
  | some pbEnc =>
    have hpack := v1_optProtoPolyEncoderAt_pack_some A (s0.sp - 2400#64 + 1496#64) pbEnc
      w0 w8 w16 w24 w32 w40 w48
    have hne := cap_add_one_beq_zero_false hw0_cond
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hdrop := v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb hA
    simp only [dropProtoPolyEncoderSpec] at hdrop
    have h904 : s0.sp - 2400#64 + 1496#64 = s0.sp - 904#64 := by bv_omega
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4352#64)
      (P_mid :=
        protoPolynomialEncoderAt A (s0.sp - 904#64) pbEnc ∗
        A.pool ∗
        stackAt (s0.sp - 2400#64) dropStack48 ∗
        (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
         memRegion (s0.sp - 2400#64) 232 ∗
         ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
         memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
         memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = s0.sp - 904#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = s1.readReg64 .x26 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 4332 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, v1_optProtoPolyEncoderWordsAt,
        BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), ← h904]
        refine Entails.trans (Entails.of_eq (show _ =
          (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48) ∗
          (A.pool ∗ stackAt (s0.sp - 2400#64) dropStack48 ∗
           (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
            memRegion (s0.sp - 2400#64) 232 ∗
            ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
            memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
            memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by
            dsimp only [v1_optProtoPolyEncoderWordsAt]; ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hpack) (Entails.of_eq (by ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx26_2, htr2⟩
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5940#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          (A.pool ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          (sm.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 4352 12
        dsimp only [tripleRatchetProgAtExt, statesFromPbName,
          BitVec.ofNat_eq_ofNat] at hdrop hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        wp_call hdrop ⟨s0.sp - 904#64, pbEnc⟩
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have h7552 : s0.sp - 2400#64 - 5152#64 = s0.sp - 7552#64 := by bv_omega
          rw [v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), h7552, ← h904, hsp2]
          dsimp only [protoPolynomialEncoderSize]
          simp only [arm64_norm] at hmerge ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 232 ∗
             ((s0.sp - 2168#64) ↦₆₄ w232) ∗
             memRegion (s0.sp - 2160#64) 1256 ∗
             memRegion (s0.sp - 904#64) 56 ∗
             memRegion (s0.sp - 848#64) 752) ∗
            (memRegion (s0.sp - 7552#64) 1008 ∗
             stackAt (s0.sp - 2400#64) dropStack48 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hmerge) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
        have herr := v1_err_5940 (A := A) (F := F) s0 s3 out (A.pool ∗ Rest)
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
        refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

theorem v1_drop_sendingHdr_4204
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4204#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4332#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1496 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 4204 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, spqrErrorByte,
      BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    exact v1_drop_sendingHdr_4332 (A := A) (F := F) hA s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48 Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2

/-! ## Error Cleanup for `uc` (`ek`, `dk`, `auth`) + `sendingHdr` (`+3872 -> +3936 -> +4328 -> +4332`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem v1_bv_sub_sub_lit (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_shl8_extract_0_8 (w : BitVec 64) :
    ((w &&& 72057594037927935#64) <<< 8).extractLsb' 0 8 = 0#8 := by
  bv_kernel

theorem v1_merge_stack_192_216_224_1496 (fsp w192 w216 w224 : BitVec 64) :
    memRegion fsp 192 ∗
      ((fsp + 192#64) ↦₆₄ w192) ∗
      memRegion (fsp + 200#64) 16 ∗
      ((fsp + 216#64) ↦₆₄ w216) ∗
      ((fsp + 224#64) ↦₆₄ w224) ∗
      memRegion (fsp + 232#64) 1264 ⊢
      memRegion fsp 1496 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

/-- Cleanup `ek` (`x9 = ptr_ek`, `x20 = cap_ek`), `dk` (`[fsp+216] = ptr_dk`, `[fsp+224] = cap_dk`),
    and `sendingHdr` at `fsp + 1496..1552`, returning `Err(StateDecode)` (`+3936 -> s0.x30`). -/
theorem v1_drop_uc_and_sendingHdr_3936
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out cap_ek ptr_ek cap_dk ptr_dk w192 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = cap_ek)
    (hx9_1 : s1.readReg64 .x9 = ptr_ek)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A cap_ek ptr_ek ∗
        vecCapPtrDealloc A cap_dk ptr_dk ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v1_dealloc_ok_at_statesFromPb hA
  simp only [rustDeallocSpec] at hdealloc
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3956#64)
    (P_mid :=
      memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      memRegion (s0.sp - 2400#64) 192 ∗
      ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
      memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
      ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
      memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      vecCapPtrDealloc A cap_dk ptr_dk ∗
      A.pool ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x20 = cap_ek ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 3936 20
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
      BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_cases hc_ek : (cap_ek == 0#64) = true <;>
      simp only [hc_ek, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply
      refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4332#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        Rest)
      (Q := fun s3 =>
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        (s3.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
        TraceCalleeSaved s3 s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 3956 60
      states_from_pb_fetches_range b (Rust.withPanics ext) 4328 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc, spqrErrorByte,
        BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      by_cases hc_dk : (cap_dk == 0#64) = true <;>
        simp only [hc_dk, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
          have hm := v1_merge_stack_192_216_224_1496 (s0.sp - 2400#64) w192 ptr_dk cap_dk
          simp only [arm64_norm] at hm ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 192 ∗
             ((s0.sp - 2208#64) ↦₆₄ w192) ∗
             memRegion (s0.sp - 2200#64) 16 ∗
             ((s0.sp - 2184#64) ↦₆₄ ptr_dk) ∗
             ((s0.sp - 2176#64) ↦₆₄ cap_dk) ∗
             memRegion (s0.sp - 2168#64) 1264) ∗
            (memRegion (s0.sp - 7552#64) 1056 ∗
             stackAt (s0.sp - 2400#64) allocHookStack ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 848#64) 752 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
        · wp_done
      · wp_steps; wp_apply; wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp2]
          have hm := v1_merge_stack_192_216_224_1496 (s0.sp - 2400#64) (s2.readReg64 .x22) ptr_dk cap_dk
          simp only [arm64_norm] at hm ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 192 ∗
             ((s0.sp - 2208#64) ↦₆₄ s2.readReg64 .x22) ∗
             memRegion (s0.sp - 2200#64) 16 ∗
             ((s0.sp - 2184#64) ↦₆₄ ptr_dk) ∗
             ((s0.sp - 2176#64) ↦₆₄ cap_dk) ∗
             memRegion (s0.sp - 2168#64) 1264) ∗
            (memRegion (s0.sp - 7552#64) 1056 ∗
             stackAt (s0.sp - 2400#64) allocHookStack ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 848#64) 752 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
        · wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
      exact v1_drop_sendingHdr_4332 (A := A) (F := F) hA s0 s3 out optEnc
        w0 w8 w16 w24 w32 w40 w48 Rest hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3

/-- Heap and pure constraints of `Option<ProtoAuthenticator>` associated with words `u56..u96`. -/
def v1_optProtoAuthHeap (A : RustAlloc) :
    Option ProtoAuthenticator → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, u56, _, _, _, _, _ => ⌜u56 = noneCap⌝
  | some auth, u56, u64, u72, u80, u88, u96 =>
    ⌜u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 auth.rootKey.length ∧
      u96 = BitVec.ofNat 64 auth.macKey.length⌝ ∗
    vecU8Payload A u56 u64 auth.rootKey ∗
    vecU8Payload A u80 u88 auth.macKey

/-- Cleanup `optAuth` (`x25 = u56, x28 = u64, x23 = u80, x24 = u88`), `ek`, `dk`, and `sendingHdr`,
    returning `Err(StateDecode)` (`+3872 -> +3936 -> s0.x30`). -/
theorem v1_drop_uc_and_sendingHdr_3872
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out cap_ek ptr_ek cap_dk ptr_dk w192 : BitVec 64)
    (optAuth : Option ProtoAuthenticator) (u56 u64 u72 u80 u88 u96 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = cap_ek)
    (hx9_1 : s1.readReg64 .x9 = ptr_ek)
    (hx25_1 : s1.readReg64 .x25 = u56)
    (hx28_1 : s1.readReg64 .x28 = u64)
    (hx23_1 : s1.readReg64 .x23 = u80)
    (hx24_1 : s1.readReg64 .x24 = u88)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A cap_ek ptr_ek ∗
        vecCapPtrDealloc A cap_dk ptr_dk ∗
        v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  cases optAuth with
  | none =>
    dsimp only [v1_optProtoAuthHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; intro hu56
    subst hu56
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3936#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A cap_ek ptr_ek ∗
        vecCapPtrDealloc A cap_dk ptr_dk ∗
        A.pool ∗
        Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = cap_ek ∧
        s2.readReg64 .x9 = ptr_ek ∧
        TraceCalleeSaved s2 s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 3872 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap,
        BitVec.ofNat_eq_ofNat] at hpc1 hx25_1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps; wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx9_2, htr2⟩
      exact v1_drop_uc_and_sendingHdr_3936 (A := A) (F := F) hA s0 s2 out
        cap_ek ptr_ek cap_dk ptr_dk w192 optEnc w0 w8 w16 w24 w32 w40 w48 Rest
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx9_2 htr2
  | some auth =>
    dsimp only [v1_optProtoAuthHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; rintro ⟨hu56, _, _⟩
    have hcmn : (u56 + 1#64 == 0#64) = false :=
      Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hu56)
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
    have hdealloc := v1_dealloc_ok_at_statesFromPb hA
    simp only [rustDeallocSpec] at hdealloc
    have hd_root := vecU8Payload_entails_dealloc A u56 u64 auth.rootKey
    have hd_mac := vecU8Payload_entails_dealloc A u80 u88 auth.macKey
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A u56 u64 auth.rootKey ∗
      vecU8Payload A u80 u88 auth.macKey ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 192 ∗
       ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
       memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
       ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
       ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
       memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       vecCapPtrDealloc A cap_ek ptr_ek ∗
       vecCapPtrDealloc A cap_dk ptr_dk ∗
       A.pool ∗
       Rest) by ac_rfl))
      (sepConj_mono hd_root (sepConj_mono_left hd_mac))) ?_
    rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
    wp_simp_pre [sepConj_assoc]
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3908#64)
      (P_mid :=
        vecCapPtrDealloc A u80 u88 ∗
        memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
        stackAt (s0.sp - 2400#64) allocHookStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A cap_ek ptr_ek ∗
        vecCapPtrDealloc A cap_dk ptr_dk ∗
        A.pool ∗
        Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = cap_ek ∧
        s2.readReg64 .x9 = ptr_ek ∧
        s2.readReg64 .x23 = u80 ∧
        s2.readReg64 .x24 = u88 ∧
        TraceCalleeSaved s2 s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 3872 36
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
        BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      by_cases hc_r : (u56 == 0#64) = true <;>
        simp only [hc_r, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply; wp_steps
        refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx9_2, hx23_2, hx24_2, htr2⟩
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3936#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 192 ∗
          ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
          memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
          memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A cap_ek ptr_ek ∗
          vecCapPtrDealloc A cap_dk ptr_dk ∗
          A.pool ∗
          Rest)
        (Q := fun s3 =>
          s3.sp = s0.sp - 2400#64 ∧
          s3.readReg64 .x19 = out ∧
          s3.readReg64 .x20 = cap_ek ∧
          s3.readReg64 .x9 = ptr_ek ∧
          TraceCalleeSaved s3 s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 3908 28
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
          BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        by_cases hc_m : (u80 == 0#64) = true <;>
          simp only [hc_m, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine EncoderFromPb.align_pre ?_ ?_
          · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
            simp only [arm64_norm]
            exact Entails.of_eq (by ac_rfl)
          · wp_done
        · wp_steps; wp_apply; wp_steps
          refine EncoderFromPb.align_pre ?_ ?_
          · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp2]
            simp only [arm64_norm]
            exact Entails.of_eq (by ac_rfl)
          · wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx20_3, hx9_3, htr3⟩
        exact v1_drop_uc_and_sendingHdr_3936 (A := A) (F := F) hA s0 s3 out
          cap_ek ptr_ek cap_dk ptr_dk w192 optEnc w0 w8 w16 w24 w32 w40 w48 Rest
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx9_3 htr3

/-! ## Word Unpacking & 128-bit Pairing Helpers for `uc` (`104`B) and `sendingHdr` (`56`B) -/

@[local simp, local arm64_norm, local wp_norm]
theorem v1_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-- Thirteen 64-bit words of a 104-byte `Option<V1State.Unchunked.HeaderSent>` at `a`. -/
def v1_ucWordsAt (a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) : SepProp :=
  (a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ u24) ∗
  ((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ u48) ∗
  ((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ u72) ∗
  ((a + 72#64) ↦₆₄ u80) ∗ ((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96) ∗
  ((a + 96#64) ↦₆₄ u104)

theorem v1_ucWordsAt_entails_104
    (a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) :
    v1_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ⊢ memRegion a 104 := by
  unfold v1_ucWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

/-- Ten 128-bit (`↦₁₂₈`) chunks covering `pbA + 8..168` (`160` bytes). -/
def v1_pb128At (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  ((pbA + 8#64) ↦₁₂₈ (u16 ++ u8)) ∗
  ((pbA + 24#64) ↦₁₂₈ (u32 ++ u24)) ∗
  ((pbA + 40#64) ↦₁₂₈ (u48 ++ u40)) ∗
  ((pbA + 56#64) ↦₁₂₈ (u64 ++ u56)) ∗
  ((pbA + 72#64) ↦₁₂₈ (u80 ++ u72)) ∗
  ((pbA + 88#64) ↦₁₂₈ (u96 ++ u88)) ∗
  ((pbA + 104#64) ↦₁₂₈ (w0 ++ u104)) ∗
  ((pbA + 120#64) ↦₁₂₈ (w16 ++ w8)) ∗
  ((pbA + 136#64) ↦₁₂₈ (w32 ++ w24)) ∗
  ((pbA + 152#64) ↦₁₂₈ (w48 ++ w40))

theorem v1_uc_and_enc_words_eq_pb128
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
     w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
      v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 =
      v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        w0 w8 w16 w24 w32 w40 w48 := by
  dsimp only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt, v1_pb128At]
  simp only [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128, arm64_norm]

theorem v1_pb128_entails_112_and_enc
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
     w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000001#64) ∗
      v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        w0 w8 w16 w24 w32 w40 w48 ⊢
      memRegion pbA 112 ∗
      v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 := by
  rw [← v1_uc_and_enc_words_eq_pb128]
  have h104 := v1_ucWordsAt_entails_104 (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
  have h112 : (pbA ↦₆₄ 0x8000000000000001#64) ∗ memRegion (pbA + 8#64) 104 ⊢ memRegion pbA 112 :=
    collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    ((pbA ↦₆₄ 0x8000000000000001#64) ∗
      v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
    v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 by ac_rfl)) ?_
  exact sepConj_mono (Entails.trans (sepConj_mono_right h104) h112) (Entails.refl _)

theorem v1_pb128_entails_full_224
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
     w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000001#64) ∗
      v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (pbA + 168#64) 56 ⊢
      memRegion pbA optProtoInnerStateSize := by
  have h1 := v1_pb128_entails_112_and_enc pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    w0 w8 w16 w24 w32 w40 w48
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48
  have h224 : memRegion pbA 112 ∗ memRegion (pbA + 112#64) 56 ∗ memRegion (pbA + 168#64) 56 ⊢
      memRegion pbA optProtoInnerStateSize :=
    collapse_top <| collapse_step0 (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    ((pbA ↦₆₄ 0x8000000000000001#64) ∗
      v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        w0 w8 w16 w24 w32 w40 w48) ∗
    memRegion (pbA + 168#64) 56 by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left h1) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion pbA 112 ∗
    v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (pbA + 168#64) 56 by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left h56)) h224

end CryptoVerification.SpqrV1.States.FromPb
