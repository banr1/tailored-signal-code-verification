/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7b
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# SPQR V1 `<States>::from_pb`: Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part B

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant7b.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

variable [LibsignalPlacement]

/-! ## 1. `Option<ProtoPolynomialDecoder>` Cleanup at `+4548`, `+4528`, `+5444` -/

/-- Placed cleanup of `Option<ProtoPolynomialDecoder>` at `+4548` (`+4548 -> +4632`):
given `x22 = cap_dec`, `x27 = pbA`, and `(pbA + 184#64 ↦₆₄ cap_dec) ∗ v7_optProtoPolyDecoderTail`,
deallocates `optDec` if `some` and reaches `+4632` with `memRegion (pbA + 184#64) 40`. -/
theorem v7_cleanup_opt_decoder_4548_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4548#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  cases optDec with
  | none =>
    unfold v7_optDecoderCapProp at hcap_dec
    subst hcap_dec
    unfold v7_optProtoPolyDecoderTail
    dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx22_1 ⊢
    change s1.pc = (blkPl_333).base + 4548#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4632#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hm := optProtoPolyDecoder_none_entails_memRegion_40 (pbA + 184#64)
      dsimp only [noneCap] at hm
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 184#64) ↦₆₄ 18446744073709551615#64) ∗
           memRegion ((pbA + 184#64) + 8#64) 32) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
    · wp_done
  | some pb =>
    refine SepWP.weaken_pre (v7_cleanup_opt_decoder_some_pre A (s0.sp - 2400#64) pbA cap_dec pb Frame) ?_
    apply ProofLib.SepWP.exists_left; intro ptsPtr
    apply ProofLib.SepWP.pure_elim; rintro ⟨hpts_le, hpts_cap_lt, _⟩
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 4556#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         (if cap_dec = 0 then emp
          else A.live ptsPtr (cap_dec.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
              ((cap_dec.toNat - pb.pts.length) * 24)) ∗
         memRegion (pbA + 208#64) 16) ∗
        A.pool ∗
        Frame)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
      change s1.pc = (blkPl_333).base + 4548#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4556#64) s1 _ _
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
      exact v7_proto_decoder_dealloc_4556_placed hA s0 s2 out pbA cap_dec ptsPtr x28_val pb.pts Frame
        hsp0_align hpts_le hpts_cap_lt hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2

/-- Placed helper for `+4544 -> +4548` (`bl` Block `271`): calls `drop_glue::<ProtoPolynomialEncoder>`
    with `x0 = pbA + 128#64`. -/
theorem v7_call_drop_proto_poly_encoder_4544_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (enc : ProtoPolynomialEncoder) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4544#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx0_1 : s1.readReg64 .x0 = pbA + 128#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4548#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        protoPolynomialEncoderAt A (pbA + 128#64) enc ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 128#64) 56 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdrop := v7_sub_ok_drop_proto_poly_encoder_mem_placed hA hcl1
  simp only [withMemEq, dropProtoPolyEncoderSpec] at hdrop
  refine SepWP.weaken_pre
    (sepConj_mono_left (v7_stackAt_encoderFromPbStack_to_dropStack48 (s0.sp - 2400#64))) ?_
  dsimp only [protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
  change s1.pc = (blkPl_333).base + 4544#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4548#64) s1 _ _
  wp_steps
  wp_apply
  refine EncoderFromPb.align_pre ?_ ?_
  · have hst := v7_stackAt_dropStack48_to_encoderFromPbStack (s0.sp - 2400#64)
    have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
    rw [haddr] at hst
    nth_rw 1 [← hsp1] at hst
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt s1.sp dropStack48 ∗ memRegion (s0.sp - 7552#64) 1008) ∗
        (memRegion (pbA + 128#64) 56 ∗ A.pool ∗ Frame) by ac_rfl)) ?_
    exact sepConj_mono_left hst
  · wp_done

/-- Placed cleanup at `+4528 -> +4632`:
drops `optEnc` at `pbA + 128#64` and `optDec` at `pbA + 184#64`, preserving `x28`. -/
theorem v7_cleanup_4528_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder)
    (optDec : Option ProtoPolynomialDecoder)
    (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4528#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 128#64) 56 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 4548#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
      A.pool ∗
      (memRegion (pbA + 128#64) 56 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = x28_val ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · cases optEnc with
    | none =>
      rw [optProtoPolynomialEncoderAt_none']
      dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 4528#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4548#64) s1 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hm := optProtoPolyEncoder_none_entails_memRegion_56 (pbA + 128#64)
        dsimp only [noneCap] at hm
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 128#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion ((pbA + 128#64) + 8#64) 48) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
             A.pool ∗ Frame) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
      · wp_done
    | some enc =>
      rw [optProtoPolynomialEncoderAt_some']
      refine SepWP.weaken_pre
        (v7_expose_some_protoPolyEncoder_pre A (s0.sp - 2400#64) pbA enc
          (((pbA + 184#64) ↦₆₄ cap_dec) ∗
           v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) Frame) ?_
      apply ProofLib.SepWP.exists_left; intro cap_enc
      apply ProofLib.SepWP.exists_left; intro ptr_enc
      apply ProofLib.SepWP.pure_elim; intro hcap_enc
      refine seq_clean_lscl hcl1
        (mid := lsmpl.base 333 + 4544#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          protoPolynomialEncoderAt A (pbA + 128#64) enc ∗
          A.pool ∗
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = pbA + 128#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = x28_val ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · have hne := cap_add_one_beq_zero_false hcap_enc
        change s1.pc = (blkPl_333).base + 4528#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4544#64) s1 _ _
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hunexp := protoPolynomialEncoderAt_unexpose_cap A (pbA + 128#64) cap_enc ptr_enc enc
          refine Entails.trans
            (Entails.of_eq (show _ =
              (((pbA + 128#64) ↦₆₄ cap_enc) ∗
               protoPolynomialEncoderRestAt A (pbA + 128#64) cap_enc ptr_enc enc) ∗
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               A.pool ∗
               ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
                 v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame)) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hunexp) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
        have hcall := v7_call_drop_proto_poly_encoder_4544_placed hA s0 s2 out pbA cap_dec x28_val enc
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hcl2 hsp0_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
        refine SepWP.mono hcall ?_
        intro sf Pf _ _ ⟨hPf, hrest⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hrest⟩
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    have h4548 := v7_cleanup_opt_decoder_4548_placed hA s0 s2 out pbA cap_dec x28_val optDec
      (memRegion (pbA + 128#64) 56 ∗ Frame)
      hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
    refine SepWP.mono h4548 ?_
    intro sf Pf _ _ ⟨hPf, hrest⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hrest⟩

/-- Placed cleanup at `+5444 -> +4632`:
executes `lsr x23, x28, #8`, drops `optEnc` at `pbA + 128#64` and `optDec` at `pbA + 184#64`,
preserving `x28`. -/
theorem v7_cleanup_5444_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder)
    (optDec : Option ProtoPolynomialDecoder)
    (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5444#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 128#64) 56 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 4548#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
      A.pool ∗
      (memRegion (pbA + 128#64) 56 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = x28_val ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · cases optEnc with
    | none =>
      rw [optProtoPolynomialEncoderAt_none']
      dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 5444#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4548#64) s1 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hm := optProtoPolyEncoder_none_entails_memRegion_56 (pbA + 128#64)
        dsimp only [noneCap] at hm
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 128#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion ((pbA + 128#64) + 8#64) 48) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
             A.pool ∗ Frame) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
      · wp_done
    | some enc =>
      rw [optProtoPolynomialEncoderAt_some']
      refine SepWP.weaken_pre
        (v7_expose_some_protoPolyEncoder_pre A (s0.sp - 2400#64) pbA enc
          (((pbA + 184#64) ↦₆₄ cap_dec) ∗
           v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) Frame) ?_
      apply ProofLib.SepWP.exists_left; intro cap_enc
      apply ProofLib.SepWP.exists_left; intro ptr_enc
      apply ProofLib.SepWP.pure_elim; intro hcap_enc
      refine seq_clean_lscl hcl1
        (mid := lsmpl.base 333 + 4544#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          protoPolynomialEncoderAt A (pbA + 128#64) enc ∗
          A.pool ∗
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = pbA + 128#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = x28_val ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · have hne := cap_add_one_beq_zero_false hcap_enc
        change s1.pc = (blkPl_333).base + 5444#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4544#64) s1 _ _
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hunexp := protoPolynomialEncoderAt_unexpose_cap A (pbA + 128#64) cap_enc ptr_enc enc
          refine Entails.trans
            (Entails.of_eq (show _ =
              (((pbA + 128#64) ↦₆₄ cap_enc) ∗
               protoPolynomialEncoderRestAt A (pbA + 128#64) cap_enc ptr_enc enc) ∗
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               A.pool ∗
               ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
                 v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame)) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hunexp) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
        have hcall := v7_call_drop_proto_poly_encoder_4544_placed hA s0 s2 out pbA cap_dec x28_val enc
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hcl2 hsp0_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
        refine SepWP.mono hcall ?_
        intro sf Pf _ _ ⟨hPf, hrest⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hrest⟩
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    have h4548 := v7_cleanup_opt_decoder_4548_placed hA s0 s2 out pbA cap_dec x28_val optDec
      (memRegion (pbA + 128#64) 56 ∗ Frame)
      hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
    refine SepWP.mono h4548 ?_
    intro sf Pf _ _ ⟨hPf, hrest⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hrest⟩

/-! ## 2. Cleanup at `+11112 -> +4632` and `+11096 -> +4632` (`<PolyDecoder>::from_pb = Err`) -/

/-- Placed step `+11112 -> +4632` (`mov w28, wzr; b +4632`): sets `x28 = 0#64`
and jumps to `+4632`. -/
theorem v7_cleanup_11112_placed
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 11112#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      Rest
      (fun sm Pm =>
        (Pm ⊢ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  change s1.pc = (blkPl_333).base + 11112#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4632#64) s1 _ _
  wp_steps
  wp_done

/-- Placed cleanup at `+11096 -> +4632`:
drops `polyEncoderAt A (fsp + 1392) enc` (Block `272`), drops `unchunkedCt1SentAt A (fsp + 1264) uc`
(Block `279`), sets `x28 = 0#64`, and jumps to `+4632`. -/
theorem v7_cleanup_11096_placed
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out : BitVec 64)
    (enc : PolyEncoder) (uc : LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11096#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        unchunkedCt1SentAt A ((s0.sp - 2400#64) + 1264#64) uc ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdrop_enc := v7_sub_ok_drop_poly_encoder_local2_mem_placed hA hcl1
  simp only [withMemEq, dropGluePolyEncoderSpec, dropGluePoly16Stack] at hdrop_enc
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 11112#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
      memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
      A.pool ∗
      Frame)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · refine SepWP.weaken_pre
      (sepConj_mono_left (v7_stackAt_encoderFromPbStack_to_dropStack32 (s0.sp - 2400#64))) ?_
    have h1392 : (s0.sp - 2400#64) + 1392#64 = s0.sp - 1008#64 := by bv_omega
    have h1264 : (s0.sp - 2400#64) + 1264#64 = s0.sp - 1136#64 := by bv_omega
    have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
    rw [h1392, h1264, h7552]
    dsimp only [polyEncoderSize, BitVec.ofNat_eq_ofNat] at hdrop_enc hpc1 ⊢
    refine seq_clean_lscl hcl1 (mid := lsmpl.base 333 + 11104#64)
      (P_mid :=
        (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
        memRegion (s0.sp - 1008#64) 400 ∗
        unchunkedCt1SentAt A (s0.sp - 1136#64) uc ∗
        A.pool ∗
        Frame)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 11096#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 11104#64) s1 _ _
      wp_steps
      wp_apply
      refine Drop.align_pre (by rw [hsp1]; ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
      clear hdrop_enc
      have hdrop_uc := v7_sub_ok_drop_unchunked_ct1_sent_local2_mem_placed (F := F) hA hcl2
      simp only [withMemEq, dropUnchunkedCt1SentSpec] at hdrop_uc
      dsimp only [unchunkedCt1SentSize, BitVec.ofNat_eq_ofNat] at hdrop_uc ⊢
      rcases uc with ⟨epoch, ⟨rootKey, macKey⟩, hdr, es, ct1⟩
      change s2.pc = (blkPl_333).base + 11104#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 11112#64) s2 _ _
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v7_stackAt_dropStack32_to_encoderFromPbStack (s0.sp - 2400#64)
        rw [h7552] at hst
        rw [hsp2]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
            (memRegion (s0.sp - 1008#64) 400 ∗
             memRegion (s0.sp - 1136#64) 128 ∗
             A.pool ∗ Frame) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    exact v7_cleanup_11112_placed s0 s2 out _ hpc2 hrun2 hsp2 hx19_2 htr2

end CryptoVerification.SpqrV1.States.FromPb
