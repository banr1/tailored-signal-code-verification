/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7c
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part C

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant7c.lean`.
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

variable [LibsignalPlacement]

/-! ## 1. Cleanup at `+7100..+7208 -> +4632` and `+3732..+3740 -> +7104/+7116` -/

/-- Placed step `+7196 -> +4632`:
sets `x28 = 0#64` and deallocates `optDec` at `pbA + 184#64` if `some`. -/
theorem v7_cleanup_7196_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7196#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
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
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  cases optDec with
  | none =>
    unfold v7_optDecoderCapProp at hcap_dec
    subst hcap_dec
    unfold v7_optProtoPolyDecoderTail
    dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx22_1 ⊢
    change s1.pc = (blkPl_333).base + 7196#64 at hpc1
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
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
      change s1.pc = (blkPl_333).base + 7196#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4556#64) s1 _ _
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
      exact v7_proto_decoder_dealloc_4556_placed hA s0 s2 out pbA cap_dec ptsPtr 0#64 pb.pts Frame
        hsp0_align hpts_le hpts_cap_lt hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2

/-- Placed deallocation of the 4 `Vec<u8>` buffers `c2/p2 .. c5/p5` at `+7116 -> +7196`. -/
theorem v7_dealloc_4vecs_7116_to_7196_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7116#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7196#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A c2 p2 ∗
        vecCapPtrDealloc A c3 p3 ∗
        vecCapPtrDealloc A c4 p4 ∗
        vecCapPtrDealloc A c5 p5 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v4_sub_ok_dealloc_125316_placed (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  unfold v7_ct1SentSpillCells
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  have h1296 : (s0.sp - 2400#64) + 1296#64 = s0.sp - 1104#64 := by bv_omega
  have h1312 : (s0.sp - 2400#64) + 1312#64 = s0.sp - 1088#64 := by bv_omega
  have h1320 : (s0.sp - 2400#64) + 1320#64 = s0.sp - 1080#64 := by bv_omega
  have h1336 : (s0.sp - 2400#64) + 1336#64 = s0.sp - 1064#64 := by bv_omega
  have h1344 : (s0.sp - 2400#64) + 1344#64 = s0.sp - 1056#64 := by bv_omega
  have h1360 : (s0.sp - 2400#64) + 1360#64 = s0.sp - 1040#64 := by bv_omega
  have h1368 : (s0.sp - 2400#64) + 1368#64 = s0.sp - 1032#64 := by bv_omega
  rw [h7552, h1296, h1312, h1320, h1336, h1344, h1360, h1368]
  dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 7136#64)
    (P_mid := (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c3 == 0#64) = true then emp else A.live p3 c3.toNat 1 ∗ memRegion p3 c3.toNat) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool ∗ Frame)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s1.pc = (blkPl_333).base + 7116#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7136#64) s1 _ _
    by_cases hc2 : (c2 == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp1]; ac_rfl) ?_; wp_done
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, htr2⟩
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 7156#64)
    (P_mid := (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool ∗ Frame)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s2.pc = (blkPl_333).base + 7136#64 at hpc2
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7156#64) s2 _ _
    by_cases hc3 : (c3 == 0#64) = true <;>
      simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp2]; ac_rfl) ?_; wp_done
  intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 7176#64)
    (P_mid := (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool ∗ Frame)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s3.pc = (blkPl_333).base + 7156#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7176#64) s3 _ _
    by_cases hc4 : (c4 == 0#64) = true <;>
      simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp3]; ac_rfl) ?_; wp_done
  intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx22_4, hx27_4, htr4⟩
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  change s4.pc = (blkPl_333).base + 7176#64 at hpc4
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 7196#64) s4 _ _
  by_cases hc5 : (c5 == 0#64) = true <;>
    simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · exact sepConj_mono_left hst
    · wp_done
  · wp_steps
    wp_apply
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp4]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          ((((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
            ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
            ((s0.sp - 1032#64) ↦₆₄ p5)) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

/-- Placed deallocation of `c1/p1` at `+7104 -> +7116` when `(c1 == 0#64) = false`. -/
theorem v7_dealloc_c1_7104_to_7116_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 : BitVec 64)
    (Frame : SepProp)
    (hc1 : ¬((c1 == 0#64) = true))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7104#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7116#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecCapPtrDealloc A c1 p1 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v4_sub_ok_dealloc_125316_placed (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  rw [h7552]
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  simp only [hc1, ↓reduceIte]
  change s1.pc = (blkPl_333).base + 7104#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 7116#64) s1 _ _
  wp_steps
  wp_apply
  refine EncoderFromPb.align_pre ?_ ?_
  · rw [hsp1]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
        (A.pool ∗ Frame) by ac_rfl)) ?_
    exact sepConj_mono_left hst
  · wp_done

/-- Placed cleanup at `+7100 -> +4632` (when `s.sendingCt1 = none`):
deallocates `c1/p1 .. c5/p5` and `optDec` (if `some`), sets `x28 = 0#64`, and reaches `+4632`. -/
theorem v7_cleanup_7100_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        vecCapPtrDealloc A c3 p3 ∗
        vecCapPtrDealloc A c4 p4 ∗
        vecCapPtrDealloc A c5 p5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 7116#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      A.pool ∗
      (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       vecCapPtrDealloc A c2 p2 ∗
       vecCapPtrDealloc A c3 p3 ∗
       vecCapPtrDealloc A c4 p4 ∗
       vecCapPtrDealloc A c5 p5 ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
       Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x27 = pbA ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc1 : (c1 == 0#64) = true
    · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      simp only [hc1, ↓reduceIte, emp_sepConj]
      change s1.pc = (blkPl_333).base + 7100#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 7116#64) s1 _ _
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    · refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 7104#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          vecCapPtrDealloc A c1 p1 ∗
          A.pool ∗
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A c2 p2 ∗
           vecCapPtrDealloc A c3 p3 ∗
           vecCapPtrDealloc A c4 p4 ∗
           vecCapPtrDealloc A c5 p5 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
           Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x1 = c1 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x24 = c2 ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = p1 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s1.pc = (blkPl_333).base + 7100#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7104#64) s1 _ _
        wp_steps
        refine Drop.align_pre (by ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx1_2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
        exact v7_dealloc_c1_7104_to_7116_placed hA s0 s2 out pbA cap_dec c1 p1 c2 _
          hc1 hsp0_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx22_2 hx24_2 hx27_2 hx28_2 htr2
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx24_2, hx27_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 7196#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        A.pool ∗
        ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (v7_dealloc_4vecs_7116_to_7196_placed hA s0 s2 out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx24_2 hx27_2 htr2)
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
      refine SepWP.weaken_pre ?_
        (SepWP.mono
          (v7_cleanup_7196_placed hA s0 s3 out pbA cap_dec optDec
            (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗ Frame)
            hcap_dec hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 hx27_3 htr3)
          (fun _ _ _ _ ⟨hPm, hq⟩ => ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩))
      exact Entails.of_eq (by ac_rfl)

/-- Placed cleanup at `+3732 -> +4632` (when `<PolyEncoder>::from_pb = Err`):
loads `c1` from `[sp, #0x18]`, deallocates `c1/p1 .. c5/p5` and `optDec` (if `some`),
sets `x28 = 0#64`, and reaches `+4632`. -/
theorem v7_cleanup_3732_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3732#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        vecCapPtrDealloc A c3 p3 ∗
        vecCapPtrDealloc A c4 p4 ∗
        vecCapPtrDealloc A c5 p5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have h24 : (s0.sp - 2400#64) + 24#64 = s0.sp - 2376#64 := by bv_omega
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 7116#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      A.pool ∗
      (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       vecCapPtrDealloc A c2 p2 ∗
       vecCapPtrDealloc A c3 p3 ∗
       vecCapPtrDealloc A c4 p4 ∗
       vecCapPtrDealloc A c5 p5 ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
       ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame)))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x27 = pbA ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc1 : (c1 == 0#64) = true
    · rw [h24]
      dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      simp only [hc1, Bool.true_eq_false, ↓reduceIte, emp_sepConj]
      change s1.pc = (blkPl_333).base + 3732#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 7116#64) s1 _ _
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    · refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 7104#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          vecCapPtrDealloc A c1 p1 ∗
          A.pool ∗
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A c2 p2 ∗
           vecCapPtrDealloc A c3 p3 ∗
           vecCapPtrDealloc A c4 p4 ∗
           vecCapPtrDealloc A c5 p5 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
           ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame)))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x1 = c1 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x24 = c2 ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = p1 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rw [h24]
        change s1.pc = (blkPl_333).base + 3732#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7104#64) s1 _ _
        wp_steps
        refine Drop.align_pre (by ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx1_2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
        exact v7_dealloc_c1_7104_to_7116_placed hA s0 s2 out pbA cap_dec c1 p1 c2 _
          hc1 hsp0_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx22_2 hx24_2 hx27_2 hx28_2 htr2
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx24_2, hx27_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 7196#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        A.pool ∗
        ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
         ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame)))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (v7_dealloc_4vecs_7116_to_7196_placed hA s0 s2 out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
           ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame))
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx24_2 hx27_2 htr2)
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
      refine SepWP.weaken_pre ?_
        (SepWP.mono
          (v7_cleanup_7196_placed hA s0 s3 out pbA cap_dec optDec
            (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
             ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame))
            hcap_dec hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 hx27_3 htr3)
          (fun _ _ _ _ ⟨hPm, hq⟩ => ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩))
      exact Entails.of_eq (by ac_rfl)

/-! ## 2. Cleanup at `+10556..+10672 -> +11112 -> +4632` (`s.receivingEk = none`) -/

/-- Placed step `+10556 -> +10568`: drops `[Poly; 16]` at `(s0.sp - 2400#64) + 1400#64` via Block `265`
and combines with the tag and tail to leave `memRegion ((s0.sp - 2400#64) + 1392#64) 400`. -/
theorem v7_drop_poly16_10556_to_10568_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out c2 : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10556#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10568#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x24 = c2 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdrop := v7_sub_ok_drop_poly16_mem_placed hA hcl1
  simp only [withMemEq, dropGluePoly16Spec, dropGluePoly16Stack] at hdrop
  refine SepWP.weaken_pre (v7_drop_poly16_pre A (s0.sp - 2400#64) enc Frame) ?_
  apply ProofLib.SepWP.exists_left; intro tag
  apply ProofLib.SepWP.exists_left; intro vecs
  apply ProofLib.SepWP.pure_elim; intro hvecs_len
  have h1392 : (s0.sp - 2400#64) + 1392#64 = s0.sp - 1008#64 := by bv_omega
  have h1400 : (s0.sp - 1008#64) + 8#64 = s0.sp - 1000#64 := by bv_omega
  have h1784 : (s0.sp - 1008#64) + 392#64 = s0.sp - 616#64 := by bv_omega
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  rw [h1392, h1400, h1784, h7552]
  dsimp only [polyArrayBytes, BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
  change s1.pc = (blkPl_333).base + 10556#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10568#64) s1 _ _
  wp_steps
  wp_apply
  refine EncoderFromPb.align_pre ?_ ?_
  · have hst := v7_stackAt_dropStack32_to_encoderFromPbStack (s0.sp - 2400#64)
    have hjoin := v7_polyEncoder_1392_join (s0.sp - 2400#64) tag
    have h1400' : (s0.sp - 2400#64) + 1400#64 = s0.sp - 1000#64 := by bv_omega
    have h1784' : (s0.sp - 2400#64) + 1784#64 = s0.sp - 616#64 := by bv_omega
    rw [h7552] at hst
    rw [h1392, h1400', h1784'] at hjoin
    rw [hsp1]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
        ((((s0.sp - 1008#64) ↦₆₄ tag) ∗
          memRegion (s0.sp - 1000#64) 384 ∗
          memRegion (s0.sp - 616#64) 8) ∗
         (A.pool ∗ Frame)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hst (sepConj_mono_left hjoin)) (Entails.of_eq (by ac_rfl))
  · wp_done

/-- Placed deallocation of `c1/p1` at `+10568 -> +10588`. -/
theorem v7_dealloc_c1_10568_to_10588_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out c1 p1 c2 : BitVec 64)
    (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10568#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10588#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        vecCapPtrDealloc A c1 p1 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x24 = c2 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v4_sub_ok_dealloc_125316_placed (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  have h24 : (s0.sp - 2400#64) + 24#64 = s0.sp - 2376#64 := by bv_omega
  rw [h7552, h200, h24]
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  change s1.pc = (blkPl_333).base + 10568#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10588#64) s1 _ _
  by_cases hc1 : (c1 == 0#64) = true <;>
    simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · exact sepConj_mono_left hst
    · wp_done
  · wp_steps
    wp_apply
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          (((s0.sp - 2200#64) ↦₆₄ p1) ∗ ((s0.sp - 2376#64) ↦₆₄ c1) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

/-- Placed deallocation of the 4 `Vec<u8>` buffers `c2/p2 .. c5/p5` at `+10588 -> +11112`. -/
theorem v7_dealloc_4vecs_10588_to_11112_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10588#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11112#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A c2 p2 ∗
        vecCapPtrDealloc A c3 p3 ∗
        vecCapPtrDealloc A c4 p4 ∗
        vecCapPtrDealloc A c5 p5 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v4_sub_ok_dealloc_125316_placed (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  unfold v7_ct1SentSpillCells
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  have h1296 : (s0.sp - 2400#64) + 1296#64 = s0.sp - 1104#64 := by bv_omega
  have h1312 : (s0.sp - 2400#64) + 1312#64 = s0.sp - 1088#64 := by bv_omega
  have h1320 : (s0.sp - 2400#64) + 1320#64 = s0.sp - 1080#64 := by bv_omega
  have h1336 : (s0.sp - 2400#64) + 1336#64 = s0.sp - 1064#64 := by bv_omega
  have h1344 : (s0.sp - 2400#64) + 1344#64 = s0.sp - 1056#64 := by bv_omega
  have h1360 : (s0.sp - 2400#64) + 1360#64 = s0.sp - 1040#64 := by bv_omega
  have h1368 : (s0.sp - 2400#64) + 1368#64 = s0.sp - 1032#64 := by bv_omega
  rw [h7552, h1296, h1312, h1320, h1336, h1344, h1360, h1368]
  dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 10608#64)
    (P_mid := (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c3 == 0#64) = true then emp else A.live p3 c3.toNat 1 ∗ memRegion p3 c3.toNat) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool ∗ Frame)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s1.pc = (blkPl_333).base + 10588#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10608#64) s1 _ _
    by_cases hc2 : (c2 == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp1]; ac_rfl) ?_; wp_done
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 10628#64)
    (P_mid := (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool ∗ Frame)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s2.pc = (blkPl_333).base + 10608#64 at hpc2
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10628#64) s2 _ _
    by_cases hc3 : (c3 == 0#64) = true <;>
      simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp2]; ac_rfl) ?_; wp_done
  intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, htr3⟩
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 10648#64)
    (P_mid := (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool ∗ Frame)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s3.pc = (blkPl_333).base + 10628#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10648#64) s3 _ _
    by_cases hc4 : (c4 == 0#64) = true <;>
      simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp3]; ac_rfl) ?_; wp_done
  intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, htr4⟩
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  change s4.pc = (blkPl_333).base + 10648#64 at hpc4
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 11112#64) s4 _ _
  by_cases hc5 : (c5 == 0#64) = true <;>
    simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · exact sepConj_mono_left hst
    · wp_done
  · wp_steps
    wp_apply
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp4]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          ((((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
            ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
            ((s0.sp - 1032#64) ↦₆₄ p5)) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

/-- Placed cleanup at `+10556 -> +4632` (when `s.receivingEk = none`):
drops `enc` at `fsp + 1392..1792`, deallocates `c1/p1 .. c5/p5`, sets `x28 = 0#64` at `+11112`,
and branches to `+4632`. -/
theorem v7_cleanup_10556_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10556#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        vecCapPtrDealloc A c3 p3 ∗
        vecCapPtrDealloc A c4 p4 ∗
        vecCapPtrDealloc A c5 p5 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 10568#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
      A.pool ∗
      ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       vecCapPtrDealloc A c1 p1 ∗
       vecCapPtrDealloc A c2 p2 ∗
       vecCapPtrDealloc A c3 p3 ∗
       vecCapPtrDealloc A c4 p4 ∗
       vecCapPtrDealloc A c5 p5 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x24 = c2 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (v7_drop_poly16_10556_to_10568_placed hA s0 s1 out c2 enc
        ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
         (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
         v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
         vecCapPtrDealloc A c1 p1 ∗
         vecCapPtrDealloc A c2 p2 ∗
         vecCapPtrDealloc A c3 p3 ∗
         vecCapPtrDealloc A c4 p4 ∗
         vecCapPtrDealloc A c5 p5 ∗ Frame)
        hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx24_1 htr1)
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx24_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 10588#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        A.pool ∗
        (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
         vecCapPtrDealloc A c2 p2 ∗
         vecCapPtrDealloc A c3 p3 ∗
         vecCapPtrDealloc A c4 p4 ∗
         vecCapPtrDealloc A c5 p5 ∗
         memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x24 = c2 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (v7_dealloc_c1_10568_to_10588_placed hA s0 s2 out c1 p1 c2
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A c2 p2 ∗
           vecCapPtrDealloc A c3 p3 ∗
           vecCapPtrDealloc A c4 p4 ∗
           vecCapPtrDealloc A c5 p5 ∗
           memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame)
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx24_2 htr2)
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx24_3, htr3⟩
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 11112#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
           (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
           memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (v7_dealloc_4vecs_10588_to_11112_placed hA s0 s3 out c2 p2 c3 p3 c4 p4 c5 p5
            ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
             (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
             memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame)
            hsp0_align hpc3 hrun3 hsp3 hx19_3 hx24_3 htr3)
      · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, htr4⟩
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) ?_
        exact SepWP.mono
          (v7_cleanup_11112_placed s0 s4 out _ hpc4 hrun4 hsp4 hx19_4 htr4)
          (fun _ _ _ _ ⟨hPm, hq⟩ => ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩)

end CryptoVerification.SpqrV1.States.FromPb
