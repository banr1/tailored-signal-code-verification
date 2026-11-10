/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 8 (`EkReceivedCt1Sampled`, `+1764`, Block `333`) — Part A

Relocatable (`Obj.MultiPlacedLib`) error exits (`+4240`, `+4216`, `+4212`) and `uc` / `sendingCt1`
cleanup paths (`+2208`, `+2148`, `+2100`, `+10544 -> s0.x30`) for Variant 8.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlaced

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
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v8_bv_sub_sub_lit v8_bv_add_add_lit

/-! ## 1. Error Exit at `+4240` and `sendingCt1` Drop at `+4216` / `+4212` -/

/-- Shared `Err(StateDecode)` exit at `+4240` (`lsmpl.base 333 + 4240 -> +60 -> s0.x30`):
when `x20` has low byte `spqrErrorByte .stateDecode` (`0#8`) and `x19 = out`,
sets `x8 = noneCap`, writes `x20` to `[out + 8]`, `x8, x28` to `[out + 16..32]`, and branches to `+60`. -/
theorem v8_err_4240_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4240#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : (s1.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
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
    (mid := lsmpl.base 333 + 60#64)
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
  · change s1.pc = (blkPl_333).base + 4240#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 60#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htail := out_8_32_entails_err_tail out (s1.readReg64 .x20)
        noneCap (s1.readReg64 .x28)
      rw [hx20_1] at htail
      dsimp only [noneCap] at htail ⊢
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ s1.readReg64 .x20) ∗
           ((out + 16#64) ↦₆₄ 18446744073709551615#64) ∗
           ((out + 24#64) ↦₆₄ s1.readReg64 .x28) ∗
           memRegion (out + 32#64) 896) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60_placed (A := A) (F := F) (ext := ext) s0 s2 out .stateDecode v0 Rest
      hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

/-- Drop `Option<ProtoPolynomialEncoder>` at `fsp + 1520` (`s0.sp - 880`) and return
`Err(StateDecode)` (`+4216 -> +4240 -> s0.x30`). -/
theorem v8_drop_sendingCt1_4216_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4216#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : (s1.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1520 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
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
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hex)))) ?_
  wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
  apply SepWP.pure_elim; intro hw0_cond
  have hmerge := v8_merge_stack_1520_56_728 (s0.sp - 2400#64)
  cases optEnc with
  | none =>
    subst hw0_cond
    dsimp only [v1_optProtoPolyEncoderHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 4240#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (A.pool ∗ Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        (sm.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 4216#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4240#64) s1 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hw_mem := v1_optProtoPolyEncoderWordsAt_entails_56
          (s0.sp - 2400#64 + 1520#64) 18446744073709551615#64 w8 w16 w24 w32 w40 w48
        dsimp only [v1_optProtoPolyEncoderWordsAt] at hw_mem
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 1520 ∗
           (((s0.sp - 2400#64 + 1520#64) ↦₆₄ 18446744073709551615#64) ∗
            ((s0.sp - 2400#64 + 1520#64 + 8#64) ↦₆₄ w8) ∗
            ((s0.sp - 2400#64 + 1520#64 + 16#64) ↦₆₄ w16) ∗
            ((s0.sp - 2400#64 + 1520#64 + 24#64) ↦₆₄ w24) ∗
            ((s0.sp - 2400#64 + 1520#64 + 32#64) ↦₆₄ w32) ∗
            ((s0.sp - 2400#64 + 1520#64 + 40#64) ↦₆₄ w40) ∗
            ((s0.sp - 2400#64 + 1520#64 + 48#64) ↦₆₄ w48)) ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hw_mem))) ?_
        exact Entails.trans (sepConj_mono_left hmerge) (Entails.of_eq (by ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, htr2⟩
      have herr := v8_err_4240_placed (A := A) (F := F) (ext := ext) s0 s2 out (A.pool ∗ Rest)
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 htr2
      refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩
  | some pbEnc =>
    have hpack := v1_optProtoPolyEncoderAt_pack_some A (s0.sp - 2400#64 + 1520#64) pbEnc
      w0 w8 w16 w24 w32 w40 w48
    have hne := cap_add_one_beq_zero_false hw0_cond
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have h880 : s0.sp - 2400#64 + 1520#64 = s0.sp - 880#64 := by bv_omega
    refine seq_clean_lscl hcl1
      (mid := lsmpl.base 333 + 4236#64)
      (P_mid :=
        protoPolynomialEncoderAt A (s0.sp - 880#64) pbEnc ∗
        A.pool ∗
        stackAt (s0.sp - 2400#64) dropStack48 ∗
        (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
         memRegion (s0.sp - 2400#64) 1520 ∗
         memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = s0.sp - 880#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = s1.readReg64 .x20 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 4216#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4236#64) s1 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), ← h880]
        refine Entails.trans (Entails.of_eq (show _ =
          (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48) ∗
          (A.pool ∗ stackAt (s0.sp - 2400#64) dropStack48 ∗
           (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
            memRegion (s0.sp - 2400#64) 1520 ∗
            memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by
            dsimp only [v1_optProtoPolyEncoderWordsAt]; ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hpack) (Entails.of_eq (by ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx19_2, hx20_2, htr2⟩
      have hdrop := v1_drop_glue_proto_poly_encoder_mem_ok_at_statesFromPb_placed hA hcl2
      simp only [withMemEq, dropProtoPolyEncoderSpec] at hdrop
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 4240#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          (A.pool ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          (sm.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 4236#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4240#64) s2 _ _
        wp_steps
        wp_call hdrop ⟨s0.sp - 880#64, pbEnc⟩
        refine EncoderFromPb.align_pre ?_ ?_
        · have h7552 : s0.sp - 2400#64 - 5152#64 = s0.sp - 7552#64 := by bv_omega
          rw [v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), h7552, ← h880, hsp2]
          dsimp only [protoPolynomialEncoderSize]
          simp only [arm64_norm] at hmerge ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 1520 ∗
             memRegion (s0.sp - 880#64) 56 ∗
             memRegion (s0.sp - 824#64) 728) ∗
            (memRegion (s0.sp - 7552#64) 1008 ∗
             stackAt (s0.sp - 2400#64) dropStack48 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hmerge) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx20_3, htr3⟩
        have herr := v8_err_4240_placed (A := A) (F := F) (ext := ext) s0 s3 out (A.pool ∗ Rest)
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 htr3
        refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-- Error exit at `+4212` (`lsmpl.base 333 + 4212 -> +4216 -> s0.x30`): sets `x20 = 0`, drops `sendingCt1`, and returns `Err(StateDecode)`. -/
theorem v8_drop_sendingCt1_4212_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4212#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1520 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
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
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 4216#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1520 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [spqrErrorByte, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 4212#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4216#64) s1 _ _
    wp_steps; wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, htr2⟩
    exact v8_drop_sendingCt1_4216_placed (A := A) (F := F) hA s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48 Rest hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 htr2

/-! ## 2. Error Cleanup for `uc` (`es`, `ek`, `ct1`, `auth`) + `sendingCt1` (`+2100 -> +2148 -> +2208 -> +4216`) -/

/-- Error transition `+2208 -> +4216 -> s0.x30`: sets `x20 = 0`, drops `sendingCt1` at `fsp + 1520`,
and returns `Err(StateDecode)`. -/
theorem v8_drop_sendingCt1_2208_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2208#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1520 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
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
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 4216#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1520 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [spqrErrorByte, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 2208#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4216#64) s1 _ _
    wp_steps; wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, htr2⟩
    exact v8_drop_sendingCt1_4216_placed (A := A) (F := F) hA s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48 Rest hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 htr2

/-- Cleanup `es` (`x26 = u8`, `[fsp+904] = u16`), `ek` (`[fsp+920] = u32`, `[fsp+928] = u40`),
`ct1` (`[fsp+944] = u56`, `[fsp+952] = u64`), and `sendingCt1` at `fsp + 1520..1576`,
returning `Err(StateDecode)` (`+2148 -> +2208 -> +4216 -> s0.x30`). -/
theorem v8_drop_uc_and_sendingCt1_2148_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2148#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u8 u16 ∗
        vecCapPtrDealloc A u32 u40 ∗
        vecCapPtrDealloc A u56 u64 ∗
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
  have hdealloc := v1_dealloc_ok_at_statesFromPb_placed hA
  simp only [rustDeallocSpec] at hdealloc
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 2168#64)
    (P_mid :=
      memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      memRegion (s0.sp - 2400#64) 896 ∗
      v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
      memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      vecCapPtrDealloc A u32 u40 ∗
      vecCapPtrDealloc A u56 u64 ∗
      A.pool ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [v8_ucWordsAt, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
    change s1.pc = (blkPl_333).base + 2148#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 2168#64) s1 _ _
    by_cases hc1 : (u8 == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply
      refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
    refine seq_clean_lscl hcl2
      (mid := lsmpl.base 333 + 2188#64)
      (P_mid :=
        memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
        stackAt (s0.sp - 2400#64) allocHookStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u56 u64 ∗
        A.pool ∗
        Rest)
      (Q := fun s3 =>
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        TraceCalleeSaved s3 s0)
      ?_ ?_
    · dsimp only [v8_ucWordsAt, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
      change s2.pc = (blkPl_333).base + 2168#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 2188#64) s2 _ _
      by_cases hc2 : (u32 == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply
        refine EncoderFromPb.align_pre (by rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, htr3⟩
      refine seq_clean_lscl hcl3
        (mid := lsmpl.base 333 + 2208#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 1520 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          A.pool ∗
          Rest)
        (Q := fun s4 =>
          s4.sp = s0.sp - 2400#64 ∧
          s4.readReg64 .x19 = out ∧
          TraceCalleeSaved s4 s0)
        ?_ ?_
      · dsimp only [v8_ucWordsAt, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc3 ⊢
        change s3.pc = (blkPl_333).base + 2188#64 at hpc3
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 2208#64) s3 _ _
        have hm := v8_merge_stack_896_128_496_1520 (s0.sp - 2400#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
        by_cases hc3 : (u56 == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine EncoderFromPb.align_pre ?_ ?_
          · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
            refine Entails.trans (Entails.of_eq (show _ =
              (memRegion (s0.sp - 2400#64) 896 ∗
               v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
                 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
               memRegion (s0.sp - 2400#64 + 1024#64) 496) ∗
              (memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
               stackAt (s0.sp - 2400#64) allocHookStack ∗
               v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
               v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
               memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by
                 dsimp only [v8_ucWordsAt]; simp only [arm64_norm]; ac_rfl)) ?_
            exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by simp only [arm64_norm]; ac_rfl))
          · wp_done
        · wp_steps; wp_apply
          refine EncoderFromPb.align_pre ?_ ?_
          · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp3]
            refine Entails.trans (Entails.of_eq (show _ =
              (memRegion (s0.sp - 2400#64) 896 ∗
               v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
                 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
               memRegion (s0.sp - 2400#64 + 1024#64) 496) ∗
              (memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
               stackAt (s0.sp - 2400#64) allocHookStack ∗
               v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
               v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
               memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by
                 dsimp only [v8_ucWordsAt]; simp only [arm64_norm]; ac_rfl)) ?_
            exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by simp only [arm64_norm]; ac_rfl))
          · wp_done
      · intro s4 hpc4 hrun4 hcl4 ⟨hsp4, hx19_4, htr4⟩
        exact v8_drop_sendingCt1_2208_placed (A := A) (F := F) hA s0 s4 out optEnc
          w0 w8 w16 w24 w32 w40 w48 Rest hcl4 hsp0_align hpc4 hrun4 hsp4 hx19_4 htr4

/-- Cleanup `optAuth` (`[fsp+968..1016] = u80..u120`), `es`, `ek`, `ct1`, and `sendingCt1`,
returning `Err(StateDecode)` (`+2100 -> +2148 -> +2208 -> +4216 -> s0.x30`). -/
theorem v8_drop_uc_and_sendingCt1_2100_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optAuth : Option ProtoAuthenticator)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2100#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx26_1 : s1.readReg64 .x26 = u8)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗
        v1_optProtoAuthHeap A optAuth u80 u88 u96 u104 u112 u120 ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  cases optAuth with
  | none =>
    dsimp only [v1_optProtoAuthHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; intro hu80; subst hu80
    refine seq_clean_lscl hcl1
      (mid := lsmpl.base 333 + 2148#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u128 ∗
        memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗
        A.pool ∗ Rest)
      (Q := fun s2 => s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x26 = u8 ∧ TraceCalleeSaved s2 s0)
      ?_ ?_
    · dsimp only [v8_ucWordsAt, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 2100#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 2148#64) s1 _ _
      wp_steps; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
      exact v8_drop_uc_and_sendingCt1_2148_placed (A := A) (F := F) hA s0 s2 out
        u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u128
        optEnc w0 w8 w16 w24 w32 w40 w48 Rest hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2
  | some auth =>
    dsimp only [v1_optProtoAuthHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; rintro ⟨hu80, _, _⟩
    have hcmn : (u80 + 1#64 == 0#64) = false :=
      Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hu80)
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
    have hdealloc := v1_dealloc_ok_at_statesFromPb_placed hA
    simp only [rustDeallocSpec] at hdealloc
    have hd_root := vecU8Payload_entails_dealloc A u80 u88 auth.rootKey
    have hd_mac := vecU8Payload_entails_dealloc A u104 u112 auth.macKey
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗
       v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
         u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
       memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗
       A.pool ∗ Rest) by ac_rfl))
      (sepConj_mono hd_root (sepConj_mono_left hd_mac))) ?_
    rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
    wp_simp_pre [sepConj_assoc]
    refine seq_clean_lscl hcl1
      (mid := lsmpl.base 333 + 2128#64)
      (P_mid :=
        vecCapPtrDealloc A u104 u112 ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
        stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64) 896 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗
        A.pool ∗ Rest)
      (Q := fun s2 => s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x26 = u8 ∧ TraceCalleeSaved s2 s0)
      ?_ ?_
    · dsimp only [v8_ucWordsAt, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      change s1.pc = (blkPl_333).base + 2100#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 2128#64) s1 _ _
      by_cases hc_r : (u80 == 0#64) = true <;>
        simp only [hc_r, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply
        refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
      refine seq_clean_lscl hcl2
        (mid := lsmpl.base 333 + 2148#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗
          A.pool ∗ Rest)
        (Q := fun s3 => s3.sp = s0.sp - 2400#64 ∧ s3.readReg64 .x19 = out ∧
          s3.readReg64 .x26 = u8 ∧ TraceCalleeSaved s3 s0)
        ?_ ?_
      · dsimp only [v8_ucWordsAt, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
        change s2.pc = (blkPl_333).base + 2128#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 2148#64) s2 _ _
        by_cases hc_m : (u104 == 0#64) = true <;>
          simp only [hc_m, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine EncoderFromPb.align_pre ?_ ?_
          · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
            simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
          · wp_done
        · wp_steps; wp_apply
          refine EncoderFromPb.align_pre ?_ ?_
          · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp2]
            simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)
          · wp_done
      · intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
        exact v8_drop_uc_and_sendingCt1_2148_placed (A := A) (F := F) hA s0 s3 out
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          optEnc w0 w8 w16 w24 w32 w40 w48 Rest hcl3 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3

/-! ## 3. Error Cleanup when `u.auth = none` (`+10544 -> +2208 -> +4216 -> s0.x30`) -/

/-- Error path at `+10544 -> +2208 -> +4216 -> s0.x30` when `u.auth = none`:
calls `lsmpl.base 286` (`drop_glue::<ProtoUnchunkedCt1SentEkReceived>`) on `fsp + 896`, then drops `sendingCt1`
and returns `Err(StateDecode)`. -/
theorem v8_drop_uc_auth_none_10544_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out : BitVec 64) (u : V1State.Unchunked.Ct1SentEkReceived)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u88 u96 u104 u112 u120 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63) (hu24 : u24 = (u.es.length : BitVec 64))
    (hu32 : u32.toNat < 2 ^ 63) (hu48 : u48 = (u.ek.length : BitVec 64))
    (hu56 : u56.toNat < 2 ^ 63) (hu72 : u72 = (u.ct1.length : BitVec 64))
    (hauth : u.auth = none)
    (hpc1 : s1.pc = lsmpl.base 333 + 10544#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u.epoch ∗
        memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A u8 u16 u.es ∗
        vecU8Payload A u32 u40 u.ek ∗
        vecU8Payload A u56 u64 u.ct1 ∗
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
  have hdrop := v9_sub_ok_drop_proto_unchunked_ct1_sent_mem_placed hA hcl1
  simp only [withMemEq, dropProtoUnchunkedCt1SentEkReceivedSpec] at hdrop
  have hpack := v8_pack_protoUnchunkedCt1SentEkReceived_auth_none A (s0.sp - 2400#64 + 896#64) u
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u88 u96 u104 u112 u120 hu8 hu24 hu32 hu48 hu56 hu72 hauth
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    (v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
       u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u.epoch ∗
     vecU8Payload A u8 u16 u.es ∗
     vecU8Payload A u32 u40 u.ek ∗
     vecU8Payload A u56 u64 u.ct1) ∗
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     memRegion (s0.sp - 2400#64) 896 ∗
     memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
     v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
     v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
     memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     A.pool ∗
     Rest) by ac_rfl))
    (sepConj_mono_left hpack)) ?_
  rw [v8_stackAt_encoder_split_dropStack32 (s0.sp - 2400#64)]
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 2208#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1520 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [protoUnchunkedCt1SentEkReceivedSize, BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
    change s1.pc = (blkPl_333).base + 10544#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 2208#64) s1 _ _
    have hm : memRegion (s0.sp - 2400#64) 896 ∗
        memRegion (s0.sp - 2400#64 + 896#64) 128 ∗
        memRegion (s0.sp - 2400#64 + 1024#64) 496 ⊢
        memRegion (s0.sp - 2400#64) 1520 :=
      collapse_top <|
        collapse_step0 (Entails.refl _) <|
        collapse_step (Entails.refl _) <|
        Entails.refl _
    wp_steps
    wp_call hdrop ⟨s0.sp - 1504#64, u⟩
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [v8_stackAt_encoder_split_dropStack32 (s0.sp - 2400#64), hsp1]
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion (s0.sp - 2400#64) 896 ∗
         memRegion (s0.sp - 2400#64 + 896#64) 128 ∗
         memRegion (s0.sp - 2400#64 + 1024#64) 496) ∗
        (memRegion (s0.sp - 2400#64 - 5152#64) 1024 ∗
         stackAt (s0.sp - 2400#64) dropStack32 ∗
         v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         A.pool ∗
         Rest) by simp only [arm64_norm]; ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by simp only [arm64_norm]; ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
    exact v8_drop_sendingCt1_2208_placed (A := A) (F := F) hA s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48 Rest hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlaced (
  v8_err_4240_placed
  v8_drop_sendingCt1_4216_placed
  v8_drop_sendingCt1_4212_placed
  v8_drop_sendingCt1_2208_placed
  v8_drop_uc_and_sendingCt1_2148_placed
  v8_drop_uc_and_sendingCt1_2100_placed
  v8_drop_uc_auth_none_10544_placed
)

end CryptoVerification.SpqrV1.States.FromPb
