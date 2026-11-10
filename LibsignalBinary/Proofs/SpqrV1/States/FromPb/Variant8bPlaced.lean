/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8b
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 8 (`EkReceivedCt1Sampled`, `+1764`, Block `333`) — Part B

Relocatable (`Obj.MultiPlacedLib`) PB-to-stack copy (`+1764..+1872`), `s.uc = none` error exit,
and `es`/`ct1`/`ek` byte-length validation (`+1872 -> +1936 -> +2100 | +1972`) for Variant 8.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8bPlaced

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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v8_bv_add_add_lit' v8_bv_sub_sub_lit'
attribute [local arm64_norm, local wp_norm]
  v8_pbA_17_add_8 v8_pbA_40_add_8 v8_pbA_56_add_8 v8_pbA_72_add_8
  v8_pbA_88_add_8 v8_pbA_104_add_8 v8_pbA_120_add_8 v8_pbA_145_add_8
  v8_pbA_168_add_8 v8_fsp_848_add_57 v8_fsp_905_add_8 v8_fsp_928_add_8
  v8_fsp_944_add_8 v8_fsp_960_add_8 v8_fsp_976_add_8 v8_fsp_992_add_8
  v8_fsp_1008_add_8 v8_fsp_249_add_8 v8_fsp_272_add_8

/-! ## 1. PB-to-Stack Copy (`+1764..+1872`) and `s.uc = none` Error Path -/

/-- Copy the 184-byte payload `pbA + 8..192` to `fsp + 1392..1576` (`+1764..+1872`),
    branching to `+4212` if `u8 + 1 == 0` (`u8 = noneCap`) or falling through to `+1872`. -/
theorem v8_copy_pb_to_stack_1764_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (u8 + 1#64 == 0#64) = true
       then lsmpl.base 333 + 4212#64
       else lsmpl.base 333 + 1872#64)
      s1
      (memRegion (s0.sp - 2400#64) 2304 ∗
        v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          memRegion (s0.sp - 2400#64) 1392 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64)
            w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
          v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
            w0 w8 w16 w24 w32 w40 w48 ∗
          Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x23 = s1.readReg64 .x23 ∧
        s2.readReg64 .x26 = u8 ∧
        s2.readReg64 .x27 = pbA ∧
        TraceCalleeSaved s2 s0) := by
  rw [← v8_uc_and_enc_words_eq_pb128 pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48]
  refine SepWP.weaken_pre (sepConj_mono_left (v8_memRegion_2304_split_1392_184_728 (s0.sp - 2400#64))) ?_
  wp_simp_pre [v8_ucWordsAt, v1_optProtoPolyEncoderWordsAt, pointsTo128,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w11
  apply ProofLib.SepWP.exists_left; intro q10
  apply ProofLib.SepWP.exists_left; intro q9
  apply ProofLib.SepWP.exists_left; intro q8
  apply ProofLib.SepWP.exists_left; intro q7
  apply ProofLib.SepWP.exists_left; intro q6
  apply ProofLib.SepWP.exists_left; intro q5
  apply ProofLib.SepWP.exists_left; intro q4
  apply ProofLib.SepWP.exists_left; intro q3
  apply ProofLib.SepWP.exists_left; intro q2
  apply ProofLib.SepWP.exists_left; intro q1
  apply ProofLib.SepWP.exists_left; intro q0
  change s1.pc = (blkPl_333).base + 1764#64 at hpc1
  by_cases hcmn : (u8 + 1#64 == 0#64) = true <;>
    simp only [hcmn, Bool.false_eq_true, ↓reduceIte]
  · change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4212#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v8_ucWordsAt, v1_optProtoPolyEncoderWordsAt]
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 1872#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v8_ucWordsAt, v1_optProtoPolyEncoderWordsAt]
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    · wp_done

/-- Variant 8 error path when `s.uc = none` (`+1764 -> +4212 -> s0.x30`). -/
theorem v8_ekReceivedCt1Sampled_uc_none_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hcopy := v8_copy_pb_to_stack_1764_placed (ext := ext) s0 s1 out pbA
    noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     (pbA ↦₆₄ 0x8000000000000008#64) ∗
     memRegion (pbA + 192#64) 32 ∗
     v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
     statesFromPbJumpTablePlacedAt ∗
     A.pool)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  have hcmn : (noneCap + 1#64 == 0#64) = true := by decide
  simp only [hcmn, ↓reduceIte] at hcopy
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 4212#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1520 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt))
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      TraceCalleeSaved s2 s0)
    (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono hcopy fun s2 P2 _ _ ⟨hP2, hsp2, hx19_2, _, _, _, htr2⟩ => ?_)) ?_
  · refine ⟨Entails.trans hP2 ?_, hsp2, hx19_2, htr2⟩
    have huc := v8_ucWordsAt_entails_128 (s0.sp - 2400#64 + 1392#64)
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    have h1520 := v8_merge_1392_128_1520 (s0.sp - 2400#64)
    have hpb := v8_pb128_entails_full_224 pbA
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 1392 ∗
       v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
         noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128) ∗
      ((pbA ↦₆₄ 0x8000000000000008#64) ∗
       v8_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
         w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 192#64) 32) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       A.pool ∗
       statesFromPbJumpTablePlacedAt) by ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono (Entails.trans (sepConj_mono_right huc) h1520) (sepConj_mono_left hpb))
      (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
    have hdrop := v8_drop_sendingCt1_4212_placed (A := A) (F := F) hA s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2
    refine SepWP.mono hdrop fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-! ## 2. Step 1 (`+1872 -> +1936`) and Length Check (`+1936 -> +2100 | +1972`) -/

/-- Steps `+1872 -> +1936` (`lsmpl.base 333 + 1872 -> +1936`), copying `u8..u32` and `u72..u128` to
`fsp + 896..928` and `fsp + 960..1024`, and loading `x9 = u24`, `q0 = u48 ++ u40`, `q1 = u64 ++ u56`. -/
theorem v8_copy_uc_1872_to_1936_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z896 z904 z912 z920 z960 z968 z976 z984 z992 z1000 z1008 z1016 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1936#64) s1
      (v8_ucWordsAt (pbA + 8#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 896#64) ↦₆₄ z896) ∗
        ((s0.sp - 2400#64 + 904#64) ↦₆₄ z904) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ z912) ∗
        ((s0.sp - 2400#64 + 920#64) ↦₆₄ z920) ∗
        ((s0.sp - 2400#64 + 960#64) ↦₆₄ z960) ∗
        ((s0.sp - 2400#64 + 968#64) ↦₆₄ z968) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ z976) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ z984) ∗
        ((s0.sp - 2400#64 + 992#64) ↦₆₄ z992) ∗
        ((s0.sp - 2400#64 + 1000#64) ↦₆₄ z1000) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ z1008) ∗
        ((s0.sp - 2400#64 + 1016#64) ↦₆₄ z1016) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (pbA + 8#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
          ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
          ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
          ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
          ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
          ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
          ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
          ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
          ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
          ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = u24 ∧
        sm.readVReg128 0#5 = u48 ++ u40 ∧
        sm.readVReg128 1#5 = u64 ++ u56 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  change s1.pc = (blkPl_333).base + 1872#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 1936#64) s1 _ _
  wp_simp_pre [v8_ucWordsAt, v10_pbA_16_realign_rest, v8_fsp_1400_split_1_7_rest,
    v8_fsp_904_split_for_stur, sepConj_assoc]
  iterate 9 wp_step
  wp_simp_pre [v10_pbA_16_unrealign_rest, v8_fsp_1400_unsplit_1_7_rest, sepConj_assoc]
  iterate 3 wp_step
  wp_simp_pre [v8_fsp_913_realign_rest, v8_fsp_904_realign_16_rest, sepConj_assoc]
  iterate 4 wp_step
  simp only [v8_ucWordsAt, sepConj_assoc]
  wp_done

/-- At `+1936` (`lsmpl.base 333 + 1936`), when `u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64`,
stores `q0, q1` to `fsp + 928..960` and branches to `+2100`. -/
theorem v8_check_lengths_1936_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z928 z936 z944 z952 : BitVec 64)
    (Rest : SepProp)
    (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = u24)
    (hq0_1 : s1.readVReg128 0#5 = u48 ++ u40)
    (hq1_1 : s1.readVReg128 1#5 = u64 ++ u56)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2100#64) s1
      (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
        ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
        ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
        ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
        ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
        ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  change s1.pc = (blkPl_333).base + 1936#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 2100#64) s1 _ _
  by_cases h24 : u24 = 2080#64
  · subst h24
    by_cases h72 : u72 = 960#64
    · subst h72
      have h48 : u48 ≠ 1152#64 := by
        rcases herr with h | h | h
        · exact False.elim (h rfl)
        · exact False.elim (h rfl)
        · exact h
      have h48_bne : (u48 != 1152#64) = true := bne_iff_ne.mpr h48
      wp_steps
      simp only [v8_ucWordsAt, sepConj_assoc]
      wp_done
    · have h72_bne : (u72 != 960#64) = true := bne_iff_ne.mpr h72
      wp_steps
      simp only [v8_ucWordsAt, sepConj_assoc]
      wp_done
  · have h24_bne : (u24 != 2080#64) = true := bne_iff_ne.mpr h24
    wp_steps
    simp only [v8_ucWordsAt, sepConj_assoc]
    wp_done

/-- At `+1936` (`lsmpl.base 333 + 1936`), when `u24 = 2080#64 ∧ u72 = 960#64 ∧ u48 = 1152#64`,
stores `q0, q1` to `fsp + 928..960` and reaches `+1972` (`lsmpl.base 333 + 1972`). -/
theorem v8_check_lengths_1936_ok_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z928 z936 z944 z952 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = 2080#64)
    (hq0_1 : s1.readVReg128 0#5 = 1152#64 ++ u40)
    (hq1_1 : s1.readVReg128 1#5 = u64 ++ u56)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1972#64) s1
      (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗
        ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
        ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
        ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
        ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗
        ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
        ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = s1.readReg64 .x26 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  change s1.pc = (blkPl_333).base + 1936#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 1972#64) s1 _ _
  wp_steps
  simp only [v8_ucWordsAt, sepConj_assoc]
  wp_done

/-- Combined step `+1872 -> +2100` when `u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64`. -/
theorem v8_step_1872_to_2100_len_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2100#64) s1
      (memRegion (s0.sp - 2400#64) 1392 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        v8_ucWordsAt (pbA + 8#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (s0.sp - 2400#64) 896 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v8_ucWordsAt (pbA + 8#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre
    (sepConj_mono_left (v8_memRegion_1392_split_896_128_368 (s0.sp - 2400#64))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro z1016
  apply ProofLib.SepWP.exists_left; intro z1008
  apply ProofLib.SepWP.exists_left; intro z1000
  apply ProofLib.SepWP.exists_left; intro z992
  apply ProofLib.SepWP.exists_left; intro z984
  apply ProofLib.SepWP.exists_left; intro z976
  apply ProofLib.SepWP.exists_left; intro z968
  apply ProofLib.SepWP.exists_left; intro z960
  apply ProofLib.SepWP.exists_left; intro z952
  apply ProofLib.SepWP.exists_left; intro z944
  apply ProofLib.SepWP.exists_left; intro z936
  apply ProofLib.SepWP.exists_left; intro z928
  apply ProofLib.SepWP.exists_left; intro z920
  apply ProofLib.SepWP.exists_left; intro z912
  apply ProofLib.SepWP.exists_left; intro z904
  apply ProofLib.SepWP.exists_left; intro z896
  have hcopy := v8_copy_uc_1872_to_1936_placed (ext := ext) s0 s1 out pbA
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    z896 z904 z912 z920 z960 z968 z976 z984 z992 z1000 z1008 z1016
    (memRegion (s0.sp - 2400#64) 896 ∗
      ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
      ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
      ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
      ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
      memRegion (s0.sp - 2400#64 + 1024#64) 368 ∗
      ((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
      ((s0.sp - 2400#64 + 1392#64 + 16#64) ↦₆₄ u24) ∗
      ((s0.sp - 2400#64 + 1392#64 + 24#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 1392#64 + 32#64) ↦₆₄ u40) ∗
      ((s0.sp - 2400#64 + 1392#64 + 40#64) ↦₆₄ u48) ∗
      ((s0.sp - 2400#64 + 1392#64 + 48#64) ↦₆₄ u56) ∗
      ((s0.sp - 2400#64 + 1392#64 + 56#64) ↦₆₄ u64) ∗
      ((s0.sp - 2400#64 + 1392#64 + 64#64) ↦₆₄ u72) ∗
      ((s0.sp - 2400#64 + 1392#64 + 72#64) ↦₆₄ u80) ∗
      ((s0.sp - 2400#64 + 1392#64 + 80#64) ↦₆₄ u88) ∗
      ((s0.sp - 2400#64 + 1392#64 + 88#64) ↦₆₄ u96) ∗
      ((s0.sp - 2400#64 + 1392#64 + 96#64) ↦₆₄ u104) ∗
      ((s0.sp - 2400#64 + 1392#64 + 104#64) ↦₆₄ u112) ∗
      ((s0.sp - 2400#64 + 1392#64 + 112#64) ↦₆₄ u120) ∗
      ((s0.sp - 2400#64 + 1392#64 + 120#64) ↦₆₄ u128) ∗
      Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hx27_1 htr1
  have h1400 : (s0.sp - 2400#64 + 1392#64) + 8#64 = s0.sp - 2400#64 + 1400#64 := by bv_omega
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 1936#64)
    (P_mid :=
      ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
      ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
      ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
      ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
      ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
      ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
      ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
      ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
      ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
      ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
      ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
      ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
      ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
      ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
      (memRegion (s0.sp - 2400#64) 896 ∗
       memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
       v8_ucWordsAt (pbA + 8#64)
         u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
       Rest))
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x9 = u24 ∧
      s2.readVReg128 0#5 = u48 ++ u40 ∧
      s2.readVReg128 1#5 = u64 ++ u56 ∧
      s2.readReg64 .x19 = out ∧
      TraceCalleeSaved s2 s0)
    (SepWP.weaken_pre
      (by
        dsimp only [v8_ucWordsAt]
        rw [h1400]
        exact Entails.of_eq (by ac_rfl))
      (SepWP.mono hcopy fun s2 P2 _ _ ⟨hP2, hsp2, hx9_2, hq0_2, hq1_2, hx19_2, _, _, htr2⟩ => ?_)) ?_
  · refine ⟨Entails.trans hP2 ?_, hsp2, hx9_2, hq0_2, hq1_2, hx19_2, htr2⟩
    have hm496 := v8_merge_368_ucWords_496 (s0.sp - 2400#64)
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    dsimp only [v8_ucWordsAt] at hm496 ⊢
    rw [h1400] at hm496
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64 + 1024#64) 368 ∗
       (((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 1392#64 + 16#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 1392#64 + 24#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 1392#64 + 32#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 1392#64 + 40#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 1392#64 + 48#64) ↦₆₄ u56) ∗
        ((s0.sp - 2400#64 + 1392#64 + 56#64) ↦₆₄ u64) ∗
        ((s0.sp - 2400#64 + 1392#64 + 64#64) ↦₆₄ u72) ∗
        ((s0.sp - 2400#64 + 1392#64 + 72#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 1392#64 + 80#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 1392#64 + 88#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 1392#64 + 96#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 1392#64 + 104#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1392#64 + 112#64) ↦₆₄ u120) ∗
        ((s0.sp - 2400#64 + 1392#64 + 120#64) ↦₆₄ u128))) ∗
      (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
       ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
       ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
       ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
       ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
       ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
       ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
       ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
       ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
       ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
       ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
       ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
       ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
       ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
       ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
       memRegion (s0.sp - 2400#64) 896 ∗
       ((pbA + 8#64) ↦₆₄ u8) ∗
       ((pbA + 8#64 + 8#64) ↦₆₄ u16) ∗
       ((pbA + 8#64 + 16#64) ↦₆₄ u24) ∗
       ((pbA + 8#64 + 24#64) ↦₆₄ u32) ∗
       ((pbA + 8#64 + 32#64) ↦₆₄ u40) ∗
       ((pbA + 8#64 + 40#64) ↦₆₄ u48) ∗
       ((pbA + 8#64 + 48#64) ↦₆₄ u56) ∗
       ((pbA + 8#64 + 56#64) ↦₆₄ u64) ∗
       ((pbA + 8#64 + 64#64) ↦₆₄ u72) ∗
       ((pbA + 8#64 + 72#64) ↦₆₄ u80) ∗
       ((pbA + 8#64 + 80#64) ↦₆₄ u88) ∗
       ((pbA + 8#64 + 88#64) ↦₆₄ u96) ∗
       ((pbA + 8#64 + 96#64) ↦₆₄ u104) ∗
       ((pbA + 8#64 + 104#64) ↦₆₄ u112) ∗
       ((pbA + 8#64 + 112#64) ↦₆₄ u120) ∗
       ((pbA + 8#64 + 120#64) ↦₆₄ u128) ∗
       Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hm496) (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hq0_2, hq1_2, hx19_2, htr2⟩
    have hchk := v8_check_lengths_1936_err_placed (ext := ext) s0 s2 out
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
      z928 z936 z944 z952
      (memRegion (s0.sp - 2400#64) 896 ∗
       memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
       v8_ucWordsAt (pbA + 8#64)
         u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
       Rest)
      herr hsp0_align hpc2 hrun2 hsp2 hx9_2 hq0_2 hq1_2 hx19_2 htr2
    refine SepWP.mono hchk fun sf Pf _ _ ⟨hPf, hsp_f, hx19_f, htr_f⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, htr_f⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8bPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8bPlaced (
  v8_copy_pb_to_stack_1764_placed
  v8_ekReceivedCt1Sampled_uc_none_placed
  v8_copy_uc_1872_to_1936_placed
  v8_check_lengths_1936_err_placed
  v8_check_lengths_1936_ok_placed
  v8_step_1872_to_2100_len_err_placed
)

end CryptoVerification.SpqrV1.States.FromPb
