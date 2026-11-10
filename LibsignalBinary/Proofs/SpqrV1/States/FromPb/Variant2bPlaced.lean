/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 1 (`KeysSampled`, `+1104`) — Part B

Relocatable Block-`333` stack copy, validation, and `auth.rootKey` cloning (`+1104 -> +8756`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2bPlaced

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

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_sub_sub_lit v1_shl8_extract_0_8 v1_bv_add_add_lit

/-! ## Entry Copy (`+1104 -> +1196`) and `uc = None` Error Branch (`+1104 -> +4204 -> s0.x30`) -/

/-- Steps from `+1104` through the 160-byte copy of `s.uc` and `s.sendingHdr` to the stack frame,
    branching to `+4204` if `u8 + 1 == 0` (`u8 = noneCap`) or falling through to `+1196`. -/
theorem v1_copy_pb_to_stack_1104_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1104#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (u8 + 1#64 == 0#64) = true
       then lsmpl.base 333 + 4204#64
       else lsmpl.base 333 + 1196#64)
      s1
      (memRegion (s0.sp - 2400#64) 2304 ∗
        v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          w0 w8 w16 w24 w32 w40 w48 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          memRegion (s0.sp - 2400#64) 1392 ∗
          v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64)
            w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
            w0 w8 w16 w24 w32 w40 w48 ∗
          Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = u8 ∧
        s2.readReg64 .x27 = pbA ∧
        TraceCalleeSaved s2 s0) := by
  rw [← v1_uc_and_enc_words_eq_pb128 pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48]
  refine SepWP.weaken_pre (sepConj_mono_left (v1_memRegion_2304_split_1392_160_752 (s0.sp - 2400#64))) ?_
  wp_simp_pre [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt, pointsTo128,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
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
  change s1.pc = (blkPl_333).base + 1104#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    (if (u8 + 1#64 == 0#64) = true
     then (blkPl_333).base + 4204#64
     else (blkPl_333).base + 1196#64) s1 _ _
  by_cases hcmn : (u8 + 1#64 == 0#64) = true <;>
    simp only [hcmn, Bool.false_eq_true, ↓reduceIte]
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt]
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt]
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    · wp_done

/-- Variant 1 error path when `s.uc = none` (`+1104 -> +4204 -> s0.x30`). -/
theorem v1_keysSampled_uc_none_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1104#64)
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
        (pbA ↦₆₄ 0x8000000000000001#64) ∗
        v1_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          A.pool ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hcopy := v1_copy_pb_to_stack_1104_placed (ext := ext) s0 s1 out pbA
    noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     (pbA ↦₆₄ 0x8000000000000001#64) ∗
     memRegion (pbA + 168#64) 56 ∗
     v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
     A.pool)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  have hcmn : (noneCap + 1#64 == 0#64) = true := by decide
  simp only [hcmn, ↓reduceIte] at hcopy
  refine seq_clean_lscl
    (mid := lsmpl.base 333 + 4204#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1496 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool ∗
      memRegion pbA optProtoInnerStateSize)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      TraceCalleeSaved s2 s0)
    hcl1
    (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono hcopy fun s2 P2 _ _ ⟨hP2, hsp2, hx19_2, _, _, htr2⟩ => ?_)) ?_
  · refine ⟨Entails.trans hP2 ?_, hsp2, hx19_2, htr2⟩
    have huc := v1_ucWordsAt_entails_104 (s0.sp - 2400#64 + 1392#64)
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    have h1496 := v1_merge_1392_104_1496 (s0.sp - 2400#64)
    have hpb := v1_pb128_entails_full_224 pbA
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 1392 ∗
       v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
         noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
      ((pbA ↦₆₄ 0x8000000000000001#64) ∗
       v1_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
         w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       A.pool) by ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono (Entails.trans (sepConj_mono_right huc) h1496) (sepConj_mono_left hpb))
      (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
    have hdrop := v1_drop_sendingHdr_4204_placed (A := A) (F := F) hA s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48
      (memRegion pbA optProtoInnerStateSize)
      hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2
    refine SepWP.mono hdrop fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-! ## Validation (`+1196..+1260`) and `Authenticator::from_pb` (`+1260..+4016`) -/

/-- Validation error paths at `+1196`: when `u48 != 2400#64`, `u24 != 1152#64`, or `uc.auth = none`,
    cleans up `uc` and `sendingHdr` and returns `Err(StateDecode)`. -/
theorem v1_validate_err_1196_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (optAuth : Option ProtoAuthenticator)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (herr : (u48 == 2400#64) = false ∨ (u24 == 1152#64) = false ∨ optAuth = none)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1196#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u8)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1392 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64)
          w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u8 u16 ∗
        vecCapPtrDealloc A u32 u40 ∗
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
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (v1_memRegion_1392_split_frame (s0.sp - 2400#64)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w232
  apply ProofLib.SepWP.exists_left; intro w224
  apply ProofLib.SepWP.exists_left; intro w216
  apply ProofLib.SepWP.exists_left; intro w200
  apply ProofLib.SepWP.exists_left; intro w192
  apply ProofLib.SepWP.exists_left; intro w184
  apply ProofLib.SepWP.exists_left; intro w176
  apply ProofLib.SepWP.exists_left; intro w64
  by_cases hdk : (u48 == 2400#64) = true
  · by_cases hek : (u24 == 1152#64) = true
    · have hauth : optAuth = none := by
        rcases herr with h | h | h
        · rw [hdk] at h; cases h
        · rw [hek] at h; cases h
        · exact h
      subst hauth
      dsimp only [v1_optProtoAuthHeap]
      wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
      apply SepWP.pure_elim; intro hu56
      subst hu56
      refine seq_clean_lscl
        (mid := lsmpl.base 333 + 3936#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 192 ∗
          ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
          memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
          memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A u8 u16 ∗
          vecCapPtrDealloc A u32 u40 ∗
          A.pool ∗
          Rest)
        (Q := fun s2 =>
          s2.sp = s0.sp - 2400#64 ∧
          s2.readReg64 .x19 = out ∧
          s2.readReg64 .x20 = u8 ∧
          s2.readReg64 .x9 = u16 ∧
          TraceCalleeSaved s2 s0)
        hcl1 ?_ ?_
      · dsimp only [v1_ucWordsAt, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hdk hek ⊢
        change s1.pc = (blkPl_333).base + 1196#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 3936#64) s1 _ _
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hf := v1_frame_entails_192_216_224_1496 (s0.sp - 2400#64)
            w64 w176 w184 w192 w200 u40 u32 w232
            u8 u16 u24 u32 u40 u48 18446744073709551615#64 u64 u72 u80 u88 u96 u104
          dsimp only [v1_ucWordsAt] at hf
          simp only [arm64_norm] at hf ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 64 ∗
             ((s0.sp - 2336#64) ↦₆₄ w64) ∗
             memRegion (s0.sp - 2328#64) 104 ∗
             ((s0.sp - 2224#64) ↦₆₄ w176) ∗
             ((s0.sp - 2216#64) ↦₆₄ w184) ∗
             ((s0.sp - 2208#64) ↦₆₄ w192) ∗
             ((s0.sp - 2200#64) ↦₆₄ w200) ∗
             memRegion (s0.sp - 2192#64) 8 ∗
             ((s0.sp - 2184#64) ↦₆₄ u40) ∗
             ((s0.sp - 2176#64) ↦₆₄ u32) ∗
             ((s0.sp - 2168#64) ↦₆₄ w232) ∗
             memRegion (s0.sp - 2160#64) 1152 ∗
             ((s0.sp - 1008#64) ↦₆₄ u8) ∗ ((s0.sp - 1000#64) ↦₆₄ u16) ∗
             ((s0.sp - 992#64) ↦₆₄ u24) ∗ ((s0.sp - 984#64) ↦₆₄ u32) ∗
             ((s0.sp - 976#64) ↦₆₄ u40) ∗ ((s0.sp - 968#64) ↦₆₄ u48) ∗
             ((s0.sp - 960#64) ↦₆₄ 18446744073709551615#64) ∗ ((s0.sp - 952#64) ↦₆₄ u64) ∗
             ((s0.sp - 944#64) ↦₆₄ u72) ∗ ((s0.sp - 936#64) ↦₆₄ u80) ∗
             ((s0.sp - 928#64) ↦₆₄ u88) ∗ ((s0.sp - 920#64) ↦₆₄ u96) ∗
             ((s0.sp - 912#64) ↦₆₄ u104)) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 848#64) 752 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ A.pool ∗ Rest) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hf) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, hx9_2, htr2⟩
        exact v1_drop_uc_and_sendingHdr_3936_placed (A := A) (F := F) hA s0 s2 out
          u8 u16 u32 u40 w192 optEnc w0 w8 w16 w24 w32 w40 w48 Rest
          hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx9_2 htr2
    · have hek_f : (u24 == 1152#64) = false := Bool.eq_false_iff.mpr hek
      refine seq_clean_lscl
        (mid := lsmpl.base 333 + 3872#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 192 ∗
          ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
          memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
          memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A u8 u16 ∗
          vecCapPtrDealloc A u32 u40 ∗
          v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ∗
          A.pool ∗
          Rest)
        (Q := fun s2 =>
          s2.sp = s0.sp - 2400#64 ∧
          s2.readReg64 .x19 = out ∧
          s2.readReg64 .x20 = u8 ∧
          s2.readReg64 .x9 = u16 ∧
          s2.readReg64 .x25 = u56 ∧
          s2.readReg64 .x28 = u64 ∧
          s2.readReg64 .x23 = u80 ∧
          s2.readReg64 .x24 = u88 ∧
          TraceCalleeSaved s2 s0)
        hcl1 ?_ ?_
      · dsimp only [v1_ucWordsAt, BitVec.ofNat_eq_ofNat] at hpc1 hdk hek_f ⊢
        change s1.pc = (blkPl_333).base + 1196#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 3872#64) s1 _ _
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hf := v1_frame_entails_192_216_224_1496 (s0.sp - 2400#64)
            w64 w176 w184 w192 w200 u40 u32 w232
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          dsimp only [v1_ucWordsAt] at hf
          simp only [arm64_norm] at hf ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 64 ∗
             ((s0.sp - 2336#64) ↦₆₄ w64) ∗
             memRegion (s0.sp - 2328#64) 104 ∗
             ((s0.sp - 2224#64) ↦₆₄ w176) ∗
             ((s0.sp - 2216#64) ↦₆₄ w184) ∗
             ((s0.sp - 2208#64) ↦₆₄ w192) ∗
             ((s0.sp - 2200#64) ↦₆₄ w200) ∗
             memRegion (s0.sp - 2192#64) 8 ∗
             ((s0.sp - 2184#64) ↦₆₄ u40) ∗
             ((s0.sp - 2176#64) ↦₆₄ u32) ∗
             ((s0.sp - 2168#64) ↦₆₄ w232) ∗
             memRegion (s0.sp - 2160#64) 1152 ∗
             ((s0.sp - 1008#64) ↦₆₄ u8) ∗ ((s0.sp - 1000#64) ↦₆₄ u16) ∗
             ((s0.sp - 992#64) ↦₆₄ u24) ∗ ((s0.sp - 984#64) ↦₆₄ u32) ∗
             ((s0.sp - 976#64) ↦₆₄ u40) ∗ ((s0.sp - 968#64) ↦₆₄ u48) ∗
             ((s0.sp - 960#64) ↦₆₄ u56) ∗ ((s0.sp - 952#64) ↦₆₄ u64) ∗
             ((s0.sp - 944#64) ↦₆₄ u72) ∗ ((s0.sp - 936#64) ↦₆₄ u80) ∗
             ((s0.sp - 928#64) ↦₆₄ u88) ∗ ((s0.sp - 920#64) ↦₆₄ u96) ∗
             ((s0.sp - 912#64) ↦₆₄ u104)) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 848#64) 752 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗
             v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ∗ A.pool ∗ Rest) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hf) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, hx9_2, hx25_2, hx28_2, hx23_2, hx24_2, htr2⟩
        exact v1_drop_uc_and_sendingHdr_3872_placed (A := A) (F := F) hA s0 s2 out
          u8 u16 u32 u40 w192 optAuth u56 u64 u72 u80 u88 u96
          optEnc w0 w8 w16 w24 w32 w40 w48 Rest
          hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx9_2 hx25_2 hx28_2 hx23_2 hx24_2 htr2
  · have hdk_f : (u48 == 2400#64) = false := Bool.eq_false_iff.mpr hdk
    refine seq_clean_lscl
      (mid := lsmpl.base 333 + 3872#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u8 u16 ∗
        vecCapPtrDealloc A u32 u40 ∗
        v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ∗
        A.pool ∗
        Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = u8 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x25 = u56 ∧
        s2.readReg64 .x28 = u64 ∧
        s2.readReg64 .x23 = u80 ∧
        s2.readReg64 .x24 = u88 ∧
        TraceCalleeSaved s2 s0)
      hcl1 ?_ ?_
    · dsimp only [v1_ucWordsAt, BitVec.ofNat_eq_ofNat] at hpc1 hdk_f ⊢
      change s1.pc = (blkPl_333).base + 1196#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 3872#64) s1 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hf := v1_frame_entails_192_216_224_1496 (s0.sp - 2400#64)
          w64 w176 w184 w192 w200 u40 u32 w232
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        dsimp only [v1_ucWordsAt] at hf
        simp only [arm64_norm] at hf ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 64 ∗
           ((s0.sp - 2336#64) ↦₆₄ w64) ∗
           memRegion (s0.sp - 2328#64) 104 ∗
           ((s0.sp - 2224#64) ↦₆₄ w176) ∗
           ((s0.sp - 2216#64) ↦₆₄ w184) ∗
           ((s0.sp - 2208#64) ↦₆₄ w192) ∗
           ((s0.sp - 2200#64) ↦₆₄ w200) ∗
           memRegion (s0.sp - 2192#64) 8 ∗
           ((s0.sp - 2184#64) ↦₆₄ u40) ∗
           ((s0.sp - 2176#64) ↦₆₄ u32) ∗
           ((s0.sp - 2168#64) ↦₆₄ w232) ∗
           memRegion (s0.sp - 2160#64) 1152 ∗
           ((s0.sp - 1008#64) ↦₆₄ u8) ∗ ((s0.sp - 1000#64) ↦₆₄ u16) ∗
           ((s0.sp - 992#64) ↦₆₄ u24) ∗ ((s0.sp - 984#64) ↦₆₄ u32) ∗
           ((s0.sp - 976#64) ↦₆₄ u40) ∗ ((s0.sp - 968#64) ↦₆₄ u48) ∗
           ((s0.sp - 960#64) ↦₆₄ u56) ∗ ((s0.sp - 952#64) ↦₆₄ u64) ∗
           ((s0.sp - 944#64) ↦₆₄ u72) ∗ ((s0.sp - 936#64) ↦₆₄ u80) ∗
           ((s0.sp - 928#64) ↦₆₄ u88) ∗ ((s0.sp - 920#64) ↦₆₄ u96) ∗
           ((s0.sp - 912#64) ↦₆₄ u104)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 848#64) 752 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗
           v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hf) (Entails.of_eq (by ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, hx9_2, hx25_2, hx28_2, hx23_2, hx24_2, htr2⟩
      exact v1_drop_uc_and_sendingHdr_3872_placed (A := A) (F := F) hA s0 s2 out
        u8 u16 u32 u40 w192 optAuth u56 u64 u72 u80 u88 u96
        optEnc w0 w8 w16 w24 w32 w40 w48 Rest
        hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx9_2 hx25_2 hx28_2 hx23_2 hx24_2 htr2

/-- Validation success step (`+1196 -> +1292`): when `u48 = 2400#64`, `u24 = 1152#64`, and
    `u56.toNat < 2 ^ 63`, stores stack slots `64, 176, 192, 216, 224, 232` and collapses
    `v1_ucWordsAt (fsp + 1392#64)` into `memRegion (fsp + 240#64) 1256`. -/
theorem v1_validate_ok_1196_1292_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (w64 w176 w192 w216 w224 w232 : BitVec 64)
    (Rest : SepProp)
    (hdk : (u48 == 2400#64) = true)
    (hek : (u24 == 1152#64) = true)
    (hu56 : u56.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1196#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1292#64) s1
      (((s0.sp - 2400#64 + 64#64) ↦₆₄ w64) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1152 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
          ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
          ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
          memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
          Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = u72 ∧
        s2.readReg64 .x21 = u8 ∧
        s2.readReg64 .x22 = u48 ∧
        s2.readReg64 .x23 = u80 ∧
        s2.readReg64 .x24 = u88 ∧
        s2.readReg64 .x25 = u56 ∧
        s2.readReg64 .x27 = pbA ∧
        s2.readReg64 .x28 = u64 ∧
        s2.readReg64 .x9 = u96 ∧
        TraceCalleeSaved s2 s0) := by
  have hcmn : (u56 + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hu56)
  dsimp only [v1_ucWordsAt, BitVec.ofNat_eq_ofNat] at hpc1 hdk hek ⊢
  change s1.pc = (blkPl_333).base + 1196#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 1292#64) s1 _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hm := v1_merge_240_1152_104_1256 (s0.sp - 2400#64)
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    have hdk_eq : u48 = 2400#64 := beq_iff_eq.mp hdk
    dsimp only [v1_ucWordsAt] at hm
    simp only [arm64_norm] at hm ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2160#64) 1152 ∗
       ((s0.sp - 1008#64) ↦₆₄ u8) ∗ ((s0.sp - 1000#64) ↦₆₄ u16) ∗
       ((s0.sp - 992#64) ↦₆₄ u24) ∗ ((s0.sp - 984#64) ↦₆₄ u32) ∗
       ((s0.sp - 976#64) ↦₆₄ u40) ∗ ((s0.sp - 968#64) ↦₆₄ u48) ∗
       ((s0.sp - 960#64) ↦₆₄ u56) ∗ ((s0.sp - 952#64) ↦₆₄ u64) ∗
       ((s0.sp - 944#64) ↦₆₄ u72) ∗ ((s0.sp - 936#64) ↦₆₄ u80) ∗
       ((s0.sp - 928#64) ↦₆₄ u88) ∗ ((s0.sp - 920#64) ↦₆₄ u96) ∗
       ((s0.sp - 912#64) ↦₆₄ u104)) ∗
      (((s0.sp - 2336#64) ↦₆₄ u104) ∗
       ((s0.sp - 2224#64) ↦₆₄ u16) ∗
       ((s0.sp - 2208#64) ↦₆₄ 2400#64) ∗
       ((s0.sp - 2184#64) ↦₆₄ u40) ∗
       ((s0.sp - 2176#64) ↦₆₄ u32) ∗
       ((s0.sp - 2168#64) ↦₆₄ u96) ∗
       Rest) by ac_rfl)) ?_
    rw [hdk_eq] at hm ⊢
    exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
  · wp_done

set_option maxHeartbeats 800000 in
/-- `Authenticator::from_pb` segment (`+1292 -> +8756`) in Variant 1:
    allocates and copies `auth.rootKey` into `pa1 = s1.readReg64 .x26` (or `1#64` if empty). -/
theorem v1_auth_from_pb_step1_1292_8756_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (target_pc fsp out pbA : BitVec 64)
    (u8 u56 u64 u80 u88 u96 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1292#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx21 : s.readReg64 .x21 = u8)
    (hx23 : s.readReg64 .x23 = u80)
    (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u64)
    (hx9 : s.readReg64 .x9 = u96)
    (hu96 : u96 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa1 : BitVec 64) (s1 : State),
      s1.pc = lsmpl.base 333 + 8756#64 →
      s1.status = .Running →
      (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
       s1.readReg64 .x21 = u8 ∧
       s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
       s1.readReg64 .x23 = u80 ∧ s1.readReg64 .x24 = u88 ∧
       s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = pa1 ∧
       s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧
       s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 232#64) ↦₆₄ u96) ∗
         vecCapPtrDealloc A u56 u64 ∗
         vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
         A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 232#64) ↦₆₄ u96) ∗
       vecU8Payload A u56 u64 auth.rootKey ∗
       A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hr_cases : auth.rootKey = [] ∨ 0 < auth.rootKey.length := by cases auth.rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · refine CryptoVerification.SpqrV1.States.FromPb.sepWPp_seq_clean
      (mid := lsmpl.base 333 + 8756#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
        vecCapPtrDealloc A u56 u64 ∗
        vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) 1#64 auth.rootKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x23 = u80 ∧ s1.readReg64 .x24 = u88 ∧
        s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = 1#64 ∧
        s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧
        s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0)
      ?_ (hnext 1#64)
    clear hnext; rw [hr_nil] at hx20 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hpc hx20 ⊢
    change s.pc = (blkPl_333).base + 1292#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8756#64) s _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A u56 u64 []
      have hn := vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A u56 u64 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecU8Payload_pos_unpack A u56 u64 auth.rootKey hr_pos)))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
          (⌜auth.rootKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧
            u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
           (A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.rootKey) ∗
            memRegion (u64 + BitVec.ofNat 64 auth.rootKey.length) (u56.toNat - auth.rootKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.rootKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧
          u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
         A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.rootKey) ∗
         memRegion (u64 + BitVec.ofNat 64 auth.rootKey.length) (u56.toNat - auth.rootKey.length) ∗
         A.pool ∗ Frame) by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hr_le, hr_cap, hptr0, hcap0_ne⟩ => ?_
    have hr_lt63 : auth.rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 auth.rootKey.length == 0#64) = false := ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hr_lay3 : auth.rootKey.length + 1 ≤ 2 ^ 63 := hr_lt63
    have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [stackAt_encoderFromPb_split_allocHook fsp]; wp_simp_pre [sepConj_assoc]
    have hshim : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec := by
      simpa only [lsProg_333, blkPl_333] using
        (spqr_hook_ok_of_mem hA.shim : subroutine_ok (lsProg_333 (Rust.withPanics ext))
          (lsρ spqrRustNoAllocShimSym) sessionShimSpec)
    simp only [sessionShimSpec] at hshim
    have halloc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) := by
      simpa only [lsProg_333, blkPl_333] using
        (spqr_hook_ok_of_mem hA.alloc : subroutine_ok (lsProg_333 (Rust.withPanics ext))
          (lsρ spqrRustAllocSym) (rustAllocSpec A))
    simp only [rustAllocSpec] at halloc
    have hmc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec := by
      simpa only [lsProg_333, blkPl_333] using
        (spqr_hook_ok_of_mem hA.memcpy : subroutine_ok (lsProg_333 (Rust.withPanics ext))
          (lsρ spqrMemcpySym) sessionMemcpySpec)
    simp only [sessionMemcpySpec] at hmc
    have hpanic := fromPb_externAt?_handleError hA
    change s.pc = (blkPl_333).base + 1292#64 at hpc
    change ∀ (pa1 : BitVec 64) (s1 : State),
      s1.pc = (blkPl_333).base + 8756#64 → _ → _ →
      SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s1 _ _ _ at hnext
    change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s _ _ _
    clear hA
    apply SepWPp.of_sepWP (mid := (blkPl_333).base + 1312#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.rootKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      refine CryptoVerification.SpqrV1.States.FromPb.sepWPp_seq_clean (mid := (blkPl_333).base + 8756#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
          vecCapPtrDealloc A u56 u64 ∗
          vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) (sf_1.readReg64 Reg.x0) auth.rootKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
          s1.readReg64 .x21 = u8 ∧
          s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
          s1.readReg64 .x23 = u80 ∧ s1.readReg64 .x24 = u88 ∧
          s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = sf_1.readReg64 Reg.x0 ∧
          s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧
          s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0)
        ?_ (hnext (sf_1.readReg64 Reg.x0))
      clear hnext
      have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp, hsp_sf1]
        have hd := vecU8Payload_pos_dealloc A u56 u64 auth.rootKey hr_le hr_cap hptr0 hcap0_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.rootKey hr_pos hr_lt63 hoom0
        simp only [arm64_norm] at hd hp ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.rootKey) ∗
           memRegion (u64 + BitVec.ofNat 64 auth.rootKey.length) (u56.toNat - auth.rootKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.rootKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.rootKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
          ((fsp + 232#64) ↦₆₄ u96) ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2bPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2bPlaced (
  v1_copy_pb_to_stack_1104_placed
  v1_keysSampled_uc_none_placed
  v1_validate_err_1196_placed
  v1_validate_ok_1196_1292_placed
  v1_auth_from_pb_step1_1292_8756_placed
)

end CryptoVerification.SpqrV1.States.FromPb
