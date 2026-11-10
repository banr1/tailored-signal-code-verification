/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8a
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8b
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for `Variant8b`

Lifts `Variant8b.lean`'s `AllocContracts`-parameterized theorems to `AllocContracts4K`
inside `CryptoVerification.SpqrV1.States.FromPb.Ext4K`.
-/

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
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

attribute [local simp, local arm64_norm, local wp_norm] v8_bv_add_add_lit'
attribute [local simp, local arm64_norm, local wp_norm] v8_bv_sub_sub_lit'
attribute [local arm64_norm, local wp_norm] v8_pbA_17_add_8
attribute [local arm64_norm, local wp_norm] v8_pbA_40_add_8
attribute [local arm64_norm, local wp_norm] v8_pbA_56_add_8
attribute [local arm64_norm, local wp_norm] v8_pbA_72_add_8
attribute [local arm64_norm, local wp_norm] v8_pbA_88_add_8
attribute [local arm64_norm, local wp_norm] v8_pbA_104_add_8
attribute [local arm64_norm, local wp_norm] v8_pbA_120_add_8
attribute [local arm64_norm, local wp_norm] v8_pbA_145_add_8
attribute [local arm64_norm, local wp_norm] v8_pbA_168_add_8
attribute [local arm64_norm, local wp_norm] v8_fsp_848_add_57
attribute [local arm64_norm, local wp_norm] v8_fsp_905_add_8
attribute [local arm64_norm, local wp_norm] v8_fsp_928_add_8
attribute [local arm64_norm, local wp_norm] v8_fsp_944_add_8
attribute [local arm64_norm, local wp_norm] v8_fsp_960_add_8
attribute [local arm64_norm, local wp_norm] v8_fsp_976_add_8
attribute [local arm64_norm, local wp_norm] v8_fsp_992_add_8
attribute [local arm64_norm, local wp_norm] v8_fsp_1008_add_8
attribute [local arm64_norm, local wp_norm] v8_fsp_249_add_8
attribute [local arm64_norm, local wp_norm] v8_fsp_272_add_8

namespace Ext4K

theorem v8_ekReceivedCt1Sampled_uc_none
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1764#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗
          A.pool ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hcopy := v8_copy_pb_to_stack_1764 s0 s1 out pbA
    noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     (pbA ↦₆₄ 0x8000000000000008#64) ∗
     memRegion (pbA + 192#64) 32 ∗
     v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
     statesFromPbJumpTableAt b ∗
     A.pool)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  have hcmn : (noneCap + 1#64 == 0#64) = true := by decide
  simp only [hcmn, ↓reduceIte] at hcopy
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4212#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1520 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b))
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
       statesFromPbJumpTableAt b) by ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono (Entails.trans (sepConj_mono_right huc) h1520) (sepConj_mono_left hpb))
      (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    have hdrop := Ext4K.v8_drop_sendingCt1_4212 (A := A) (F := F) hA s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2
    refine SepWP.mono hdrop fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb
