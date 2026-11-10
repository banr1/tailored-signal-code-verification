/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5d
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dExt
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5e (`AllocContracts4K`: Arm 7 `ct1Sampled`)

Lifts `states_into_pb_ct1Sampled` from `AllocContracts` to `SpqrV1.Alloc.AllocContracts4K`.
-/

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eExt

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.States.IntoPb
open scoped CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1 (spqrPolyApi spqrAuthApi)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderAt polyEncoderSize polyDecoderAt polyDecoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
  (EncoderIntoPbOkExt encoderIntoPbStack)
open CryptoVerification.SpqrV1.Poly.DecoderPb (DecoderIntoPbOkExt)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize optProtoInnerStateSize
   none2Cap_add_two_beq_zero noneCap_add_two_beq_zero)
open CryptoVerification.SpqrV1.States.IntoPb
  (statesIntoPbName statesIntoPbStack statesIntoPbVariantSpec statesIntoPbJumpTableAt
   statesIntoPbSavedCells StatesIntoPbPost
   sepWPp_of_states_into_pb_wpp states_into_pb_prologue_60 states_into_pb_epilogue
   sub_ok_encoderIntoPb_raw sub_ok_decoderIntoPb_raw stackAt_encoderIntoPb_eq_allocHook
   epilogueStagingCells memRegion_1424_split_epilogue outWords28
   vecU8Heap vecU8CloneTail authenticatorHeap
   protoPolynomialEncoderHeap protoPolynomialDecoderHeap
   polyEncoderTag polyEncoderTailAt polyEncoderAt_eq_tag_tail
   chunkedCt1Sampled_expose ekReceivedScratchCells memRegion_ekReceived_scratch_split
   ct1SampledScratchCells_entails_memRegions stA_ct1Sampled_entails_928
   outWords28_entails_ct1Sampled
   ct1Sampled_step_60_to_1712 ct1Sampled_step_1712_to_2028_4k
   ct1Sampled_step_2028_to_2100_4k ct1Sampled_step_2100_to_2116
   ct1Sampled_step_2116_to_2128 ct1Sampled_step_2128_to_1544
   bv_sub_sub_lit' bv_add_add_lit')

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

set_option maxHeartbeats 800000 in
/-- Arm 7 (`States.ct1Sampled`, `PolyEncoder` tag `0` or `1`, jump table index `7` -> `+828`)
    under `AllocContracts4K`. -/
theorem states_into_pb_ct1Sampled_4k
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (henc : EncoderIntoPbOkExt b A ext)
    (hdec : DecoderIntoPbOkExt b A ext)
    (s : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled
      spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b (.ct1Sampled s)) := by
  have henc_raw := sub_ok_encoderIntoPb_raw henc
  have hdec_raw := sub_ok_decoderIntoPb_raw hdec
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb_align⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.ct1Sampled s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_wpp s0 s0 out stA (.ct1Sampled s) _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedCt1Sampled_expose A stA s))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro a0
  apply SepWPp.exists_elim; intro a1
  apply SepWPp.exists_elim; intro a2
  apply SepWPp.exists_elim; intro a3
  apply SepWPp.exists_elim; intro a4
  apply SepWPp.exists_elim; intro a5
  apply SepWPp.exists_elim; intro hdr0
  apply SepWPp.exists_elim; intro hdr1
  apply SepWPp.exists_elim; intro hdr2
  apply SepWPp.exists_elim; intro es0
  apply SepWPp.exists_elim; intro es1
  apply SepWPp.exists_elim; intro es2
  apply SepWPp.exists_elim; intro cap_ct1
  apply SepWPp.exists_elim; intro ptr_ct1
  rw [show memRegion out optProtoInnerStateSize ∗
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stA ↦₆₄ polyEncoderTag s.sending_ct1) ∗
      polyEncoderTailAt A stA s.sending_ct1 ∗
      ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
      ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
      ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
      ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
      ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (stA + 528#64) s.receiving_ek ∗
      (ptr_ct1 ↦ₛ s.uc.ct1) ∗
      vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
      vecU8Heap A es0 es1 es2 s.uc.es ∗
      statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack =
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ polyEncoderTag s.sending_ct1) ∗
       (statesIntoPbJumpTableAt b ∗
        memRegion out optProtoInnerStateSize ∗
        polyEncoderTailAt A stA s.sending_ct1 ∗
        ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
        ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
        ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
        ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
        ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
        ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
        polyDecoderAt A (stA + 528#64) s.receiving_ek ∗
        (ptr_ct1 ↦ₛ s.uc.ct1) ∗
        vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
        vecU8Heap A es0 es1 es2 s.uc.es ∗ A.pool)) by sep_ac_rfl]
  apply SepWPp.pure_elim; intro hlen
  have hpro := states_into_pb_prologue_60 s0 out stA (polyEncoderTag s.sending_ct1)
    (statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderTailAt A stA s.sending_ct1 ∗
     ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
     ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
     ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
     ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
     ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
     polyDecoderAt A (stA + 528#64) s.receiving_ek ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩
  have h1424 :
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416 ⊢
      memRegion (s0.sp - 1520#64) 1424 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1520#64) (n := 8) (k := 1416)
          (b' := s0.sp - 1512#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (pointsTo64_entails_memRegion (s0.sp - 1520#64) 0#64)
  have henc_rejoin :
      (stA ↦₆₄ polyEncoderTag s.sending_ct1) ∗ polyEncoderTailAt A stA s.sending_ct1 =
      polyEncoderAt A stA s.sending_ct1 :=
    (polyEncoderAt_eq_tag_tail A stA s.sending_ct1).symm
  refine SepWPp.weaken_pre
    (by
      rw [show stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ polyEncoderTag s.sending_ct1) ∗
          (statesIntoPbJumpTableAt b ∗
           memRegion out optProtoInnerStateSize ∗
           polyEncoderTailAt A stA s.sending_ct1 ∗
           ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
           ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
           ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
           ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
           ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
           ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
           ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
           polyDecoderAt A (stA + 528#64) s.receiving_ek ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
           vecU8Heap A es0 es1 es2 s.uc.es ∗ A.pool) =
          (((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
           statesIntoPbSavedCells s0 ∗
           ((stA ↦₆₄ polyEncoderTag s.sending_ct1) ∗ polyEncoderTailAt A stA s.sending_ct1) ∗
           statesIntoPbJumpTableAt b ∗
           memRegion out optProtoInnerStateSize ∗
           ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
           ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
           ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
           ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
           ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
           ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
           ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
           polyDecoderAt A (stA + 528#64) s.receiving_ek ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
           vecU8Heap A es0 es1 es2 s.uc.es ∗ A.pool) by sep_ac_rfl,
          henc_rejoin]
      exact sepConj_mono_left (Entails.trans h1424 (memRegion_1424_split_epilogue s0.sp))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro w8
  apply SepWPp.exists_elim; intro w16
  apply SepWPp.exists_elim; intro w24
  apply SepWPp.exists_elim; intro w32
  apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w48
  apply SepWPp.exists_elim; intro w64
  apply SepWPp.exists_elim; intro w72
  apply SepWPp.exists_elim; intro w80
  apply SepWPp.exists_elim; intro w88
  apply SepWPp.exists_elim; intro w96
  apply SepWPp.exists_elim; intro w104
  apply SepWPp.exists_elim; intro w112
  apply SepWPp.exists_elim; intro w120
  apply SepWPp.exists_elim; intro w128
  apply SepWPp.exists_elim; intro w136
  apply SepWPp.exists_elim; intro w144
  apply SepWPp.exists_elim; intro w152
  apply SepWPp.exists_elim; intro w160
  apply SepWPp.exists_elim; intro w168
  apply SepWPp.exists_elim; intro w176
  apply SepWPp.exists_elim; intro w184
  apply SepWPp.exists_elim; intro w192
  apply SepWPp.exists_elim; intro w200
  apply SepWPp.exists_elim; intro w208
  apply SepWPp.exists_elim; intro w216
  have hscratch_split :
      ∀ (Rest : SepProp),
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        memRegion (s0.sp - 1360#64) 880 ∗
        memRegion (s0.sp - 480#64) 176 ∗
        memRegion (s0.sp - 256#64) 160 ∗ Rest ⊢
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        (∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64,
         ∃∗ t4 : BitVec 64, ∃∗ t5 : BitVec 64, ∃∗ t6 : BitVec 64, ∃∗ t7 : BitVec 64,
         ∃∗ t8 : BitVec 64, ∃∗ t9 : BitVec 64, ∃∗ t10 : BitVec 64, ∃∗ t11 : BitVec 64,
         ∃∗ t12 : BitVec 64, ∃∗ t13 : BitVec 64, ∃∗ t14 : BitVec 64, ∃∗ t15 : BitVec 64,
         ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
         ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
         ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
           ekReceivedScratchCells s0.sp
             t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
             u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
           memRegion (s0.sp - 1232#64) 56 ∗
           memRegion (s0.sp - 1176#64) 696 ∗
           memRegion (s0.sp - 432#64) 128 ∗
           memRegion (s0.sp - 208#64) 112) ∗ Rest := by
    intro Rest
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       memRegion (s0.sp - 256#64) 160) ∗ Rest by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left (memRegion_ekReceived_scratch_split s0.sp))
  refine SepWPp.weaken_pre (hscratch_split _) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro t0
  apply SepWPp.exists_elim; intro t1
  apply SepWPp.exists_elim; intro t2
  apply SepWPp.exists_elim; intro t3
  apply SepWPp.exists_elim; intro t4
  apply SepWPp.exists_elim; intro t5
  apply SepWPp.exists_elim; intro t6
  apply SepWPp.exists_elim; intro t7
  apply SepWPp.exists_elim; intro t8
  apply SepWPp.exists_elim; intro t9
  apply SepWPp.exists_elim; intro t10
  apply SepWPp.exists_elim; intro t11
  apply SepWPp.exists_elim; intro t12
  apply SepWPp.exists_elim; intro t13
  apply SepWPp.exists_elim; intro t14
  apply SepWPp.exists_elim; intro t15
  apply SepWPp.exists_elim; intro u0
  apply SepWPp.exists_elim; intro u1
  apply SepWPp.exists_elim; intro u2
  apply SepWPp.exists_elim; intro u3
  apply SepWPp.exists_elim; intro u4
  apply SepWPp.exists_elim; intro u5
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v1
  apply SepWPp.exists_elim; intro v2
  apply SepWPp.exists_elim; intro v3
  apply SepWPp.exists_elim; intro v4
  apply SepWPp.exists_elim; intro v5
  rw [ProofLib.memRegion_split' (b := s0.sp - 1176#64) (n := 40) (k := 656)
        (b' := s0.sp - 1136#64) rfl (by bv_omega) (by decide)]
  have hstep2 := ct1Sampled_step_60_to_1712 s0 s1 out stA s.sending_ct1
    a0 a1 a2 a3 a4 a5 cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1.length
    t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    (memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 40 ∗
     memRegion (s0.sp - 1136#64) 656 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A stA s.sending_ct1 ∗
     polyDecoderAt A (stA + 528#64) s.receiving_ek ∗
     ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
     ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗ A.pool)
    hb_align hsp0_align hlen hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
  refine CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep2) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2,
    hx26_2, hx27_2, hx28_2, htr2⟩
  rw [stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)]
  refine SepWPp.weaken_pre ?_
    (ct1Sampled_step_1712_to_2028_4k hA s0 s2 out stA cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1
      (((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
       ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
       ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
       ekReceivedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
         u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
       memRegion (s0.sp - 1232#64) 56 ∗
       memRegion (s0.sp - 1176#64) 40 ∗
       memRegion (s0.sp - 1136#64) 656 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112 ∗
       memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       statesIntoPbJumpTableAt b ∗
       memRegion out optProtoInnerStateSize ∗
       polyEncoderAt A stA s.sending_ct1 ∗
       polyDecoderAt A (stA + 528#64) s.receiving_ek ∗
       ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
       ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A es0 es1 es2 s.uc.es)
      R hsp0_align hlen hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx22_2 hx23_2 hx24_2
      hx26_2 hx27_2 hx28_2 htr2 ?_)
  · exact Entails.of_eq (by sep_ac_rfl)
  intro s3 ptr_new hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
    hx26_3 hx27_3 hx28_3 htr3
  have hstep3 := ct1Sampled_step_2028_to_2100_4k hA s0 s3 out stA
    cap_ct1 ptr_ct1 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
    t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    (vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
     ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
     ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 40 ∗
     memRegion (s0.sp - 1136#64) 656 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A stA s.sending_ct1 ∗
     polyDecoderAt A (stA + 528#64) s.receiving_ek ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es)
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
    hx26_3 hx27_3 hx28_3 htr3
  refine CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep3) ?_
  intro s4 hpc4 hrun4 ⟨hsp4, hx29_4, hx19_4, hx20_4, hx21_4, hx22_4, hx27_4, hx28_4, htr4⟩
  have hrecomb_stack :
      memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗ stackAt (s0.sp - 1520#64) allocHookStack =
      stackAt (s0.sp - 1520#64) encoderIntoPbStack :=
    (stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)).symm
  refine SepWPp.weaken_pre ?_
    (ct1Sampled_step_2100_to_2116 henc_raw s0 s4 out stA ptr_new
      (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch s.sending_ct1
      (((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
       ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
       ekReceivedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
         hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
       ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
       ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1176#64) 40 ∗
       memRegion (s0.sp - 1136#64) 656 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112 ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       statesIntoPbJumpTableAt b ∗
       memRegion out optProtoInnerStateSize ∗
       polyDecoderAt A (stA + 528#64) s.receiving_ek ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A es0 es1 es2 s.uc.es)
      R hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hx20_4 hx21_4 hx22_4 hx27_4 hx28_4 htr4 ?_)
  · rw [← hrecomb_stack]
    exact Entails.of_eq (by sep_ac_rfl)
  intro s5 e0 e1 e2 e3 e4 e5 e6 hpc5 hrun5 hsp5 hx29_5 hx19_5 hx20_5 hx21_5 hx22_5
    hx23_5 hx27_5 hx28_5 htr5
  refine SepWPp.weaken_pre ?_
    (ct1Sampled_step_2116_to_2128 hdec_raw s0 s5 out stA ptr_new
      (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch s.receiving_ek
      ((((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
        ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
        ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
        ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
       protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       memRegion stA polyEncoderSize ∗
       ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
       ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
       ekReceivedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
         hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
       ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
       ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1136#64) 656 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112 ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       statesIntoPbJumpTableAt b ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A es0 es1 es2 s.uc.es)
      R hsp0_align hpc5 hrun5 hsp5 hx29_5 hx19_5 hx20_5 hx21_5 hx22_5
      hx23_5 hx27_5 hx28_5 htr5 ?_)
  · exact Entails.of_eq (by sep_ac_rfl)
  intro s6 d0 d1 d2 d3 d4 hpc6 hrun6 hsp6 hx29_6 hx19_6 hx21_6 hx22_6 hx27_6 hx28_6 htr6
  have hstep6 := ct1Sampled_step_2128_to_1544 s0 s6 out ptr_new
    (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
    e0 e1 e2 e3 e4 e5 e6
    d0 d1 d2 d3 d4
    t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
    (protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     memRegion (stA + 528#64) polyDecoderSize ∗
     A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     memRegion stA polyEncoderSize ∗
     ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
     ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
     vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
     ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
     ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1136#64) 656 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     statesIntoPbSavedCells s0 ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es)
    hsp0_align hpc6 hrun6 hsp6 hx29_6 hx19_6 hx21_6 hx22_6 hx27_6 hx28_6 htr6
  refine CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep6) ?_
  intro s7 hpc7 hrun7 ⟨hsp7, hx29_7, hx19_7, hx21_7, hx22_7, htr7⟩
  have hscratch := ct1SampledScratchCells_entails_memRegions s0.sp
    hdr0 hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length) t7
    (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
    hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
    d0 d1 d2 d3 d4
  have hstA := stA_ct1Sampled_entails_928 stA
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
    cap_ct1 ptr_ct1 (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
  have hpre_epi :
      ekReceivedScratchCells s0.sp
        hdr0 hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length) t7
        (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
        hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
      (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
       ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
       ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
       ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
      (((s0.sp - 1176#64) ↦₆₄ d0) ∗ ((s0.sp - 1168#64) ↦₆₄ d1) ∗
       ((s0.sp - 1160#64) ↦₆₄ d2) ∗ ((s0.sp - 1152#64) ↦₆₄ d3) ∗
       ((s0.sp - 1144#64) ↦₆₄ d4)) ∗
      epilogueStagingCells s0.sp
        hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length)
        (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch e0 e1 e2 e3 e4 e5 e6
        d0 d1 d2 d3 d4 ∗
      (protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       memRegion (stA + 528#64) polyDecoderSize ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       memRegion stA polyEncoderSize ∗
       ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
       ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
       ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
       ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1136#64) 656 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112 ∗
       statesIntoPbSavedCells s0 ∗
       statesIntoPbJumpTableAt b ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A es0 es1 es2 s.uc.es) ⊢
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length)
        (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch e0 e1 e2 e3 e4 e5 e6
        d0 d1 d2 d3 d4 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTableAt b ∗ A.pool) := by
    refine Entails.trans (Entails.of_eq (show _ =
      (ekReceivedScratchCells s0.sp
         hdr0 hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length) t7
         (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
         hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
        ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
        ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
        ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
       (((s0.sp - 1176#64) ↦₆₄ d0) ∗ ((s0.sp - 1168#64) ↦₆₄ d1) ∗
        ((s0.sp - 1160#64) ↦₆₄ d2) ∗ ((s0.sp - 1152#64) ↦₆₄ d3) ∗
        ((s0.sp - 1144#64) ↦₆₄ d4)) ∗
       memRegion (s0.sp - 1136#64) 656 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112) ∗
      (memRegion stA polyEncoderSize ∗
       ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
       ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
       ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
       ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
       ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (stA + 528#64) polyDecoderSize) ∗
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       epilogueStagingCells s0.sp
         hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length)
         (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
         s.uc.epoch e0 e1 e2 e3 e4 e5 e6
         d0 d1 d2 d3 d4 ∗
       statesIntoPbSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗
       protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       statesIntoPbJumpTableAt b ∗ A.pool) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hscratch (sepConj_mono hstA (Entails.refl _))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  apply SepWPp.of_sepWP_ret
  have hep := states_into_pb_epilogue s0 s7 out
    hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length)
    (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
    s.uc.epoch e0 e1 e2 e3 e4 e5 e6
    d0 d1 d2 d3 d4
    (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc7 hrun7 hsp7 hx29_7 hx19_7 htr7
  rw [hx22_7, hx21_7] at hep
  unfold StatesIntoPbPost
  refine SepWP.strengthen_entails_const ?_ (SepWP.weaken_pre hpre_epi hep)
  have hout := outWords28_entails_ct1Sampled A out
    hdr0 hdr1 hdr2 es0 es1 es2
    (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
    a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
    d0 d1 d2 d3 d4 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
       hdr0 hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
       e0 e1 e2 e3 e4 e5 e6
       d0 d1 d2 d3 d4 ∗
     protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack) by sep_ac_rfl)) ?_
  exact sepConj_mono_left hout

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SpqrV1.States.IntoPb
export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eExt
  (states_into_pb_ct1Sampled_4k)
end CryptoVerification.SpqrV1.States.IntoPb
-- AUTO-BRIDGE END
