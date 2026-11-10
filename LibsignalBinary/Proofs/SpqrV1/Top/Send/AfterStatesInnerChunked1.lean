/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerHeader
import all Init.Data.Nat.Bitwise.Basic
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: `V1State::encode_raw` Branches (`idx = 3, 4, 7, 9`)

Symbolic execution of the shared `PolynomialEncoder` / `PolynomialDecoder` tail blocks and the
`.ct1Sampled` (`idx = 7`), `.ekSentCt1Received` (`idx = 4`), `.ct1Acknowledged` (`idx = 9`), and
`.ct1Received` (`idx = 3`) encoding branches in `spqr::send::<HookRng>`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet (spqrSendName)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  Prost.EncodeToVec.noneCap2_add_two_beq_zero Prost.EncodeToVec.noneCap2_add_two_bne_zero
  ProtoRepr.noneCap_add_two_beq_zero ProtoRepr.noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Shared `PolynomialDecoder` / `PolynomialEncoder` Tail Blocks -/

/-- Step `+10352 .. +6216` (`0x330cc .. 0x320a4`): sets `x2 = sp + 1424#64`, `w0 = 3#32`, calls
    `encode<PolynomialDecoder> [local#1]` (`0x37520`) with `x1 = dec_ptr`, then branches to
    `+6216`. -/
theorem step_send_tail_10352_polyDec3 {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry)
    {s0 s : State}
    (hpolyDec : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 27844#64) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (dec_ptr sp cap ptr : BitVec 64) (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 10352#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = dec_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialDecoderPBPinnedAt A g dec_ptr dec ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((polynomialDecoderPBPinnedAt A g dec_ptr dec ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F) Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches b (Rust.withPanics ext) hfn 10352 10368; examples_hide_fetches; subst hP
  apply SepWPp.of_sepWP_cs (mid := entry + 27844#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_send_encode_polyDecoder_call b A ext hpolyDec 3#32 dec_ptr (sp + 1424#64) cap ptr sp (entry + 10364#64) g dec bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1; rcases hcsm1 with ⟨hm19, _, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩; simp only [arm64_norm] at hm19 hm21 hm23 hm25 hm27 hm28 hmfp
  apply SepWPp.of_sepWP_cs (mid := entry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2)

/-- Step `+11208 .. +6216` (`0x33424 .. 0x320a4`): sets `x2 = sp + 1424#64`, `w0 = 2#32`, calls
    `encode<PolynomialDecoder> [local#1]` (`0x37520`) with `x1 = dec_ptr`, then branches to
    `+6216`. -/
theorem step_send_tail_11208_polyDec2 {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry)
    {s0 s : State}
    (hpolyDec : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 27844#64) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (dec_ptr sp cap ptr : BitVec 64) (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 11208#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = dec_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialDecoderPBPinnedAt A g dec_ptr dec ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((polynomialDecoderPBPinnedAt A g dec_ptr dec ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw 2#32 dec) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F) Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches b (Rust.withPanics ext) hfn 11208 11224; examples_hide_fetches; subst hP
  apply SepWPp.of_sepWP_cs (mid := entry + 27844#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_send_encode_polyDecoder_call b A ext hpolyDec 2#32 dec_ptr (sp + 1424#64) cap ptr sp (entry + 11220#64) g dec bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1; rcases hcsm1 with ⟨hm19, _, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩; simp only [arm64_norm] at hm19 hm21 hm23 hm25 hm27 hm28 hmfp
  apply SepWPp.of_sepWP_cs (mid := entry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2)

/-- Step `+11748 .. +6216` (`0x33640 .. 0x320a4`): sets `x1 = sp + 1424#64`, calls
    `encode<PolynomialEncoder> [local#1]` (`0x37690`) with `x0 = enc_ptr`, then branches to
    `+6216`. -/
theorem step_send_tail_11748_polyEnc {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry)
    {s0 s : State}
    (hpolyEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 28212#64) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (enc_ptr sp cap ptr : BitVec 64) (g : PolynomialEncoderPBGhost) (enc : PolynomialEncoder)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 11748#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = enc_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialEncoderPBPinnedAt A g enc_ptr enc ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((polynomialEncoderPBPinnedAt A g enc_ptr enc ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F) Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches b (Rust.withPanics ext) hfn 11748 11760; examples_hide_fetches; subst hP
  apply SepWPp.of_sepWP_cs (mid := entry + 28212#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_send_encode_polyEncoder_call b A ext hpolyEnc enc_ptr (sp + 1424#64) cap ptr sp (entry + 11756#64) g enc bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1; rcases hcsm1 with ⟨hm19, _, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩; simp only [arm64_norm] at hm19 hm21 hm23 hm25 hm27 hm28 hmfp
  apply SepWPp.of_sepWP_cs (mid := entry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2)

/-! ## 2. Variant `idx = 7`: `.ct1Sampled` (`+8480 .. +8608`, `0x3297c .. 0x329fc`) -/

/-- Step `+8480 .. +6216` (`0x3297c .. 0x320a4`) for `is = .ct1Sampled v`. -/
theorem step_send_v1_ct1Sampled {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry)
    {s0 s : State}
    (hct1SampledLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 36916#64) (withStepInv s0 (chunkedCt1SampledEncodedLenPinnedSpec A)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 24012#64) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 29708#64) (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 28212#64) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 27844#64) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (sp cap ptr : BitVec 64) (g : ChunkedCt1SampledPBGhost) (v : V1State.Chunked.Ct1Sampled)
    (bs : List (BitVec 8)) (hv_len : v1StatePBEncodedLen ⟨some (.ct1Sampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct1Sampled v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 8480#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = Prost.EncodeToVec.optCt1SentCap g.uc v.uc) (hinv0 : StepInv s0 s)
    (hP : P = (chunkedCt1SampledPBPinnedAt A g (sp + 4832#64) v ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((chunkedCt1SampledPBPinnedAt A g (sp + 4832#64) v ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.ct1Sampled v)) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F) Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches b (Rust.withPanics ext) hfn 8480 8612; examples_hide_fetches; subst hP
  rcases v with ⟨uc, sendingCt1, receivingEk⟩
  rw [encodeInnerState_ct1Sampled_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩ < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x42#8]).length +
      (Proto.encodeVarint (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := chunkedCt1SampledPBPinnedAt A g (sp + 4832#64) ⟨uc, sendingCt1, receivingEk⟩ ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  rw [h1432, h1440]
  apply SepWPp.of_sepWP_cs (mid := entry + 36916#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x42#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack
  refine step_send_chunked_encLen48_call hres b ext (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen hct1SampledLen
    (sp + 4832#64) sp (entry + 8532#64) g ⟨uc, sendingCt1, receivingEk⟩ hsub_len
    (F := vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x42#8]) ∗ A.pool ∗ F) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (hinv0.trans hinv1) (by rw [← hpack]; ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1; rcases hcsm1 with ⟨hm19, hm20, hm21, hm22, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩; simp only [arm64_norm, hx20] at hm19 hm20 hm21 hm22 hm23 hm25 hm27 hm28 hmfp
  apply SepWPp.of_sepWP_cs (mid := entry + 24012#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  set bs1 := (bs ++ [0x42#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩))
  refine step_send_encode_varint_call b A ext hvarint
    (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩))
    (sp + 1424#64) cap ptr sp (entry + 8540#64) (bs ++ [0x42#8]) hfit_var
    (F := chunkedCt1SampledPBPinnedAt A g (sp + 4832#64) ⟨uc, sendingCt1, receivingEk⟩ ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2) (by ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2; rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩; simp only [arm64_norm, hm19, hm20, hm21, hm22, hm23, hm25, hm27, hm28, hmfp] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_25 hm2_27 hm2_28 hm2_fp
  have ⟨h4960, h5016⟩ : (sp + 4832#64) + 128#64 = sp + 4960#64 ∧ (sp + 4832#64) + 184#64 = sp + 5016#64 := ⟨by bv_omega, by bv_omega⟩
  refine SepWPp.weaken_pre (P' := ((optCt1SentPBPinnedAt A g.uc (sp + 4832#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.sendingCt1 (sp + 4960#64) sendingCt1 ∗
      optPolynomialDecoderPBPinnedAt A g.receivingEk (sp + 5016#64) receivingEk) ∗ vecU8At A (sp + 1424#64) cap ptr bs1 ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (Entails.of_eq (by dsimp +zetaDelta only [chunkedCt1SampledPBPinnedAt]; rw [h4960, h5016]; ac_rfl)) ?_
  refine sepWPp_extract_pure
    (((Prost.EncodeToVec.optCt1SentCap g.uc uc + 1#64 == 0#64) = !uc.isSome ∧
      (Prost.EncodeToVec.optCt1SentCap g.uc uc + 1#64 != 0#64) = uc.isSome) ∧
     ((Prost.EncodeToVec.optPolyEncCap g.sendingCt1 sendingCt1 + 1#64 == 0#64) = !sendingCt1.isSome ∧
      (Prost.EncodeToVec.optPolyEncCap g.sendingCt1 sendingCt1 + 1#64 != 0#64) = sendingCt1.isSome) ∧
     ((Prost.EncodeToVec.optPolyDecCap g.receivingEk receivingEk + 1#64 == 0#64) = !receivingEk.isSome ∧
      (Prost.EncodeToVec.optPolyDecCap g.receivingEk receivingEk + 1#64 != 0#64) = receivingEk.isSome))
    (fun R' hm =>
      ⟨Prost.EncodeToVec.optCt1SentPBPinnedAt_cap_bounds (p := sp + 4832#64)
        (R := optPolynomialEncoderPBPinnedAt A g.sendingCt1 (sp + 4960#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A g.receivingEk (sp + 5016#64) receivingEk ∗ vecU8At A (sp + 1424#64) cap ptr bs1 ∗ A.pool ∗
          stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
       Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_cap_bounds (p := sp + 4960#64)
        (R := optCt1SentPBPinnedAt A g.uc (sp + 4832#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.receivingEk (sp + 5016#64) receivingEk ∗
          vecU8At A (sp + 1424#64) cap ptr bs1 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
       Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_cap_bounds (p := sp + 5016#64)
        (R := optCt1SentPBPinnedAt A g.uc (sp + 4832#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.sendingCt1 (sp + 4960#64) sendingCt1 ∗
          vecU8At A (sp + 1424#64) cap ptr bs1 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 uc
  suffices h8560 : ∀ sm3 : State,
      sm3.pc = entry + 8560#64 → sm3.status = .Running → sm3.sp = sp → sm3.trace = s0.trace →
      sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x21 = s.readReg64 .x21 →
      sm3.readReg64 .x23 = s.readReg64 .x23 → sm3.readReg64 .x25 = s.readReg64 .x25 →
      sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .x28 = s.readReg64 .x28 → sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm3
        (((optCt1SentPBPinnedAt A g.uc (sp + 4832#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.sendingCt1 (sp + 4960#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A g.receivingEk (sp + 5016#64) receivingEk) ∗ vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F) Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 8560#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h8560 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
      simp +zetaDelta only [bs2, Proto.encodeOptMessage, List.append_nil]
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc : bs1.length + (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 u).length ≤ cap.toNat := by simp +zetaDelta only [bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := entry + 29708#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine step_send_encode_ct1Sent_call b A ext hct1SentEnc (sp + 4832#64) (sp + 1424#64) cap ptr sp (entry + 8560#64) g.uc u bs1 hfit_uc
        (F := optPolynomialEncoderPBPinnedAt A g.sendingCt1 (sp + 4960#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A g.receivingEk (sp + 5016#64) receivingEk ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3)
        (by dsimp only [optCt1SentPBPinnedAt]; ac_rfl) ?_
      intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3; rcases hcsm3 with ⟨hm3_19, _, hm3_21, _, hm3_23, _, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩; simp only [arm64_norm, hm2_19, hm2_21, hm2_23, hm2_25, hm2_27, hm2_28, hm2_fp] at hm3_19 hm3_21 hm3_23 hm3_25 hm3_27 hm3_28 hm3_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h8560 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_21 hm3_23 hm3_25 hm3_27 hm3_28 hm3_fp hinv_m3)
      simp +zetaDelta only [bs2, Proto.encodeOptMessage, optCt1SentPBPinnedAt]; ac_rfl
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx21_3 hx23_3 hx25_3 hx27_3 hx28_3 hfp_3 hinv_3
  set bs3 := bs2 ++ Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 sendingCt1
  suffices h8592 : ∀ sm4 : State,
      sm4.pc = entry + 8592#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = sp + 4704#64 →
      sm4.readReg64 .x21 = s.readReg64 .x21 → sm4.readReg64 .x23 = s.readReg64 .x23 →
      sm4.readReg64 .x25 = s.readReg64 .x25 → sm4.readReg64 .x27 = s.readReg64 .x27 →
      sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm4 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm4
        (((optCt1SentPBPinnedAt A g.uc (sp + 4832#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.sendingCt1 (sp + 4960#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A g.receivingEk (sp + 5016#64) receivingEk) ∗ vecU8At A (sp + 1424#64) cap ptr bs3 ∗ A.pool ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F) Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases sendingCt1 with
    | none =>
      rw [Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (sp + 4960#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 8592#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h8592 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4))
      rw [← Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (sp + 4960#64) none]
      simp +zetaDelta only [bs3, Proto.encodeOptMessage, List.append_nil]
    | some enc =>
      rw [Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (sp + 4960#64) (some enc)]; simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have hfit_enc : bs2.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := entry + 28212#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      rw [← Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (sp + 4960#64) (some enc)]
      refine step_send_encode_polyEncoder_call b A ext hpolyEnc (sp + 4960#64) (sp + 1424#64) cap ptr sp (entry + 8592#64) g.sendingCt1 enc bs2 hfit_enc
        (F := optCt1SentPBPinnedAt A g.uc (sp + 4832#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.receivingEk (sp + 5016#64) receivingEk ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4)
        (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4; rcases hcsm4 with ⟨hm4_19, hm4_20, hm4_21, _, hm4_23, _, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩; simp only [arm64_norm, hx19_3, hx21_3, hx23_3, hx25_3, hx27_3, hx28_3, hfp_3] at hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h8592 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
      simp +zetaDelta only [bs3, Proto.encodeOptMessage, optPolynomialEncoderPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases receivingEk with
  | none =>
    rw [Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (sp + 5016#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
    apply SepWPp.of_sepWP_cs (mid := entry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [← Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (sp + 5016#64) none, encodeInnerState_ct1Sampled_eq]
    simp +zetaDelta only [bs3, bs2, bs1, Proto.encodeOptMessage, chunkedCt1SampledPBPinnedAt,
      List.append_nil, h4960, h5016, List.append_assoc]
  | some dec =>
    rw [Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (sp + 5016#64) (some dec)]; simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs3.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat := by simp +zetaDelta only [bs3, bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := entry + 10352#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    rw [← Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (sp + 5016#64) (some dec)]
    refine step_send_tail_10352_polyDec3 b A ext hfn hpolyDec (sp + 5016#64) sp cap ptr g.receivingEk dec bs3 hfit_dec halign
      (F := optCt1SentPBPinnedAt A g.uc (sp + 4832#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.sendingCt1 (sp + 4960#64) sendingCt1 ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5; simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx25_4, hx27_4, hx28_4, hfp_4] at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [encodeInnerState_ct1Sampled_eq]; simp +zetaDelta only [bs3, bs2, bs1, Proto.encodeOptMessage,
      chunkedCt1SampledPBPinnedAt, optPolynomialDecoderPBPinnedAt,
      h4960, h5016, List.append_assoc]; ac_rfl

/-! ## 3. Variant `idx = 4`: `.ekSentCt1Received` (`+7784 .. +10352`) -/

/-- Step `+7784 .. +6216` (`0x326c4 .. 0x320a4`) for `is = .ekSentCt1Received v`. -/
theorem step_send_v1_ekSentCt1Received {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry)
    {s0 s : State}
    (hekLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 39408#64) (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 38460#64) (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 24012#64) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hekEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 29108#64) (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hpolyDec : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 27844#64) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked4PBGhost × PolynomialDecoderPBGhost)
    (v : V1State.Chunked.EkSentCt1Received) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ekSentCt1Received v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ekSentCt1Received v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 7784#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) v.uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4944#64) v.receivingCt2) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) v.uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4944#64) v.receivingCt2) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.ekSentCt1Received v)) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F) Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches b (Rust.withPanics ext) hfn 7784 7892; send_fetches b (Rust.withPanics ext) hfn 9488 9564; send_fetches b (Rust.withPanics ext) hfn 10296 10352; examples_hide_fetches; subst hP
  rcases v with ⟨uc, receivingCt2⟩
  rw [encodeInnerState_ekSentCt1Received_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x2a#8]).length +
      (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩)))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4944#64) receivingCt2 ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((Prost.EncodeToVec.optEkSentCt1ReceivedCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (Prost.EncodeToVec.optEkSentCt1ReceivedCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((Prost.EncodeToVec.optPolyDecCap g.2 receivingCt2 + 1#64 == 0#64) = !receivingCt2.isSome ∧
      (Prost.EncodeToVec.optPolyDecCap g.2 receivingCt2 + 1#64 != 0#64) = receivingCt2.isSome))
    (fun R' hm =>
      ⟨Prost.EncodeToVec.optEkSentCt1ReceivedPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optPolynomialDecoderPBPinnedAt A g.2 (sp + 4944#64) receivingCt2 ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
       Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_cap_bounds (p := sp + 4944#64)
        (R := optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x2a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack
  suffices h9492 : ∀ sm1 : State,
      sm1.pc = entry + 9492#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = sp + 4704#64 →
      sm1.readReg64 .x21 = s.readReg64 .x21 → sm1.readReg64 .x22 = Prost.EncodeToVec.optEkSentCt1ReceivedCap g.1 uc → sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x26 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm1
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4944#64) receivingCt2) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x2a#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [Prost.EncodeToVec.optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 9492#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h9492 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [optEkSentCt1ReceivedPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
      rw [← Prost.EncodeToVec.optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) none, ← hpack]
    | some u =>
      rw [Prost.EncodeToVec.optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ekSentCt1ReceivedPBEncodedLen u < 2 ^ 64 ∧ optEkSentCt1ReceivedPBFieldEncodedLen (some u) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optEkSentCt1ReceivedPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u)) < optEkSentCt1ReceivedPBFieldEncodedLen (some u) := by dsimp only [optEkSentCt1ReceivedPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ :=
        (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, Prost.EncodeToVec.ult_of_lt_of_fit hvar_u_lt hopt_u_lt, bv_optEkSentCt1Received_some_eq u⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + 39408#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← Prost.EncodeToVec.optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) (some u)]
      refine step_send_leaf_encLen16_call hres b ext (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen hekLen
        (sp + 4840#64) sp (entry + 7848#64) g.1 u hu_fit
        (F := optPolynomialDecoderPBPinnedAt A g.2 (sp + 4944#64) receivingCt2 ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x2a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv1) (by rw [← hpack]; dsimp only [optEkSentCt1ReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1; rcases hcsm1 with ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩; simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
      apply SepWPp.of_sepWP_cs (mid := entry + 9492#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h9492 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
      dsimp only [optEkSentCt1ReceivedPBPinnedAt]; ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 hfp_1 hinv_1
  suffices h10300 : ∀ sm2 : State,
      sm2.pc = entry + 10300#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingCt2) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = sp + 4704#64 →
      sm2.readReg64 .x21 = s.readReg64 .x21 → sm2.readReg64 .x22 = Prost.EncodeToVec.optEkSentCt1ReceivedCap g.1 uc →
      sm2.readReg64 .x23 = s.readReg64 .x23 → sm2.readReg64 .x24 = sp + 4704#64 → sm2.readReg64 .x25 = Prost.EncodeToVec.optPolyDecCap g.2 receivingCt2 →
      sm2.readReg64 .x26 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .x28 = s.readReg64 .x28 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm2
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4944#64) receivingCt2) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x2a#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases receivingCt2 with
    | none =>
      rw [Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.2 (sp + 4944#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 10300#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10300 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2))
      rw [← Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.2 (sp + 4944#64) none]
    | some dec =>
      rw [Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.2 (sp + 4944#64) (some dec)]; simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have ⟨hdec_fit, hopt_d_lt⟩ : polynomialDecoderPBEncodedLen dec < 2 ^ 64 ∧ optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialDecoderPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_d_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) < optPolynomialDecoderPBFieldEncodedLen (some dec) := by dsimp only [optPolynomialDecoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_d, hopt_d_eq⟩ :=
        (⟨EncodedLen.cmp_ls_false_of_lt hvar_d_lt hopt_d_lt, Prost.EncodeToVec.ult_of_lt_of_fit hvar_d_lt hopt_d_lt, bv_optPolyDec_some_eq dec⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + 38460#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.2 (sp + 4944#64) (some dec)]
      refine step_send_leaf_encLen16_call hres b ext (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen hpolyDecLen
        (sp + 4944#64) sp (entry + 9520#64) g.2 dec hdec_fit
        (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x2a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2; rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp, _⟩; simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_26 hm2_27 hm2_28 hm2_fp
      apply SepWPp.of_sepWP_cs (mid := entry + 10300#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10300 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m2.trans hinv3))
      dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen receivingCt2)
      (b := optEkSentCt1ReceivedPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩))
      rfl hsub_len
  apply SepWPp.of_sepWP_cs (mid := entry + 24012#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x2a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩)))
  refine step_send_encode_varint_call b A ext hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩)))
    (sp + 1424#64) cap ptr sp (entry + 10316#64) (bs ++ [0x2a#8]) hfit_var
    (F := (optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4944#64) receivingCt2) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3; rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩; simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_25 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 uc
  suffices h10336 : ∀ sm4 : State,
      sm4.pc = entry + 10336#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x24 = sp + 4704#64 → sm4.readReg64 .x25 = Prost.EncodeToVec.optPolyDecCap g.2 receivingCt2 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm4
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4944#64) receivingCt2) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 10336#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10336 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4))
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc : bs1.length + (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 u).length ≤ cap.toNat := by simp +zetaDelta only [bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := entry + 29108#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine step_send_encode_ekSentCt1Received_call b A ext hekEnc (sp + 4840#64) (sp + 1424#64) cap ptr sp (entry + 10336#64) g.1 u bs1 hfit_uc
        (F := optPolynomialDecoderPBPinnedAt A g.2 (sp + 4944#64) receivingCt2 ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ F) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4)
        (by dsimp only [bs1, optEkSentCt1ReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4; rcases hcsm4 with ⟨hm4_19, _, hm4_21, _, hm4_23, hm4_24, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩; simp only [arm64_norm, hm3_19, hm3_21, hm3_23, hm3_24, hm3_25, hm3_27, hm3_28, hm3_fp] at hm4_19 hm4_21 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10336 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
      simp +zetaDelta only [bs2, Proto.encodeOptMessage, optEkSentCt1ReceivedPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases receivingCt2 with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
    apply SepWPp.of_sepWP_cs (mid := entry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [encodeInnerState_ekSentCt1Received_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat := by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := entry + 10352#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine step_send_tail_10352_polyDec3 b A ext hfn hpolyDec (sp + 4944#64) sp cap ptr g.2 dec bs2 hfit_dec halign
      (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5; simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx27_4, hx28_4, hfp_4] at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [encodeInnerState_ekSentCt1Received_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage,
      optPolynomialDecoderPBPinnedAt, List.append_assoc]; ac_rfl

/-! ## 4. Variant `idx = 9`: `.ct1Acknowledged` (`+7892 .. +11220`) -/

/-- Step `+7892 .. +6216` (`0x32730 .. 0x320a4`) for `is = .ct1Acknowledged v`. -/
theorem step_send_v1_ct1Acknowledged {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry)
    {s0 s : State}
    (hct1SentLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 37204#64) (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 38460#64) (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 24012#64) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 29708#64) (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hpolyDec : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 27844#64) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked5PBGhost × PolynomialDecoderPBGhost)
    (v : V1State.Chunked.Ct1Acknowledged) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ct1Acknowledged v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct1Acknowledged v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 7892#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optCt1SentPBPinnedAt A g.1 (sp + 4840#64) v.uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4968#64) v.receivingEk) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((optCt1SentPBPinnedAt A g.1 (sp + 4840#64) v.uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4968#64) v.receivingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.ct1Acknowledged v)) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F) Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches b (Rust.withPanics ext) hfn 7892 8000; send_fetches b (Rust.withPanics ext) hfn 9564 9640; send_fetches b (Rust.withPanics ext) hfn 10368 10428; examples_hide_fetches; subst hP
  rcases v with ⟨uc, receivingEk⟩
  rw [encodeInnerState_ct1Acknowledged_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x52#8]).length +
      (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩)))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optCt1SentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4968#64) receivingEk ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((Prost.EncodeToVec.optCt1SentCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (Prost.EncodeToVec.optCt1SentCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((Prost.EncodeToVec.optPolyDecCap g.2 receivingEk + 1#64 == 0#64) = !receivingEk.isSome ∧
      (Prost.EncodeToVec.optPolyDecCap g.2 receivingEk + 1#64 != 0#64) = receivingEk.isSome))
    (fun R' hm =>
      ⟨Prost.EncodeToVec.optCt1SentPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optPolynomialDecoderPBPinnedAt A g.2 (sp + 4968#64) receivingEk ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
       Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_cap_bounds (p := sp + 4968#64)
        (R := optCt1SentPBPinnedAt A g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x52#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack
  suffices h9568 : ∀ sm1 : State,
      sm1.pc = entry + 9568#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = sp + 4704#64 →
      sm1.readReg64 .x21 = s.readReg64 .x21 → sm1.readReg64 .x22 = Prost.EncodeToVec.optCt1SentCap g.1 uc → sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x26 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen uc) → sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 →
      sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm1
        (((optCt1SentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4968#64) receivingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x52#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [Prost.EncodeToVec.optCt1SentPBPinnedAt_eq A g.1 (sp + 4840#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 9568#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h9568 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [optCt1SentPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
      rw [← Prost.EncodeToVec.optCt1SentPBPinnedAt_eq A g.1 (sp + 4840#64) none, ← hpack]
    | some u =>
      rw [Prost.EncodeToVec.optCt1SentPBPinnedAt_eq A g.1 (sp + 4840#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ct1SentPBEncodedLen u < 2 ^ 64 ∧ optCt1SentPBFieldEncodedLen (some u) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optCt1SentPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (ct1SentPBEncodedLen u)) < optCt1SentPBFieldEncodedLen (some u) := by dsimp only [optCt1SentPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ :=
        (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, Prost.EncodeToVec.ult_of_lt_of_fit hvar_u_lt hopt_u_lt, bv_optCt1Sent_some_eq u⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + 37204#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← Prost.EncodeToVec.optCt1SentPBPinnedAt_eq A g.1 (sp + 4840#64) (some u)]
      refine step_send_leaf_encLen16_call hres b ext (ct1SentPBPinnedAt A) ct1SentPBEncodedLen hct1SentLen
        (sp + 4840#64) sp (entry + 7956#64) g.1 u hu_fit
        (F := optPolynomialDecoderPBPinnedAt A g.2 (sp + 4968#64) receivingEk ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x52#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv1) (by rw [← hpack]; dsimp only [optCt1SentPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1; rcases hcsm1 with ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩; simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
      apply SepWPp.of_sepWP_cs (mid := entry + 9568#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h9568 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
      dsimp only [optCt1SentPBPinnedAt]; ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 hfp_1 hinv_1
  suffices h10372 : ∀ sm2 : State,
      sm2.pc = entry + 10372#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingEk) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = sp + 4704#64 →
      sm2.readReg64 .x21 = s.readReg64 .x21 → sm2.readReg64 .x22 = Prost.EncodeToVec.optCt1SentCap g.1 uc →
      sm2.readReg64 .x23 = s.readReg64 .x23 → sm2.readReg64 .x24 = sp + 4704#64 → sm2.readReg64 .x25 = Prost.EncodeToVec.optPolyDecCap g.2 receivingEk →
      sm2.readReg64 .x26 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen uc) → sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .x28 = s.readReg64 .x28 →
      sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm2
        (((optCt1SentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4968#64) receivingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x52#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases receivingEk with
    | none =>
      rw [Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.2 (sp + 4968#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 10372#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10372 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2))
      rw [← Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.2 (sp + 4968#64) none]
    | some dec =>
      rw [Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.2 (sp + 4968#64) (some dec)]; simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have ⟨hdec_fit, hopt_d_lt⟩ : polynomialDecoderPBEncodedLen dec < 2 ^ 64 ∧ optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialDecoderPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_d_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) < optPolynomialDecoderPBFieldEncodedLen (some dec) := by dsimp only [optPolynomialDecoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_d, hopt_d_eq⟩ :=
        (⟨EncodedLen.cmp_ls_false_of_lt hvar_d_lt hopt_d_lt, Prost.EncodeToVec.ult_of_lt_of_fit hvar_d_lt hopt_d_lt, bv_optPolyDec_some_eq dec⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + 38460#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.2 (sp + 4968#64) (some dec)]
      refine step_send_leaf_encLen16_call hres b ext (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen hpolyDecLen
        (sp + 4968#64) sp (entry + 9596#64) g.2 dec hdec_fit
        (F := optCt1SentPBPinnedAt A g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x52#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2; rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp, _⟩; simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_26 hm2_27 hm2_28 hm2_fp
      apply SepWPp.of_sepWP_cs (mid := entry + 10372#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10372 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m2.trans hinv3))
      dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen receivingEk)
      (b := optCt1SentPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩))
      rfl hsub_len
  apply SepWPp.of_sepWP_cs (mid := entry + 24012#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x52#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩)))
  refine step_send_encode_varint_call b A ext hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩)))
    (sp + 1424#64) cap ptr sp (entry + 10388#64) (bs ++ [0x52#8]) hfit_var
    (F := (optCt1SentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4968#64) receivingEk) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3; rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩; simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_25 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 uc
  suffices h10408 : ∀ sm4 : State,
      sm4.pc = entry + 10408#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x24 = sp + 4704#64 → sm4.readReg64 .x25 = Prost.EncodeToVec.optPolyDecCap g.2 receivingEk →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm4
        (((optCt1SentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4968#64) receivingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 10408#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10408 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4))
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc : bs1.length + (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 u).length ≤ cap.toNat := by simp +zetaDelta only [bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := entry + 29708#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine step_send_encode_ct1Sent_call b A ext hct1SentEnc (sp + 4840#64) (sp + 1424#64) cap ptr sp (entry + 10408#64) g.1 u bs1 hfit_uc
        (F := optPolynomialDecoderPBPinnedAt A g.2 (sp + 4968#64) receivingEk ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ F) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4)
        (by dsimp only [bs1, optCt1SentPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4; rcases hcsm4 with ⟨hm4_19, _, hm4_21, _, hm4_23, hm4_24, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩; simp only [arm64_norm, hm3_19, hm3_21, hm3_23, hm3_24, hm3_25, hm3_27, hm3_28, hm3_fp] at hm4_19 hm4_21 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10408 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
      simp +zetaDelta only [bs2, Proto.encodeOptMessage, optCt1SentPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases receivingEk with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
    apply SepWPp.of_sepWP_cs (mid := entry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [encodeInnerState_ct1Acknowledged_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat := by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := entry + 11208#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine step_send_tail_11208_polyDec2 b A ext hfn hpolyDec (sp + 4968#64) sp cap ptr g.2 dec bs2 hfit_dec halign
      (F := optCt1SentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5; simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx27_4, hx28_4, hfp_4] at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [encodeInnerState_ct1Acknowledged_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage,
      optPolynomialDecoderPBPinnedAt, List.append_assoc]; ac_rfl

/-! ## 5. Variant `idx = 3`: `.ct1Received` (`+8372 .. +11756`) -/

/-- Step `+8372 .. +6216` (`0x32910 .. 0x320a4`) for `is = .ct1Received v`. -/
theorem step_send_v1_ct1Received {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry)
    {s0 s : State}
    (hekLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 39408#64) (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 34096#64) (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 24012#64) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hekEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 29108#64) (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 28212#64) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked4PBGhost × PolynomialEncoderPBGhost)
    (v : V1State.Chunked.Ct1Received) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ct1Received v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct1Received v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 8372#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) v.uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) v.sendingEk) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) v.uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) v.sendingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.ct1Received v)) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F) Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches b (Rust.withPanics ext) hfn 8372 8480; send_fetches b (Rust.withPanics ext) hfn 9640 9716; send_fetches b (Rust.withPanics ext) hfn 10428 10488; examples_hide_fetches; subst hP
  rcases v with ⟨uc, sendingEk⟩
  rw [encodeInnerState_ct1Received_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x22#8]).length +
      (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩)))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingEk ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((Prost.EncodeToVec.optEkSentCt1ReceivedCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (Prost.EncodeToVec.optEkSentCt1ReceivedCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((Prost.EncodeToVec.optPolyEncCap g.2 sendingEk + 1#64 == 0#64) = !sendingEk.isSome ∧
      (Prost.EncodeToVec.optPolyEncCap g.2 sendingEk + 1#64 != 0#64) = sendingEk.isSome))
    (fun R' hm =>
      ⟨Prost.EncodeToVec.optEkSentCt1ReceivedPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingEk ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
       Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_cap_bounds (p := sp + 4944#64)
        (R := optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x22#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack
  suffices h9644 : ∀ sm1 : State,
      sm1.pc = entry + 9644#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = sp + 4704#64 →
      sm1.readReg64 .x21 = s.readReg64 .x21 → sm1.readReg64 .x22 = Prost.EncodeToVec.optEkSentCt1ReceivedCap g.1 uc → sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x26 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm1
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x22#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [Prost.EncodeToVec.optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 9644#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h9644 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [optEkSentCt1ReceivedPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
      rw [← Prost.EncodeToVec.optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) none, ← hpack]
    | some u =>
      rw [Prost.EncodeToVec.optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ekSentCt1ReceivedPBEncodedLen u < 2 ^ 64 ∧ optEkSentCt1ReceivedPBFieldEncodedLen (some u) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optEkSentCt1ReceivedPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u)) < optEkSentCt1ReceivedPBFieldEncodedLen (some u) := by dsimp only [optEkSentCt1ReceivedPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ :=
        (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, Prost.EncodeToVec.ult_of_lt_of_fit hvar_u_lt hopt_u_lt, bv_optEkSentCt1Received_some_eq u⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + 39408#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← Prost.EncodeToVec.optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) (some u)]
      refine step_send_leaf_encLen16_call hres b ext (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen hekLen
        (sp + 4840#64) sp (entry + 8436#64) g.1 u hu_fit
        (F := optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingEk ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x22#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv1) (by rw [← hpack]; dsimp only [optEkSentCt1ReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1; rcases hcsm1 with ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩; simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
      apply SepWPp.of_sepWP_cs (mid := entry + 9644#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h9644 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
      dsimp only [optEkSentCt1ReceivedPBPinnedAt]; ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 hfp_1 hinv_1
  suffices h10432 : ∀ sm2 : State,
      sm2.pc = entry + 10432#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingEk) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = sp + 4704#64 →
      sm2.readReg64 .x21 = s.readReg64 .x21 → sm2.readReg64 .x22 = Prost.EncodeToVec.optEkSentCt1ReceivedCap g.1 uc →
      sm2.readReg64 .x23 = s.readReg64 .x23 → sm2.readReg64 .x24 = sp + 4704#64 → sm2.readReg64 .x25 = Prost.EncodeToVec.optPolyEncCap g.2 sendingEk →
      sm2.readReg64 .x26 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .x28 = s.readReg64 .x28 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm2
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x22#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases sendingEk with
    | none =>
      rw [Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.2 (sp + 4944#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 10432#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10432 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialEncoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2))
      rw [← Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.2 (sp + 4944#64) none]
    | some enc =>
      rw [Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.2 (sp + 4944#64) (some enc)]; simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have ⟨henc_fit, hopt_e_lt⟩ : polynomialEncoderPBEncodedLen enc < 2 ^ 64 ∧ optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialEncoderPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_e_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc)) < optPolynomialEncoderPBFieldEncodedLen (some enc) := by dsimp only [optPolynomialEncoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_e, hopt_e_eq⟩ :=
        (⟨EncodedLen.cmp_ls_false_of_lt hvar_e_lt hopt_e_lt, Prost.EncodeToVec.ult_of_lt_of_fit hvar_e_lt hopt_e_lt, bv_optPolyEnc_some_eq enc⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + 34096#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.2 (sp + 4944#64) (some enc)]
      refine step_send_leaf_encLen16_call hres b ext (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen hpolyEncLen
        (sp + 4944#64) sp (entry + 9672#64) g.2 enc henc_fit
        (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x22#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2) (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2; rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp, _⟩; simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_26 hm2_27 hm2_28 hm2_fp
      apply SepWPp.of_sepWP_cs (mid := entry + 10432#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10432 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m2.trans hinv3))
      dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen sendingEk)
      (b := optEkSentCt1ReceivedPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩))
      rfl hsub_len
  apply SepWPp.of_sepWP_cs (mid := entry + 24012#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x22#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩)))
  refine step_send_encode_varint_call b A ext hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩)))
    (sp + 1424#64) cap ptr sp (entry + 10448#64) (bs ++ [0x22#8]) hfit_var
    (F := (optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingEk) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3; rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩; simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_25 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 uc
  suffices h10468 : ∀ sm4 : State,
      sm4.pc = entry + 10468#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x24 = sp + 4704#64 → sm4.readReg64 .x25 = Prost.EncodeToVec.optPolyEncCap g.2 sendingEk →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm4
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 10468#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10468 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4))
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc : bs1.length + (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 u).length ≤ cap.toNat := by simp +zetaDelta only [bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := entry + 29108#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine step_send_encode_ekSentCt1Received_call b A ext hekEnc (sp + 4840#64) (sp + 1424#64) cap ptr sp (entry + 10468#64) g.1 u bs1 hfit_uc
        (F := optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingEk ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ F) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4)
        (by dsimp only [bs1, optEkSentCt1ReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4; rcases hcsm4 with ⟨hm4_19, _, hm4_21, _, hm4_23, hm4_24, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩; simp only [arm64_norm, hm3_19, hm3_21, hm3_23, hm3_24, hm3_25, hm3_27, hm3_28, hm3_fp] at hm4_19 hm4_21 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10468 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
      simp +zetaDelta only [bs2, Proto.encodeOptMessage, optEkSentCt1ReceivedPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases sendingEk with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
    apply SepWPp.of_sepWP_cs (mid := entry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [encodeInnerState_ct1Received_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]
  | some enc =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
    have hfit_enc : bs2.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := entry + 11748#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine step_send_tail_11748_polyEnc b A ext hfn hpolyEnc (sp + 4944#64) sp cap ptr g.2 enc bs2 hfit_enc halign
      (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5; simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx27_4, hx28_4, hfp_4] at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [encodeInnerState_ct1Received_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage,
      optPolynomialEncoderPBPinnedAt, List.append_assoc]; ac_rfl

/-! ## 6. `StepSendInnerStateAt6616` Bridges for the 4 Variants -/

theorem step_send_v1_ct1Sampled_at_6616 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry)
    {s0 : State}
    (hct1SampledLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 36916#64) (withStepInv s0 (chunkedCt1SampledEncodedLenPinnedSpec A)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 24012#64) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 29708#64) (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 28212#64) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 27844#64) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.Ct1Sampled) :
    StepSendInnerStateAt6616 resStack b A ext entry roBase s0 (.ct1Sampled v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  send_fetches b (Rust.withPanics ext) hfn 6616 6632; examples_hide_fetches; subst hP
  simp only [v1StateInnerPBPinnedAt, v1StateInnerCap] at hx8 hx20 ⊢
  refine sepWPp_extract_pure
    (((Prost.EncodeToVec.optCt1SentCap g.b.gCt1Sampled.uc v.uc ^^^ 0x8000000000000000#64).ult 11#64) = false)
    (fun R' hm => by
      dsimp only [chunkedCt1SampledPBPinnedAt] at hm
      rw [Prost.EncodeToVec.optCt1SentPBPinnedAt_eq A g.b.gCt1Sampled.uc (sp + 4832#64) v.uc] at hm
      have hm' : s.mem ⊨ Prost.EncodeToVec.optCt1SentRest A g.b.gCt1Sampled.uc (sp + 4832#64) v.uc ∗
          (((sp + 4832#64) ↦₆₄ Prost.EncodeToVec.optCt1SentCap g.b.gCt1Sampled.uc v.uc) ∗
           optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (sp + 4832#64 + 128#64) v.sendingCt1 ∗
           optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (sp + 4832#64 + 184#64) v.receivingEk ∗
           ((sp + 16#64) ↦₆₄ w25) ∗
           (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
           stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
        convert hm using 1; ac_rfl
      exact (Prost.EncodeToVec.optCt1SentRest_disc_bounds hm').2.2)
    fun hult => ?_
  simp only [hult, Bool.false_eq_true, ↓reduceIte] at hx8
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  apply SepWPp.of_sepWP_cs (mid := entry + 8480#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_send_v1_ct1Sampled hres b A ext hfn
    hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec
    sp cap ptr g.b.gCt1Sampled v bs hv_len hfit halign
    (F := ((sp + 16#64) ↦₆₄ w25) ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m; simp only [arm64_norm, hx25] at hm19 hm21 hm23 hm25 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  rw [spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by ac_rfl)

theorem step_send_v1_ekSentCt1Received_at_6616 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry)
    {s0 : State}
    (hekLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 39408#64) (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 38460#64) (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 24012#64) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hekEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 29108#64) (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hpolyDec : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 27844#64) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.EkSentCt1Received) :
    StepSendInnerStateAt6616 resStack b A ext entry roBase s0 (.ekSentCt1Received v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  send_fetches b (Rust.withPanics ext) hfn 6616 6632; examples_hide_fetches; subst hP
  replace hx8 : s.readReg64 .x8 = 4#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  apply SepWPp.of_sepWP_cs (mid := entry + 7784#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have ⟨h4840, h4944⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧ (sp + 4832#64) + 112#64 = sp + 4944#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4944]
  refine step_send_v1_ekSentCt1Received hres b A ext hfn
    hekLen hpolyDecLen hvarint hekEnc hpolyDec
    sp cap ptr w25 g.a.gEkSentCt1Received v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (sp + 4832#64 + 152#64) 72 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m; simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4944, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by ac_rfl)

theorem step_send_v1_ct1Acknowledged_at_6616 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry)
    {s0 : State}
    (hct1SentLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 37204#64) (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 38460#64) (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 24012#64) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 29708#64) (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hpolyDec : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 27844#64) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.Ct1Acknowledged) :
    StepSendInnerStateAt6616 resStack b A ext entry roBase s0 (.ct1Acknowledged v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  send_fetches b (Rust.withPanics ext) hfn 6616 6632; examples_hide_fetches; subst hP
  replace hx8 : s.readReg64 .x8 = 9#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  apply SepWPp.of_sepWP_cs (mid := entry + 7892#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have ⟨h4840, h4968⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧ (sp + 4832#64) + 136#64 = sp + 4968#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4968]
  refine step_send_v1_ct1Acknowledged hres b A ext hfn
    hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec
    sp cap ptr w25 g.b.gCt1Acknowledged v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000009#64) ∗ memRegion (sp + 4832#64 + 176#64) 48 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m; simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4968, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by ac_rfl)

theorem step_send_v1_ct1Received_at_6616 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry)
    {s0 : State}
    (hekLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 39408#64) (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 34096#64) (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 24012#64) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hekEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 29108#64) (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + 28212#64) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (v : V1State.Chunked.Ct1Received) :
    StepSendInnerStateAt6616 resStack b A ext entry roBase s0 (.ct1Received v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  send_fetches b (Rust.withPanics ext) hfn 6616 6632; examples_hide_fetches; subst hP
  replace hx8 : s.readReg64 .x8 = 3#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  apply SepWPp.of_sepWP_cs (mid := entry + 8372#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have ⟨h4840, h4944⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧ (sp + 4832#64) + 112#64 = sp + 4944#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4944]
  refine step_send_v1_ct1Received hres b A ext hfn
    hekLen hpolyEncLen hvarint hekEnc hpolyEnc
    sp cap ptr w25 g.a.gCt1Received v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (sp + 4832#64 + 168#64) 56 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m; simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4944, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Send
