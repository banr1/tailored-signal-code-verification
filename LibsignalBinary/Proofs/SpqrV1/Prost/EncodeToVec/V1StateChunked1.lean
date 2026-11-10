/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import ProofLib.SepLogic.WPp

/-!
# Phase 2c (Part 1): `V1State::encode_raw` Delegating Variants in `PqRatchetState::encode_to_vec`

Proves symbolic execution of the shared `PolynomialEncoder` / `PolynomialDecoder` tails and the
4 delegating `V1State.InnerState` branches in `PqRatchetState::encode_to_vec` (`0x6d010`):
- `idx = 7`: `.ct1Sampled` (`+2620 .. +2748`, `0x6da4c .. 0x6dacc`)
- `idx = 4`: `.ekSentCt1Received` (`+1976 .. +2072`, `+3576 .. +3644`, `+4344 .. +4400`, `+5196 .. +5204`)
- `idx = 9`: `.ct1Acknowledged` (`+2076 .. +2172`, `+3648 .. +3712`, `+4404 .. +4468`)
- `idx = 3`: `.ct1Received` (`+2520 .. +2616`, `+3716 .. +3784`, `+4472 .. +4520`, `+4904 .. +4912`, `+5704 .. +5708`)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

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
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Pure Encoding Unfolding & Arithmetic Lemmas -/

theorem ult_of_lt_of_fit {vlen tot : Nat} (hlt : vlen < tot) (htot : tot < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 vlen) (BitVec.ofNat 64 tot) = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64), Nat.mod_eq_of_lt htot]
  omega

theorem bv_optEkSentCt1Received_some_eq (u : V1State.Unchunked.EkSentCt1Received) :
    BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u) +
      BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen (some u)) := by
  dsimp only [optEkSentCt1ReceivedPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add]; congr 1; omega

theorem bv_optCt1Sent_some_eq (u : V1State.Unchunked.Ct1Sent) :
    BitVec.ofNat 64 (ct1SentPBEncodedLen u) +
      BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (ct1SentPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen (some u)) := by
  dsimp only [optCt1SentPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add]; congr 1; omega

theorem bv_optPolyDec_some_eq (dec : PolynomialDecoder) :
    BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec) +
      BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec))) + 1#64 =
      BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen (some dec)) := by
  dsimp only [optPolynomialDecoderPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add]; congr 1; omega

theorem bv_optPolyEnc_some_eq (enc : PolynomialEncoder) :
    BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc) +
      BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc))) + 1#64 =
      BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen (some enc)) := by
  dsimp only [optPolynomialEncoderPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add]; congr 1; omega

theorem encodeInnerState_ct1Sampled_eq (v : V1State.Chunked.Ct1Sampled) :
    V1State.InnerState.encode (.ct1Sampled v) =
      ((([0x42#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen v))) ++
        Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 v.uc) ++
        Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingCt1) ++
        Proto.encodeOptMessage PolynomialDecoder.encodeRaw 3#32 v.receivingEk := by
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 8#32 .lengthDelimited = [0x42#8] from rfl,
    ← V1State.Chunked.Ct1Sampled.encodedLen, chunkedCt1SampledPBEncodedLen_eq_proto]
  dsimp only [V1State.Chunked.Ct1Sampled.encodeRaw]
  simp only [List.append_assoc]

theorem encodeInnerState_ekSentCt1Received_eq (v : V1State.Chunked.EkSentCt1Received) :
    V1State.InnerState.encode (.ekSentCt1Received v) =
      (([0x2a#8] ++
        Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 v.uc) ++
        Proto.encodeOptMessage PolynomialDecoder.encodeRaw 3#32 v.receivingCt2 := by
  have hlen : (V1State.Chunked.EkSentCt1Received.encodeRaw v).length =
      v1StateInnerPayloadEncodedLen (.ekSentCt1Received v) := by
    dsimp only [V1State.Chunked.EkSentCt1Received.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append,
      optEkSentCt1ReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
      optPolynomialDecoderPBFieldEncodedLen_eq_proto 3#32 v.receivingCt2 ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 5#32 .lengthDelimited = [0x2a#8] from rfl, hlen]; dsimp only [V1State.Chunked.EkSentCt1Received.encodeRaw]
  simp only [List.append_assoc]

theorem encodeInnerState_ct1Acknowledged_eq (v : V1State.Chunked.Ct1Acknowledged) :
    V1State.InnerState.encode (.ct1Acknowledged v) =
      (([0x52#8] ++
        Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 v.uc) ++
        Proto.encodeOptMessage PolynomialDecoder.encodeRaw 2#32 v.receivingEk := by
  have hlen : (V1State.Chunked.Ct1Acknowledged.encodeRaw v).length =
      v1StateInnerPayloadEncodedLen (.ct1Acknowledged v) := by
    dsimp only [V1State.Chunked.Ct1Acknowledged.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append,
      optCt1SentPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
      optPolynomialDecoderPBFieldEncodedLen_eq_proto 2#32 v.receivingEk ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 10#32 .lengthDelimited = [0x52#8] from rfl, hlen]; dsimp only [V1State.Chunked.Ct1Acknowledged.encodeRaw]
  simp only [List.append_assoc]

theorem encodeInnerState_ct1Received_eq (v : V1State.Chunked.Ct1Received) :
    V1State.InnerState.encode (.ct1Received v) =
      (([0x22#8] ++
        Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 v.uc) ++
        Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingEk := by
  have hlen : (V1State.Chunked.Ct1Received.encodeRaw v).length =
      v1StateInnerPayloadEncodedLen (.ct1Received v) := by
    dsimp only [V1State.Chunked.Ct1Received.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append,
      optEkSentCt1ReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
      optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 v.sendingEk ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 4#32 .lengthDelimited = [0x22#8] from rfl, hlen]; dsimp only [V1State.Chunked.Ct1Received.encodeRaw]
  simp only [List.append_assoc]

/-! ## 2. Shared `PolynomialDecoder` / `PolynomialEncoder` Tail Blocks -/

/-- Step `+2732 .. +1808` (`0x6dabc .. 0x6d720`): calls `encode<PolynomialDecoder>` (`0x52544`)
with `w0 = 3#32`, `x1 = dec_ptr`, `x2 = sp - 120#64`, then branches to `+1808`. -/
theorem step_encodeToVec_tail_2732_polyDec3 {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hpolyDec : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (dec_ptr sp cap ptr : BitVec 64) (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 2732#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = dec_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialDecoderPBPinnedAt A g dec_ptr dec ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((polynomialDecoderPBPinnedAt A g dec_ptr dec ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 2732 2748; examples_hide_fetches; subst hP
  apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709442356#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_etv_encode_polyDecoder_call b A ext hpolyDec 3#32 dec_ptr (sp - 120#64) cap ptr sp (entry + 2744#64) g dec bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨_, _, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm] at hm27 hmfp
  apply SepWPp.of_sepWP_cs (mid := entry + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2)

/-- Step `+4456 .. +1808` (`0x6e178 .. 0x6d720`): calls `encode<PolynomialDecoder>` (`0x52544`)
with `w0 = 2#32`, `x1 = dec_ptr`, `x2 = sp - 120#64`, then branches to `+1808`. -/
theorem step_encodeToVec_tail_4456_polyDec2 {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hpolyDec : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (dec_ptr sp cap ptr : BitVec 64) (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 4456#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = dec_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialDecoderPBPinnedAt A g dec_ptr dec ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((polynomialDecoderPBPinnedAt A g dec_ptr dec ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw 2#32 dec) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 4456 4472; examples_hide_fetches; subst hP
  apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709442356#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_etv_encode_polyDecoder_call b A ext hpolyDec 2#32 dec_ptr (sp - 120#64) cap ptr sp (entry + 4468#64) g dec bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨_, _, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm] at hm27 hmfp
  apply SepWPp.of_sepWP_cs (mid := entry + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2)

/-- Step `+5196 .. +1808` (`0x6e45c .. 0x6d720`): sets `x1 = x21`, calls `encode<PolynomialDecoder>`
(`0x52544`) with `w0 = tag`, `x1 = dec_ptr`, `x2 = sp - 120#64`, then branches to `+1808`. -/
theorem step_encodeToVec_tail_5196_polyDec {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hpolyDec : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (tag : BitVec 32) (dec_ptr sp cap ptr : BitVec 64) (g : PolynomialDecoderPBGhost)
    (dec : PolynomialDecoder) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw tag dec).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 5196#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hw0 : (s.readReg64 .x0).truncate 32 = tag) (hx2 : s.readReg64 .x2 = sp - 120#64)
    (hx21 : s.readReg64 .x21 = dec_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialDecoderPBPinnedAt A g dec_ptr dec ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((polynomialDecoderPBPinnedAt A g dec_ptr dec ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw tag dec) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 5196 5208; examples_hide_fetches; subst hP
  apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709442356#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_etv_encode_polyDecoder_call b A ext hpolyDec tag dec_ptr (sp - 120#64) cap ptr sp (entry + 5204#64) g dec bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [State.readReg32, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨_, _, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm] at hm27 hmfp
  apply SepWPp.of_sepWP_cs (mid := entry + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2)

/-- Step `+5700 .. +1808` (`0x6e654 .. 0x6d720`): sets `x1 = sp - 120#64`, calls
`encode<PolynomialEncoder>` (`0x526d4`) with `x0 = enc_ptr`, `x1 = sp - 120#64`, then branches to `+1808`. -/
theorem step_encodeToVec_tail_5700_polyEnc {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hpolyEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (enc_ptr sp cap ptr : BitVec 64) (g : PolynomialEncoderPBGhost) (enc : PolynomialEncoder)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 5700#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = enc_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialEncoderPBPinnedAt A g enc_ptr enc ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((polynomialEncoderPBPinnedAt A g enc_ptr enc ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 5700 5712; examples_hide_fetches; subst hP
  apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709442756#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_etv_encode_polyEncoder_call b A ext hpolyEnc enc_ptr (sp - 120#64) cap ptr sp (entry + 5708#64) g enc bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨_, _, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm] at hm27 hmfp
  apply SepWPp.of_sepWP_cs (mid := entry + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2)

/-! ## 3. Variant `idx = 7`: `.ct1Sampled` (`+2620 .. +2748`, `0x6da4c .. 0x6dacc`) -/

/-- Step `+2620 .. +1808` (`0x6da4c .. 0x6d720`) for `is = .ct1Sampled v`. -/
theorem step_encodeToVec_v1_ct1Sampled {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hct1SampledLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709534032#64)
      (withStepInv s0 (chunkedCt1SampledEncodedLenPinnedSpec A)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709444388#64)
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : ChunkedCt1SampledPBGhost) (v : V1State.Chunked.Ct1Sampled)
    (bs : List (BitVec 8)) (hv_len : v1StatePBEncodedLen ⟨some (.ct1Sampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct1Sampled v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 2620#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx28 : s.readReg64 .x28 = optCt1SentCap g.uc v.uc) (hinv0 : StepInv s0 s)
    (hP : P = (chunkedCt1SampledPBPinnedAt A g (a + 128#64) v ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((chunkedCt1SampledPBPinnedAt A g (a + 128#64) v ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.ct1Sampled v)) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 2620 2748; examples_hide_fetches; subst hP
  rcases v with ⟨uc, sendingCt1, receivingEk⟩
  rw [encodeInnerState_ct1Sampled_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩ < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x42#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩))).length ≤ cap.toNat := by simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := chunkedCt1SampledPBPinnedAt A g (a + 128#64) ⟨uc, sendingCt1, receivingEk⟩ ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 := ⟨by bv_omega, by bv_omega⟩
  rw [h112, h104]
  apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709534032#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x42#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  refine step_etv_chunked_encLen48_call hres b ext (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen hct1SampledLen
    (a + 128#64) sp (entry + 2664#64) g ⟨uc, sendingCt1, receivingEk⟩ hsub_len
    (F := vecU8At A (sp - 120#64) cap ptr (bs ++ [0x42#8]) ∗ A.pool ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by rw [← hpack]; ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨_, hm20, hm21, _, _, _, _, _, hm27, hm28, hmfp, _⟩; simp only [arm64_norm, hx20, hx21, hx28] at hm20 hm21 hm27 hm28 hmfp
  apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  set bs1 := (bs ++ [0x42#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩))
  refine step_etv_encode_varint_call b A ext hvarint (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩)) (sp - 120#64) cap ptr sp (entry + 2672#64)
    (bs ++ [0x42#8]) hfit_var (F := chunkedCt1SampledPBPinnedAt A g (a + 128#64) ⟨uc, sendingCt1, receivingEk⟩ ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2) (by ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
  rcases hcsm2 with ⟨_, hm2_20, hm2_21, _, _, _, _, _, hm2_27, hm2_28, hm2_fp, _⟩; simp only [arm64_norm, hm20, hm21, hm27, hm28, hmfp] at hm2_20 hm2_21 hm2_27 hm2_28 hm2_fp
  have h128_128 : (a + 128#64) + 128#64 = a + 256#64 := by bv_omega
  have h128_184 : (a + 128#64) + 184#64 = a + 312#64 := by bv_omega
  refine SepWPp.weaken_pre
    (P' := ((optCt1SentPBPinnedAt A g.uc (a + 128#64) uc ∗
      optPolynomialEncoderPBPinnedAt A g.sendingCt1 (a + 256#64) sendingCt1 ∗
      optPolynomialDecoderPBPinnedAt A g.receivingEk (a + 312#64) receivingEk) ∗
      vecU8At A (sp - 120#64) cap ptr bs1 ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (Entails.of_eq (by dsimp +zetaDelta only [chunkedCt1SampledPBPinnedAt]; rw [h128_128, h128_184]; ac_rfl)) ?_
  refine sepWPp_extract_pure
    (((optCt1SentCap g.uc uc + 1#64 == 0#64) = !uc.isSome ∧
      (optCt1SentCap g.uc uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyEncCap g.sendingCt1 sendingCt1 + 1#64 == 0#64) = !sendingCt1.isSome ∧
      (optPolyEncCap g.sendingCt1 sendingCt1 + 1#64 != 0#64) = sendingCt1.isSome) ∧
     ((optPolyDecCap g.receivingEk receivingEk + 1#64 == 0#64) = !receivingEk.isSome ∧
      (optPolyDecCap g.receivingEk receivingEk + 1#64 != 0#64) = receivingEk.isSome))
    (fun R' hm =>
      ⟨optCt1SentPBPinnedAt_cap_bounds (p := a + 128#64)
        (R := optPolynomialEncoderPBPinnedAt A g.sendingCt1 (a + 256#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A g.receivingEk (a + 312#64) receivingEk ∗
          vecU8At A (sp - 120#64) cap ptr bs1 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
       optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 256#64)
        (R := optCt1SentPBPinnedAt A g.uc (a + 128#64) uc ∗
          optPolynomialDecoderPBPinnedAt A g.receivingEk (a + 312#64) receivingEk ∗
          vecU8At A (sp - 120#64) cap ptr bs1 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
       optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 312#64)
        (R := optCt1SentPBPinnedAt A g.uc (a + 128#64) uc ∗
          optPolynomialEncoderPBPinnedAt A g.sendingCt1 (a + 256#64) sendingCt1 ∗
          vecU8At A (sp - 120#64) cap ptr bs1 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 uc
  suffices h2692 : ∀ sm3 : State,
      sm3.pc = entry + 2692#64 → sm3.status = .Running → sm3.sp = sp - 144#64 → sm3.trace = s0.trace →
      sm3.readReg64 .x20 = a → sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm3 →
      SepWPp (spqrProgAtExt b ext) ret sm3
        (((optCt1SentPBPinnedAt A g.uc (a + 128#64) uc ∗
          optPolynomialEncoderPBPinnedAt A g.sendingCt1 (a + 256#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A g.receivingEk (a + 312#64) receivingEk) ∗
          vecU8At A (sp - 120#64) cap ptr bs2 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 2692#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h2692 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
      simp +zetaDelta only [bs2, Proto.encodeOptMessage, List.append_nil]
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc : bs1.length + (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 u).length ≤ cap.toNat := by simp +zetaDelta only [bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709444388#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine step_etv_encode_ct1Sent_call b A ext hct1SentEnc (a + 128#64) (sp - 120#64) cap ptr sp (entry + 2692#64) g.uc u bs1 hfit_uc
        (F := optPolynomialEncoderPBPinnedAt A g.sendingCt1 (a + 256#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A g.receivingEk (a + 312#64) receivingEk ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3)
        (by dsimp only [optCt1SentPBPinnedAt]; ac_rfl) ?_
      intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
      rcases hcsm3 with ⟨_, hm3_20, _, _, _, _, _, _, hm3_27, _, hm3_fp, _⟩; simp only [arm64_norm, hm2_20, hm2_27, hm2_fp] at hm3_20 hm3_27 hm3_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h2692 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_20 hm3_27 hm3_fp hinv_m3)
      simp +zetaDelta only [bs2, Proto.encodeOptMessage, optCt1SentPBPinnedAt]; ac_rfl
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx20_3 hx27_3 hfp_3 hinv_3
  set bs3 := bs2 ++ Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 sendingCt1
  suffices h2716 : ∀ sm4 : State,
      sm4.pc = entry + 2716#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x20 = a → sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm4 →
      SepWPp (spqrProgAtExt b ext) ret sm4
        (((optCt1SentPBPinnedAt A g.uc (a + 128#64) uc ∗
          optPolynomialEncoderPBPinnedAt A g.sendingCt1 (a + 256#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A g.receivingEk (a + 312#64) receivingEk) ∗
          vecU8At A (sp - 120#64) cap ptr bs3 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases sendingCt1 with
    | none =>
      rw [optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (a + 256#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 2716#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h2716 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4))
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (a + 256#64) none]; simp +zetaDelta only [bs3, Proto.encodeOptMessage, List.append_nil]
    | some enc =>
      rw [optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (a + 256#64) (some enc)]; simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have hfit_enc : bs2.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709442756#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (a + 256#64) (some enc)]
      refine step_etv_encode_polyEncoder_call b A ext hpolyEnc (a + 256#64) (sp - 120#64) cap ptr sp (entry + 2716#64) g.sendingCt1 enc bs2 hfit_enc
        (F := optCt1SentPBPinnedAt A g.uc (a + 128#64) uc ∗
          optPolynomialDecoderPBPinnedAt A g.receivingEk (a + 312#64) receivingEk ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4)
        (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
      rcases hcsm4 with ⟨_, hm4_20, _, _, _, _, _, _, hm4_27, _, hm4_fp, _⟩; simp only [arm64_norm, hx20_3, hx27_3, hfp_3] at hm4_20 hm4_27 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h2716 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_20 hm4_27 hm4_fp hinv_m4)
      simp +zetaDelta only [bs3, Proto.encodeOptMessage, optPolynomialEncoderPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx20_4 hx27_4 hfp_4 hinv_4
  cases receivingEk with
  | none =>
    rw [optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (a + 312#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
    apply SepWPp.of_sepWP_cs (mid := entry + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [← optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (a + 312#64) none, encodeInnerState_ct1Sampled_eq]; simp +zetaDelta only [bs3, bs2, bs1, Proto.encodeOptMessage, chunkedCt1SampledPBPinnedAt,
      List.append_nil, h128_128, h128_184, List.append_assoc]
  | some dec =>
    rw [optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (a + 312#64) (some dec)]; simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs3.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat := by simp +zetaDelta only [bs3, bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := entry + 2732#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    rw [← optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (a + 312#64) (some dec)]
    refine step_encodeToVec_tail_2732_polyDec3 b A ext hfn hpolyDec (a + 312#64) sp cap ptr g.receivingEk dec bs3 hfit_dec halign
      (F := optCt1SentPBPinnedAt A g.uc (a + 128#64) uc ∗
        optPolynomialEncoderPBPinnedAt A g.sendingCt1 (a + 256#64) sendingCt1 ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5
    simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5)
    rw [encodeInnerState_ct1Sampled_eq]; simp +zetaDelta only [bs3, bs2, bs1, Proto.encodeOptMessage,
      chunkedCt1SampledPBPinnedAt, optPolynomialDecoderPBPinnedAt,
      h128_128, h128_184, List.append_assoc]; ac_rfl

/-! ## 4. Variant `idx = 4`: `.ekSentCt1Received` (`+1976 .. +5204`) -/

/-- Step `+1976 .. +1808` (`0x6d7c8 .. 0x6d720`) for `is = .ekSentCt1Received v`. -/
theorem step_encodeToVec_v1_ekSentCt1Received {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hekLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709549660#64)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709536996#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hekEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709443724#64)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hpolyDec : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : Unchunked4PBGhost × PolynomialDecoderPBGhost)
    (v : V1State.Chunked.EkSentCt1Received) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ekSentCt1Received v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ekSentCt1Received v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1976#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) v.receivingCt2) ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) v.uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) v.receivingCt2) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.ekSentCt1Received v)) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1976 2076; etv_fetches b (Rust.withPanics ext) hfn 3576 3648
  etv_fetches b (Rust.withPanics ext) hfn 4344 4404
  examples_hide_fetches; subst hP
  rcases v with ⟨uc, receivingCt2⟩
  rw [encodeInnerState_ekSentCt1Received_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x2a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩)))).length ≤ cap.toNat := by simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) receivingCt2 ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optEkSentCt1ReceivedCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (optEkSentCt1ReceivedCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyDecCap g.2 receivingCt2 + 1#64 == 0#64) = !receivingCt2.isSome ∧
      (optPolyDecCap g.2 receivingCt2 + 1#64 != 0#64) = receivingCt2.isSome))
    (fun R' hm =>
      ⟨optEkSentCt1ReceivedPBPinnedAt_cap_bounds (p := a + 136#64)
        (R := optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) receivingCt2 ∗
          vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
       optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 240#64)
        (R := optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x2a#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  suffices h3580 : ∀ sm1 : State,
      sm1.pc = entry + 3580#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = optEkSentCt1ReceivedCap g.1 uc → sm1.readReg64 .x20 = a →
      sm1.readReg64 .x23 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrProgAtExt b ext) ret sm1
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) receivingCt2) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x2a#8]) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 3580#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3580 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [optEkSentCt1ReceivedPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
      rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) none, ← hpack]
    | some u =>
      rw [optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ekSentCt1ReceivedPBEncodedLen u < 2 ^ 64 ∧ optEkSentCt1ReceivedPBFieldEncodedLen (some u) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optEkSentCt1ReceivedPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u)) < optEkSentCt1ReceivedPBFieldEncodedLen (some u) := by dsimp only [optEkSentCt1ReceivedPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt, bv_optEkSentCt1Received_some_eq u⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709549660#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) (some u)]
      refine step_etv_leaf_encLen16_call hres b ext (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen hekLen
        (a + 136#64) sp (entry + 2032#64) g.1 u hu_fit
        (F := optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) receivingCt2 ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x2a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
        (by rw [← hpack]; dsimp only [optEkSentCt1ReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
      rcases hcsm1 with ⟨hm19, hm20, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm, hx20] at hm19 hm20 hm27 hmfp
      apply SepWPp.of_sepWP_cs (mid := entry + 3580#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3580 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
      dsimp only [optEkSentCt1ReceivedPBPinnedAt]; ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx23_1 hx27_1 hfp_1 hinv_1
  suffices h4348 : ∀ sm2 : State,
      sm2.pc = entry + 4348#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingCt2) →
      sm2.readReg64 .x19 = optEkSentCt1ReceivedCap g.1 uc →
      sm2.readReg64 .x20 = a → sm2.readReg64 .x21 = a + 240#64 →
      sm2.readReg64 .x22 = optPolyDecCap g.2 receivingCt2 →
      sm2.readReg64 .x23 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrProgAtExt b ext) ret sm2
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) receivingCt2) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x2a#8]) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases receivingCt2 with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 240#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 4348#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4348 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2))
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 240#64) none]
    | some dec =>
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 240#64) (some dec)]; simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have ⟨hdec_fit, hopt_d_lt⟩ : polynomialDecoderPBEncodedLen dec < 2 ^ 64 ∧ optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialDecoderPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_d_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) < optPolynomialDecoderPBFieldEncodedLen (some dec) := by dsimp only [optPolynomialDecoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_d, hopt_d_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_d_lt hopt_d_lt, ult_of_lt_of_fit hvar_d_lt hopt_d_lt, bv_optPolyDec_some_eq dec⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709536996#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 240#64) (some dec)]
      refine step_etv_leaf_encLen16_call hres b ext (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen hpolyDecLen
        (a + 240#64) sp (entry + 3604#64) g.2 dec hdec_fit
        (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x2a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2)
        (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, _, _, hm2_27, _, hm2_fp, _⟩; simp only [arm64_norm, hx19_1, hx20_1, hx23_1, hx27_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_27 hm2_fp
      apply SepWPp.of_sepWP_cs (mid := entry + 4348#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4348 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
      dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx27_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen receivingCt2)
      (b := optEkSentCt1ReceivedPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩))
      rfl hsub_len
  apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x2a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩)))
  refine step_etv_encode_varint_call b A ext hvarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩)))
    (sp - 120#64) cap ptr sp (entry + 4364#64) (bs ++ [0x2a#8]) hfit_var
    (F := (optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) receivingCt2) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, _, _, _, _, hm3_27, _, hm3_fp, _⟩; simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx27_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_27 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 uc
  suffices h4384 : ∀ sm4 : State,
      sm4.pc = entry + 4384#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x21 = a + 240#64 → sm4.readReg64 .x22 = optPolyDecCap g.2 receivingCt2 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrProgAtExt b ext) ret sm4
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) receivingCt2) ∗
          vecU8At A (sp - 120#64) cap ptr bs2 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 4384#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4384 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4))
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc : bs1.length + (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 u).length ≤ cap.toNat := by simp +zetaDelta only [bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709443724#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine step_etv_encode_ekSentCt1Received_call b A ext hekEnc (a + 136#64) (sp - 120#64) cap ptr sp (entry + 4384#64) g.1 u bs1 hfit_uc
        (F := optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) receivingCt2 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4)
        (by dsimp only [bs1, optEkSentCt1ReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
      rcases hcsm4 with ⟨_, _, hm4_21, hm4_22, _, _, _, _, hm4_27, _, hm4_fp, _⟩; simp only [arm64_norm, hm3_21, hm3_22, hm3_27, hm3_fp] at hm4_21 hm4_22 hm4_27 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4384 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_21 hm4_22 hm4_27 hm4_fp hinv_m4)
      simp +zetaDelta only [bs2, Proto.encodeOptMessage, optEkSentCt1ReceivedPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx21_4 hx22_4 hx27_4 hfp_4 hinv_4
  cases receivingCt2 with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
    apply SepWPp.of_sepWP_cs (mid := entry + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [encodeInnerState_ekSentCt1Received_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat := by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := entry + 5196#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine step_encodeToVec_tail_5196_polyDec b A ext hfn hpolyDec 3#32 (a + 240#64) sp cap ptr g.2 dec bs2 hfit_dec halign
      (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5
    simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5)
    rw [encodeInnerState_ekSentCt1Received_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage,
      optPolynomialDecoderPBPinnedAt, List.append_assoc]; ac_rfl

/-! ## 5. Variant `idx = 9`: `.ct1Acknowledged` (`+2076 .. +4468`) -/

/-- Step `+2076 .. +1808` (`0x6d82c .. 0x6d720`) for `is = .ct1Acknowledged v`. -/
theorem step_encodeToVec_v1_ct1Acknowledged {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hct1SentLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709534512#64)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709536996#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709444388#64)
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hpolyDec : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : Unchunked5PBGhost × PolynomialDecoderPBGhost)
    (v : V1State.Chunked.Ct1Acknowledged) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ct1Acknowledged v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct1Acknowledged v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 2076#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optCt1SentPBPinnedAt A g.1 (a + 136#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) v.receivingEk) ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        (((optCt1SentPBPinnedAt A g.1 (a + 136#64) v.uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) v.receivingEk) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.ct1Acknowledged v)) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 2076 2176; etv_fetches b (Rust.withPanics ext) hfn 3648 3716
  etv_fetches b (Rust.withPanics ext) hfn 4404 4460
  examples_hide_fetches; subst hP
  rcases v with ⟨uc, receivingEk⟩
  rw [encodeInnerState_ct1Acknowledged_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x52#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩)))).length ≤ cap.toNat := by simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) receivingEk ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optCt1SentCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (optCt1SentCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyDecCap g.2 receivingEk + 1#64 == 0#64) = !receivingEk.isSome ∧
      (optPolyDecCap g.2 receivingEk + 1#64 != 0#64) = receivingEk.isSome))
    (fun R' hm =>
      ⟨optCt1SentPBPinnedAt_cap_bounds (p := a + 136#64)
        (R := optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) receivingEk ∗
          vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
       optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 264#64)
        (R := optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗
          vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x52#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  suffices h3652 : ∀ sm1 : State,
      sm1.pc = entry + 3652#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = optCt1SentCap g.1 uc → sm1.readReg64 .x20 = a →
      sm1.readReg64 .x22 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrProgAtExt b ext) ret sm1
        (((optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) receivingEk) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x52#8]) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optCt1SentPBPinnedAt_eq A g.1 (a + 136#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 3652#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3652 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [optCt1SentPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
      rw [← optCt1SentPBPinnedAt_eq A g.1 (a + 136#64) none, ← hpack]
    | some u =>
      rw [optCt1SentPBPinnedAt_eq A g.1 (a + 136#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ct1SentPBEncodedLen u < 2 ^ 64 ∧ optCt1SentPBFieldEncodedLen (some u) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optCt1SentPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (ct1SentPBEncodedLen u)) < optCt1SentPBFieldEncodedLen (some u) := by dsimp only [optCt1SentPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt, bv_optCt1Sent_some_eq u⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709534512#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← optCt1SentPBPinnedAt_eq A g.1 (a + 136#64) (some u)]
      refine step_etv_leaf_encLen16_call hres b ext (ct1SentPBPinnedAt A) ct1SentPBEncodedLen hct1SentLen
        (a + 136#64) sp (entry + 2132#64) g.1 u hu_fit
        (F := optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) receivingEk ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x52#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
        (by rw [← hpack]; dsimp only [optCt1SentPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
      rcases hcsm1 with ⟨hm19, hm20, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm, hx20] at hm19 hm20 hm27 hmfp
      apply SepWPp.of_sepWP_cs (mid := entry + 3652#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3652 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
      dsimp only [optCt1SentPBPinnedAt]; ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx22_1 hx27_1 hfp_1 hinv_1
  suffices h4408 : ∀ sm2 : State,
      sm2.pc = entry + 4408#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingEk) →
      sm2.readReg64 .x19 = optCt1SentCap g.1 uc →
      sm2.readReg64 .x20 = a → sm2.readReg64 .x21 = optPolyDecCap g.2 receivingEk →
      sm2.readReg64 .x22 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrProgAtExt b ext) ret sm2
        (((optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) receivingEk) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x52#8]) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases receivingEk with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 264#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 4408#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4408 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2))
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 264#64) none]
    | some dec =>
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 264#64) (some dec)]; simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have ⟨hdec_fit, hopt_d_lt⟩ : polynomialDecoderPBEncodedLen dec < 2 ^ 64 ∧ optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialDecoderPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_d_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) < optPolynomialDecoderPBFieldEncodedLen (some dec) := by dsimp only [optPolynomialDecoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_d, hopt_d_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_d_lt hopt_d_lt, ult_of_lt_of_fit hvar_d_lt hopt_d_lt, bv_optPolyDec_some_eq dec⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709536996#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 264#64) (some dec)]
      refine step_etv_leaf_encLen16_call hres b ext (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen hpolyDecLen
        (a + 264#64) sp (entry + 3672#64) g.2 dec hdec_fit
        (F := optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x52#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2)
        (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, _, _, _, _, hm2_27, _, hm2_fp, _⟩; simp only [arm64_norm, hx19_1, hx20_1, hx22_1, hx27_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_27 hm2_fp
      apply SepWPp.of_sepWP_cs (mid := entry + 4408#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4408 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
      dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx27_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen receivingEk)
      (b := optCt1SentPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩))
      rfl hsub_len
  apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x52#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩)))
  refine step_etv_encode_varint_call b A ext hvarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩)))
    (sp - 120#64) cap ptr sp (entry + 4424#64) (bs ++ [0x52#8]) hfit_var
    (F := (optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) receivingEk) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, _, _, _, _, _, hm3_27, _, hm3_fp, _⟩; simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx27_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_27 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 uc
  suffices h4444 : ∀ sm4 : State,
      sm4.pc = entry + 4444#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x20 = a → sm4.readReg64 .x21 = optPolyDecCap g.2 receivingEk →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrProgAtExt b ext) ret sm4
        (((optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) receivingEk) ∗
          vecU8At A (sp - 120#64) cap ptr bs2 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 4444#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4444 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4))
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc : bs1.length + (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 u).length ≤ cap.toNat := by simp +zetaDelta only [bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709444388#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine step_etv_encode_ct1Sent_call b A ext hct1SentEnc (a + 136#64) (sp - 120#64) cap ptr sp (entry + 4444#64) g.1 u bs1 hfit_uc
        (F := optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) receivingEk ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4)
        (by dsimp only [bs1, optCt1SentPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
      rcases hcsm4 with ⟨_, hm4_20, hm4_21, _, _, _, _, _, hm4_27, _, hm4_fp, _⟩; simp only [arm64_norm, hm3_20, hm3_21, hm3_27, hm3_fp] at hm4_20 hm4_21 hm4_27 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4444 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_20 hm4_21 hm4_27 hm4_fp hinv_m4)
      simp +zetaDelta only [bs2, Proto.encodeOptMessage, optCt1SentPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx20_4 hx21_4 hx27_4 hfp_4 hinv_4
  cases receivingEk with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
    apply SepWPp.of_sepWP_cs (mid := entry + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [encodeInnerState_ct1Acknowledged_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat := by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := entry + 4456#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine step_encodeToVec_tail_4456_polyDec2 b A ext hfn hpolyDec (a + 264#64) sp cap ptr g.2 dec bs2 hfit_dec halign
      (F := optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5
    simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5)
    rw [encodeInnerState_ct1Acknowledged_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage,
      optPolynomialDecoderPBPinnedAt, List.append_assoc]; ac_rfl

/-! ## 6. Variant `idx = 3`: `.ct1Received` (`+2520 .. +5708`) -/

/-- Step `+2520 .. +1808` (`0x6d9e8 .. 0x6d720`) for `is = .ct1Received v`. -/
theorem step_encodeToVec_v1_ct1Received {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hekLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709549660#64)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709525468#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hekEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709443724#64)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : Unchunked4PBGhost × PolynomialEncoderPBGhost)
    (v : V1State.Chunked.Ct1Received) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ct1Received v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct1Received v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 2520#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) v.sendingEk) ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) v.uc ∗
          optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) v.sendingEk) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.ct1Received v)) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 2520 2620; etv_fetches b (Rust.withPanics ext) hfn 3716 3788
  etv_fetches b (Rust.withPanics ext) hfn 4472 4524; etv_fetches b (Rust.withPanics ext) hfn 4904 4916
  etv_fetches b (Rust.withPanics ext) hfn 5704 5712
  examples_hide_fetches; subst hP
  rcases v with ⟨uc, sendingEk⟩
  rw [encodeInnerState_ct1Received_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x22#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩)))).length ≤ cap.toNat := by simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) sendingEk ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optEkSentCt1ReceivedCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (optEkSentCt1ReceivedCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyEncCap g.2 sendingEk + 1#64 == 0#64) = !sendingEk.isSome ∧
      (optPolyEncCap g.2 sendingEk + 1#64 != 0#64) = sendingEk.isSome))
    (fun R' hm =>
      ⟨optEkSentCt1ReceivedPBPinnedAt_cap_bounds (p := a + 136#64)
        (R := optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) sendingEk ∗
          vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
       optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 240#64)
        (R := optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x22#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  suffices h3720 : ∀ sm1 : State,
      sm1.pc = entry + 3720#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = optEkSentCt1ReceivedCap g.1 uc → sm1.readReg64 .x20 = a →
      sm1.readReg64 .x23 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrProgAtExt b ext) ret sm1
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) sendingEk) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x22#8]) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 3720#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3720 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [optEkSentCt1ReceivedPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
      rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) none, ← hpack]
    | some u =>
      rw [optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ekSentCt1ReceivedPBEncodedLen u < 2 ^ 64 ∧ optEkSentCt1ReceivedPBFieldEncodedLen (some u) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optEkSentCt1ReceivedPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u)) < optEkSentCt1ReceivedPBFieldEncodedLen (some u) := by dsimp only [optEkSentCt1ReceivedPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt, bv_optEkSentCt1Received_some_eq u⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709549660#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) (some u)]
      refine step_etv_leaf_encLen16_call hres b ext (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen hekLen
        (a + 136#64) sp (entry + 2576#64) g.1 u hu_fit
        (F := optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) sendingEk ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x22#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
        (by rw [← hpack]; dsimp only [optEkSentCt1ReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
      rcases hcsm1 with ⟨hm19, hm20, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm, hx20] at hm19 hm20 hm27 hmfp
      apply SepWPp.of_sepWP_cs (mid := entry + 3720#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3720 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
      dsimp only [optEkSentCt1ReceivedPBPinnedAt]; ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx23_1 hx27_1 hfp_1 hinv_1
  suffices h4476 : ∀ sm2 : State,
      sm2.pc = entry + 4476#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingEk) →
      sm2.readReg64 .x19 = optEkSentCt1ReceivedCap g.1 uc →
      sm2.readReg64 .x20 = a → sm2.readReg64 .x21 = a + 240#64 → sm2.readReg64 .x22 = optPolyEncCap g.2 sendingEk →
      sm2.readReg64 .x23 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrProgAtExt b ext) ret sm2
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) sendingEk) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x22#8]) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases sendingEk with
    | none =>
      rw [optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 240#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 4476#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4476 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialEncoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2))
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 240#64) none]
    | some enc =>
      rw [optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 240#64) (some enc)]; simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have ⟨henc_fit, hopt_e_lt⟩ : polynomialEncoderPBEncodedLen enc < 2 ^ 64 ∧ optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialEncoderPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_e_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc)) < optPolynomialEncoderPBFieldEncodedLen (some enc) := by dsimp only [optPolynomialEncoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_e, hopt_e_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_e_lt hopt_e_lt, ult_of_lt_of_fit hvar_e_lt hopt_e_lt, bv_optPolyEnc_some_eq enc⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709525468#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 240#64) (some enc)]
      refine step_etv_leaf_encLen16_call hres b ext (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen hpolyEncLen
        (a + 240#64) sp (entry + 3744#64) g.2 enc henc_fit
        (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x22#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2)
        (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, _, _, hm2_27, _, hm2_fp, _⟩; simp only [arm64_norm, hx19_1, hx20_1, hx23_1, hx27_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_27 hm2_fp
      apply SepWPp.of_sepWP_cs (mid := entry + 4476#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4476 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
      dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx27_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen sendingEk)
      (b := optEkSentCt1ReceivedPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩))
      rfl hsub_len
  apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x22#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩)))
  refine step_etv_encode_varint_call b A ext hvarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩)))
    (sp - 120#64) cap ptr sp (entry + 4492#64) (bs ++ [0x22#8]) hfit_var
    (F := (optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) sendingEk) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, _, _, _, _, hm3_27, _, hm3_fp, _⟩; simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx27_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_27 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 uc
  suffices h4512 : ∀ sm4 : State,
      sm4.pc = entry + 4512#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x21 = a + 240#64 → sm4.readReg64 .x22 = optPolyEncCap g.2 sendingEk →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrProgAtExt b ext) ret sm4
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) sendingEk) ∗
          vecU8At A (sp - 120#64) cap ptr bs2 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 4512#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4512 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4))
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc : bs1.length + (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 u).length ≤ cap.toNat := by simp +zetaDelta only [bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709443724#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine step_etv_encode_ekSentCt1Received_call b A ext hekEnc (a + 136#64) (sp - 120#64) cap ptr sp (entry + 4512#64) g.1 u bs1 hfit_uc
        (F := optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) sendingEk ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4)
        (by dsimp only [bs1, optEkSentCt1ReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
      rcases hcsm4 with ⟨_, _, hm4_21, hm4_22, _, _, _, _, hm4_27, _, hm4_fp, _⟩; simp only [arm64_norm, hm3_21, hm3_22, hm3_27, hm3_fp] at hm4_21 hm4_22 hm4_27 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4512 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_21 hm4_22 hm4_27 hm4_fp hinv_m4)
      simp +zetaDelta only [bs2, Proto.encodeOptMessage, optEkSentCt1ReceivedPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx21_4 hx22_4 hx27_4 hfp_4 hinv_4
  cases sendingEk with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
    apply SepWPp.of_sepWP_cs (mid := entry + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [encodeInnerState_ct1Received_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]
  | some enc =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
    have hfit_enc : bs2.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709442756#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine step_etv_encode_polyEncoder_call b A ext hpolyEnc (a + 240#64) (sp - 120#64) cap ptr sp (entry + 5708#64) g.2 enc bs2 hfit_enc
      (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5)
      (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5
    rcases hcsm5 with ⟨_, _, _, _, _, _, _, _, hm5_27, _, hm5_fp, _⟩; simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    apply SepWPp.of_sepWP_cs (mid := entry + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv6
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m5.trans hinv6))
    rw [encodeInnerState_ct1Received_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage,
      optPolynomialEncoderPBPinnedAt, List.append_assoc]; ac_rfl

end CryptoVerification.SpqrV1.Prost.EncodeToVec
