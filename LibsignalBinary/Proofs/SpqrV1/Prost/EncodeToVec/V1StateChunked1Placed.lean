/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Phase 2c (Part 1): `V1State::encode_raw` Delegating Variants in `PqRatchetState::encode_to_vec` (`Block 426`)

Proves symbolic execution of the shared `PolynomialEncoder` / `PolynomialDecoder` tails and the
4 delegating `V1State.InnerState` branches in `PqRatchetState::encode_to_vec` (`Block 426`):
- `idx = 7`: `.ct1Sampled` (`+2620 .. +2748`)
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

set_option autoImplicit false
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

/-! ## 1. Shared `PolynomialDecoder` / `PolynomialEncoder` Tail Blocks -/

/-- Step `+2732 .. +1808` (`Block 426`): calls `encode<PolynomialDecoder>` (`lsmpl.base 315`)
with `w0 = 3#32`, `x1 = dec_ptr`, `x2 = sp - 120#64`, then branches to `+1808`. -/
theorem step_encodeToVec_tail_2732_polyDec3_placed [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (dec_ptr sp cap ptr : BitVec 64) (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 2732#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = dec_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialDecoderPBPinnedAt A g dec_ptr dec ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((polynomialDecoderPBPinnedAt A g dec_ptr dec ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 315); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_etv_encode_polyDecoder_call_placed A hpolyDec 3#32 dec_ptr (sp - 120#64) cap ptr sp ((blkPl_426).base + 2744#64) g dec bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨_, _, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm] at hm27 hmfp
  apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2)

/-- Step `+4456 .. +1808` (`Block 426`): calls `encode<PolynomialDecoder>` (`lsmpl.base 315`)
with `w0 = 2#32`, `x1 = dec_ptr`, `x2 = sp - 120#64`, then branches to `+1808`. -/
theorem step_encodeToVec_tail_4456_polyDec2_placed [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (dec_ptr sp cap ptr : BitVec 64) (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 4456#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = dec_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialDecoderPBPinnedAt A g dec_ptr dec ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((polynomialDecoderPBPinnedAt A g dec_ptr dec ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw 2#32 dec) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 315); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_etv_encode_polyDecoder_call_placed A hpolyDec 2#32 dec_ptr (sp - 120#64) cap ptr sp ((blkPl_426).base + 4468#64) g dec bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨_, _, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm] at hm27 hmfp
  apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2)

/-- Step `+5196 .. +1808` (`Block 426`): sets `x1 = x21`, calls `encode<PolynomialDecoder>`
(`lsmpl.base 315`) with `w0 = tag`, `x1 = dec_ptr`, `x2 = sp - 120#64`, then branches to `+1808`. -/
theorem step_encodeToVec_tail_5196_polyDec_placed [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (tag : BitVec 32) (dec_ptr sp cap ptr : BitVec 64) (g : PolynomialDecoderPBGhost)
    (dec : PolynomialDecoder) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw tag dec).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 5196#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hw0 : (s.readReg64 .x0).truncate 32 = tag) (hx2 : s.readReg64 .x2 = sp - 120#64)
    (hx21 : s.readReg64 .x21 = dec_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialDecoderPBPinnedAt A g dec_ptr dec ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((polynomialDecoderPBPinnedAt A g dec_ptr dec ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw tag dec) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 315); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_etv_encode_polyDecoder_call_placed A hpolyDec tag dec_ptr (sp - 120#64) cap ptr sp ((blkPl_426).base + 5204#64) g dec bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [State.readReg32, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨_, _, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm] at hm27 hmfp
  apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2)

/-- Step `+5700 .. +1808` (`Block 426`): sets `x1 = sp - 120#64`, calls
`encode<PolynomialEncoder>` (`lsmpl.base 316`) with `x0 = enc_ptr`, `x1 = sp - 120#64`, then branches to `+1808`. -/
theorem step_encodeToVec_tail_5700_polyEnc_placed [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (enc_ptr sp cap ptr : BitVec 64) (g : PolynomialEncoderPBGhost) (enc : PolynomialEncoder)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 5700#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = enc_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialEncoderPBPinnedAt A g enc_ptr enc ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((polynomialEncoderPBPinnedAt A g enc_ptr enc ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 316); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_etv_encode_polyEncoder_call_placed A hpolyEnc enc_ptr (sp - 120#64) cap ptr sp ((blkPl_426).base + 5708#64) g enc bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨_, _, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm] at hm27 hmfp
  apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2)

/-! ## 2. Variant `idx = 7`: `.ct1Sampled` (`+2620 .. +2748`) -/

/-- Step `+2620 .. +1808` (`Block 426`) for `is = .ct1Sampled v`. -/
theorem step_encodeToVec_v1_ct1Sampled_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hct1SampledLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 407)
      (withStepInv s0 (chunkedCt1SampledEncodedLenPinnedSpec A)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 319)
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : ChunkedCt1SampledPBGhost) (v : V1State.Chunked.Ct1Sampled)
    (bs : List (BitVec 8)) (hv_len : v1StatePBEncodedLen ⟨some (.ct1Sampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct1Sampled v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 2620#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx28 : s.readReg64 .x28 = optCt1SentCap g.uc v.uc) (hinv0 : StepInv s0 s)
    (hP : P = (chunkedCt1SampledPBPinnedAt A g (a + 128#64) v ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((chunkedCt1SampledPBPinnedAt A g (a + 128#64) v ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.ct1Sampled v)) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
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
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 407); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x42#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  refine step_etv_chunked_encLen48_call_placed hres (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen hct1SampledLen
    (a + 128#64) sp ((blkPl_426).base + 2664#64) g ⟨uc, sendingCt1, receivingEk⟩ hsub_len
    (F := vecU8At A (sp - 120#64) cap ptr (bs ++ [0x42#8]) ∗ A.pool ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by rw [← hpack]; ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨_, hm20, hm21, _, _, _, _, _, hm27, hm28, hmfp, _⟩; simp only [arm64_norm, hx20, hx21, hx28] at hm20 hm21 hm27 hm28 hmfp
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 292); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  set bs1 := (bs ++ [0x42#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩))
  refine step_etv_encode_varint_call_prog A hvarint (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩)) (sp - 120#64) cap ptr sp ((blkPl_426).base + 2672#64)
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
      sm3.pc = (blkPl_426).base + 2692#64 → sm3.status = .Running → sm3.sp = sp - 144#64 → sm3.trace = s0.trace →
      sm3.readReg64 .x20 = a → sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm3 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm3
        (((optCt1SentPBPinnedAt A g.uc (a + 128#64) uc ∗
          optPolynomialEncoderPBPinnedAt A g.sendingCt1 (a + 256#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A g.receivingEk (a + 312#64) receivingEk) ∗
          vecU8At A (sp - 120#64) cap ptr bs2 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 2692#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h2692 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
      simp +zetaDelta only [bs2, Proto.encodeOptMessage, List.append_nil]
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc : bs1.length + (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 u).length ≤ cap.toNat := by simp +zetaDelta only [bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := lsmpl.base 319); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine step_etv_encode_ct1Sent_call_placed A hct1SentEnc (a + 128#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 2692#64) g.uc u bs1 hfit_uc
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
      sm4.pc = (blkPl_426).base + 2716#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x20 = a → sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm4 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
        (((optCt1SentPBPinnedAt A g.uc (a + 128#64) uc ∗
          optPolynomialEncoderPBPinnedAt A g.sendingCt1 (a + 256#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A g.receivingEk (a + 312#64) receivingEk) ∗
          vecU8At A (sp - 120#64) cap ptr bs3 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases sendingCt1 with
    | none =>
      rw [optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (a + 256#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 2716#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h2716 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4))
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (a + 256#64) none]; simp +zetaDelta only [bs3, Proto.encodeOptMessage, List.append_nil]
    | some enc =>
      rw [optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (a + 256#64) (some enc)]; simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have hfit_enc : bs2.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := lsmpl.base 316); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (a + 256#64) (some enc)]
      refine step_etv_encode_polyEncoder_call_placed A hpolyEnc (a + 256#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 2716#64) g.sendingCt1 enc bs2 hfit_enc
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
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [← optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (a + 312#64) none, encodeInnerState_ct1Sampled_eq]; simp +zetaDelta only [bs3, bs2, bs1, Proto.encodeOptMessage, chunkedCt1SampledPBPinnedAt,
      List.append_nil, h128_128, h128_184, List.append_assoc]
  | some dec =>
    rw [optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (a + 312#64) (some dec)]; simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs3.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat := by simp +zetaDelta only [bs3, bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 2732#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    rw [← optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (a + 312#64) (some dec)]
    refine step_encodeToVec_tail_2732_polyDec3_placed A H hpolyDec (a + 312#64) sp cap ptr g.receivingEk dec bs3 hfit_dec halign
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

/-! ## 3. Variant `idx = 4`: `.ekSentCt1Received` (`+1976 .. +5204`) -/

/-- Step `+1976 .. +1808` (`Block 426`) for `is = .ekSentCt1Received v`. -/
theorem step_encodeToVec_v1_ekSentCt1Received_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hekLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 421)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hekEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 318)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : Unchunked4PBGhost × PolynomialDecoderPBGhost)
    (v : V1State.Chunked.EkSentCt1Received) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ekSentCt1Received v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ekSentCt1Received v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1976#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) v.receivingCt2) ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) v.uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) v.receivingCt2) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.ekSentCt1Received v)) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
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
      sm1.pc = (blkPl_426).base + 3580#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = optEkSentCt1ReceivedCap g.1 uc → sm1.readReg64 .x20 = a →
      sm1.readReg64 .x23 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm1
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
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 3580#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3580 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [optEkSentCt1ReceivedPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
      rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) none, ← hpack]
    | some u =>
      rw [optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ekSentCt1ReceivedPBEncodedLen u < 2 ^ 64 ∧ optEkSentCt1ReceivedPBFieldEncodedLen (some u) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optEkSentCt1ReceivedPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u)) < optEkSentCt1ReceivedPBFieldEncodedLen (some u) := by dsimp only [optEkSentCt1ReceivedPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt, bv_optEkSentCt1Received_some_eq u⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := lsmpl.base 421); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) (some u)]
      refine step_etv_leaf_encLen16_call_placed hres (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen hekLen
        (a + 136#64) sp ((blkPl_426).base + 2032#64) g.1 u hu_fit
        (F := optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) receivingCt2 ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x2a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
        (by rw [← hpack]; dsimp only [optEkSentCt1ReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
      rcases hcsm1 with ⟨hm19, hm20, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm, hx20] at hm19 hm20 hm27 hmfp
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 3580#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3580 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
      dsimp only [optEkSentCt1ReceivedPBPinnedAt]; ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx23_1 hx27_1 hfp_1 hinv_1
  suffices h4348 : ∀ sm2 : State,
      sm2.pc = (blkPl_426).base + 4348#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingCt2) →
      sm2.readReg64 .x19 = optEkSentCt1ReceivedCap g.1 uc →
      sm2.readReg64 .x20 = a → sm2.readReg64 .x21 = a + 240#64 →
      sm2.readReg64 .x22 = optPolyDecCap g.2 receivingCt2 →
      sm2.readReg64 .x23 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm2
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) receivingCt2) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x2a#8]) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases receivingCt2 with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 240#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 4348#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
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
      apply SepWPp.of_sepWP_cs (mid := lsmpl.base 413); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 240#64) (some dec)]
      refine step_etv_leaf_encLen16_call_placed hres (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen hpolyDecLen
        (a + 240#64) sp ((blkPl_426).base + 3604#64) g.2 dec hdec_fit
        (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x2a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2)
        (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, _, _, hm2_27, _, hm2_fp, _⟩; simp only [arm64_norm, hx19_1, hx20_1, hx23_1, hx27_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_27 hm2_fp
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 4348#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
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
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 292); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x2a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩)))
  refine step_etv_encode_varint_call_prog A hvarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩)))
    (sp - 120#64) cap ptr sp ((blkPl_426).base + 4364#64) (bs ++ [0x2a#8]) hfit_var
    (F := (optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) receivingCt2) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, _, _, _, _, hm3_27, _, hm3_fp, _⟩; simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx27_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_27 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 uc
  suffices h4384 : ∀ sm4 : State,
      sm4.pc = (blkPl_426).base + 4384#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x21 = a + 240#64 → sm4.readReg64 .x22 = optPolyDecCap g.2 receivingCt2 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 240#64) receivingCt2) ∗
          vecU8At A (sp - 120#64) cap ptr bs2 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 4384#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4384 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4))
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc : bs1.length + (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 u).length ≤ cap.toNat := by simp +zetaDelta only [bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := lsmpl.base 318); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine step_etv_encode_ekSentCt1Received_call_placed A hekEnc (a + 136#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 4384#64) g.1 u bs1 hfit_uc
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
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [encodeInnerState_ekSentCt1Received_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat := by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 5196#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine step_encodeToVec_tail_5196_polyDec_placed A H hpolyDec 3#32 (a + 240#64) sp cap ptr g.2 dec bs2 hfit_dec halign
      (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5
    simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5)
    rw [encodeInnerState_ekSentCt1Received_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage,
      optPolynomialDecoderPBPinnedAt, List.append_assoc]; ac_rfl

/-! ## 4. Variant `idx = 9`: `.ct1Acknowledged` (`+2076 .. +4468`) -/

/-- Step `+2076 .. +1808` (`Block 426`) for `is = .ct1Acknowledged v`. -/
theorem step_encodeToVec_v1_ct1Acknowledged_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hct1SentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 408)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)))
    (hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 319)
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : Unchunked5PBGhost × PolynomialDecoderPBGhost)
    (v : V1State.Chunked.Ct1Acknowledged) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ct1Acknowledged v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct1Acknowledged v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 2076#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optCt1SentPBPinnedAt A g.1 (a + 136#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) v.receivingEk) ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        (((optCt1SentPBPinnedAt A g.1 (a + 136#64) v.uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) v.receivingEk) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.ct1Acknowledged v)) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
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
      sm1.pc = (blkPl_426).base + 3652#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = optCt1SentCap g.1 uc → sm1.readReg64 .x20 = a →
      sm1.readReg64 .x22 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm1
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
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 3652#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3652 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [optCt1SentPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
      rw [← optCt1SentPBPinnedAt_eq A g.1 (a + 136#64) none, ← hpack]
    | some u =>
      rw [optCt1SentPBPinnedAt_eq A g.1 (a + 136#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ct1SentPBEncodedLen u < 2 ^ 64 ∧ optCt1SentPBFieldEncodedLen (some u) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optCt1SentPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (ct1SentPBEncodedLen u)) < optCt1SentPBFieldEncodedLen (some u) := by dsimp only [optCt1SentPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt, bv_optCt1Sent_some_eq u⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := lsmpl.base 408); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← optCt1SentPBPinnedAt_eq A g.1 (a + 136#64) (some u)]
      refine step_etv_leaf_encLen16_call_placed hres (ct1SentPBPinnedAt A) ct1SentPBEncodedLen hct1SentLen
        (a + 136#64) sp ((blkPl_426).base + 2132#64) g.1 u hu_fit
        (F := optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) receivingEk ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x52#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
        (by rw [← hpack]; dsimp only [optCt1SentPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
      rcases hcsm1 with ⟨hm19, hm20, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm, hx20] at hm19 hm20 hm27 hmfp
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 3652#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3652 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
      dsimp only [optCt1SentPBPinnedAt]; ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx22_1 hx27_1 hfp_1 hinv_1
  suffices h4408 : ∀ sm2 : State,
      sm2.pc = (blkPl_426).base + 4408#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingEk) →
      sm2.readReg64 .x19 = optCt1SentCap g.1 uc →
      sm2.readReg64 .x20 = a → sm2.readReg64 .x21 = optPolyDecCap g.2 receivingEk →
      sm2.readReg64 .x22 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm2
        (((optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) receivingEk) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x52#8]) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases receivingEk with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 264#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 4408#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4408 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2))
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 264#64) none]
    | some dec =>
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 264#64) (some dec)]; simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have ⟨hdec_fit, hopt_d_lt⟩ : polynomialDecoderPBEncodedLen dec < 2 ^ 64 ∧ optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialDecoderPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_d_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) < optPolynomialDecoderPBFieldEncodedLen (some dec) := by dsimp only [optPolynomialDecoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_d, hopt_d_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_d_lt hopt_d_lt, ult_of_lt_of_fit hvar_d_lt hopt_d_lt, bv_optPolyDec_some_eq dec⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := lsmpl.base 413); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 264#64) (some dec)]
      refine step_etv_leaf_encLen16_call_placed hres (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen hpolyDecLen
        (a + 264#64) sp ((blkPl_426).base + 3672#64) g.2 dec hdec_fit
        (F := optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x52#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2)
        (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, _, _, _, _, hm2_27, _, hm2_fp, _⟩; simp only [arm64_norm, hx19_1, hx20_1, hx22_1, hx27_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_27 hm2_fp
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 4408#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
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
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 292); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x52#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩)))
  refine step_etv_encode_varint_call_prog A hvarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩)))
    (sp - 120#64) cap ptr sp ((blkPl_426).base + 4424#64) (bs ++ [0x52#8]) hfit_var
    (F := (optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) receivingEk) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, _, _, _, _, _, hm3_27, _, hm3_fp, _⟩; simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx27_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_27 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 uc
  suffices h4444 : ∀ sm4 : State,
      sm4.pc = (blkPl_426).base + 4444#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x20 = a → sm4.readReg64 .x21 = optPolyDecCap g.2 receivingEk →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
        (((optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 264#64) receivingEk) ∗
          vecU8At A (sp - 120#64) cap ptr bs2 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 4444#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4444 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4))
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc : bs1.length + (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 u).length ≤ cap.toNat := by simp +zetaDelta only [bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := lsmpl.base 319); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine step_etv_encode_ct1Sent_call_placed A hct1SentEnc (a + 136#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 4444#64) g.1 u bs1 hfit_uc
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
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [encodeInnerState_ct1Acknowledged_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat := by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 4456#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine step_encodeToVec_tail_4456_polyDec2_placed A H hpolyDec (a + 264#64) sp cap ptr g.2 dec bs2 hfit_dec halign
      (F := optCt1SentPBPinnedAt A g.1 (a + 136#64) uc ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5
    simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5)
    rw [encodeInnerState_ct1Acknowledged_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage,
      optPolynomialDecoderPBPinnedAt, List.append_assoc]; ac_rfl

/-! ## 5. Variant `idx = 3`: `.ct1Received` (`+2520 .. +5708`) -/

/-- Step `+2520 .. +1808` (`Block 426`) for `is = .ct1Received v`. -/
theorem step_encodeToVec_v1_ct1Received_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hekLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 421)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hekEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 318)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : Unchunked4PBGhost × PolynomialEncoderPBGhost)
    (v : V1State.Chunked.Ct1Received) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ct1Received v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct1Received v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 2520#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) v.sendingEk) ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) v.uc ∗
          optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) v.sendingEk) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.ct1Received v)) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
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
      sm1.pc = (blkPl_426).base + 3720#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = optEkSentCt1ReceivedCap g.1 uc → sm1.readReg64 .x20 = a →
      sm1.readReg64 .x23 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm1
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
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 3720#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3720 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [optEkSentCt1ReceivedPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
      rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) none, ← hpack]
    | some u =>
      rw [optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ekSentCt1ReceivedPBEncodedLen u < 2 ^ 64 ∧ optEkSentCt1ReceivedPBFieldEncodedLen (some u) < 2 ^ 64 := ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optEkSentCt1ReceivedPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u)) < optEkSentCt1ReceivedPBFieldEncodedLen (some u) := by dsimp only [optEkSentCt1ReceivedPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt, bv_optEkSentCt1Received_some_eq u⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := lsmpl.base 421); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 136#64) (some u)]
      refine step_etv_leaf_encLen16_call_placed hres (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen hekLen
        (a + 136#64) sp ((blkPl_426).base + 2576#64) g.1 u hu_fit
        (F := optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) sendingEk ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x22#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
        (by rw [← hpack]; dsimp only [optEkSentCt1ReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
      rcases hcsm1 with ⟨hm19, hm20, _, _, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm, hx20] at hm19 hm20 hm27 hmfp
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 3720#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3720 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
      dsimp only [optEkSentCt1ReceivedPBPinnedAt]; ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx23_1 hx27_1 hfp_1 hinv_1
  suffices h4476 : ∀ sm2 : State,
      sm2.pc = (blkPl_426).base + 4476#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingEk) →
      sm2.readReg64 .x19 = optEkSentCt1ReceivedCap g.1 uc →
      sm2.readReg64 .x20 = a → sm2.readReg64 .x21 = a + 240#64 → sm2.readReg64 .x22 = optPolyEncCap g.2 sendingEk →
      sm2.readReg64 .x23 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm2
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) sendingEk) ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x22#8]) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases sendingEk with
    | none =>
      rw [optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 240#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 4476#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
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
      apply SepWPp.of_sepWP_cs (mid := lsmpl.base 401); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 240#64) (some enc)]
      refine step_etv_leaf_encLen16_call_placed hres (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen hpolyEncLen
        (a + 240#64) sp ((blkPl_426).base + 3744#64) g.2 enc henc_fit
        (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ [0x22#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2)
        (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, _, _, hm2_27, _, hm2_fp, _⟩; simp only [arm64_norm, hx19_1, hx20_1, hx23_1, hx27_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_27 hm2_fp
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 4476#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
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
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 292); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x22#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩)))
  refine step_etv_encode_varint_call_prog A hvarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩)))
    (sp - 120#64) cap ptr sp ((blkPl_426).base + 4492#64) (bs ++ [0x22#8]) hfit_var
    (F := (optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) sendingEk) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, _, _, _, _, hm3_27, _, hm3_fp, _⟩; simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx27_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_27 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 uc
  suffices h4512 : ∀ sm4 : State,
      sm4.pc = (blkPl_426).base + 4512#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x21 = a + 240#64 → sm4.readReg64 .x22 = optPolyEncCap g.2 sendingEk →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
        (((optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗
          optPolynomialEncoderPBPinnedAt A g.2 (a + 240#64) sendingEk) ∗
          vecU8At A (sp - 120#64) cap ptr bs2 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 4512#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4512 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4))
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc : bs1.length + (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 u).length ≤ cap.toNat := by simp +zetaDelta only [bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := lsmpl.base 318); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine step_etv_encode_ekSentCt1Received_call_placed A hekEnc (a + 136#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 4512#64) g.1 u bs1 hfit_uc
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
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [encodeInnerState_ct1Received_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]
  | some enc =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
    have hfit_enc : bs2.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := lsmpl.base 316); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine step_etv_encode_polyEncoder_call_placed A hpolyEnc (a + 240#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 5708#64) g.2 enc bs2 hfit_enc
      (F := optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5)
      (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5
    rcases hcsm5 with ⟨_, _, _, _, _, _, _, _, hm5_27, _, hm5_fp, _⟩; simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1808#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv6
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m5.trans hinv6))
    rw [encodeInnerState_ct1Received_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage,
      optPolynomialEncoderPBPinnedAt, List.append_assoc]; ac_rfl

end CryptoVerification.SpqrV1.Prost.EncodeToVec
