/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import all Init.Data.Nat.Bitwise.Basic
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridges
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1ChainPhase
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPoly
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1State
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import ProofLib.SepLogic.WPp

/-!
# Phase 2d & Master Composition for `PqRatchetState::encode_to_vec` (`0x6d010`)

Defines the `StepInnerStateAt1880` jump-table obligation, proves Phase 2d (`+1740 .. +1808`,
`0x6d6dc .. 0x6d720`) and the 4 delegating `V1StateChunked1` variant bridges, and composes Phases
1–2d with the epilogue into `pqRatchetStateEncodeToVec_gen_ok_ext` and top-level `subroutine_ok`
wrappers.
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

/-- Execute the `.rodata` half-word (`↦₁₆ᵣ`) jump table dispatch at `+1880 .. +1896` (`0x6d768 .. 0x6d778`)
from `entry + 1880#64` to `entry + off`. -/
macro "step_etv_jump16_to " entry:term:max off:num s1:term:max idx:term:max hx8:term:max : tactic =>
  `(tactic| (
    have _hx8 : ($s1).readReg64 .x8 = $idx := $hx8
    dsimp only [encodeToVecJumpTableBytesAt]
    apply SepWPp.of_sepWP_cs (mid := $entry + BitVec.ofNat 64 $off)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])))

/-- Unified stepping obligation from `entry + 1880#64` (`0x6d768`, jump-table dispatch)
to `entry + 1808#64` (`0x6d720`, epilogue) for a `V1State.InnerState` value `is`. -/
def StepInnerStateAt1880 (resStack : Nat) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry roBase : BitVec 64)
    (s0 : State) (is : V1State.InnerState) : Prop :=
  ∀ (a sp cap ptr : BitVec 64) (g : V1StatePBGhost) (bs : List (BitVec 8)),
    v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64 →
    bs.length + (V1State.InnerState.encode is).length ≤ cap.toNat →
    sp &&& 15#64 = 0#64 →
    ∀ {R : SepProp} {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop},
      s.pc = entry + 1880#64 →
      s.status = .Running →
      s.sp = sp - 144#64 →
      s.trace = s0.trace →
      s.readReg64 .x8 =
        (if BitVec.ult (v1StateInnerCap g is ^^^ 0x8000000000000000#64) 11#64
         then v1StateInnerCap g is ^^^ 0x8000000000000000#64 else 7#64) →
      s.readReg64 .x9 = roBase →
      s.readReg64 .x20 = a →
      s.readReg64 .x21 = a + 128#64 →
      s.readReg64 .x28 = v1StateInnerCap g is →
      StepInv s0 s →
      P = (v1StateInnerPBPinnedAt A g (a + 128#64) is ∗
        (roBase ↦ᵣ encodeToVecJumpTableBytes) ∗
        vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F →
      (∀ sm : State,
        sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
        sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
        SepWPp (spqrProgAtExt b ext) ret sm
          ((v1StateInnerPBPinnedAt A g (a + 128#64) is ∗
            (roBase ↦ᵣ encodeToVecJumpTableBytes) ∗
            vecU8At A (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode is) ∗ A.pool ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) →
      SepWPp (spqrProgAtExt b ext) ret s P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))

theorem step_encodeToVec_v1_ct1Sampled_at_1880 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 : State}
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
    (v : V1State.Chunked.Ct1Sampled) :
    StepInnerStateAt1880 resStack b A ext entry roBase s0 (.ct1Sampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  etv_fetches b (Rust.withPanics ext) hfn 1880 1896
  examples_hide_fetches; subst hP
  simp only [v1StateInnerPBPinnedAt, v1StateInnerCap] at hx8 hx28 ⊢
  refine sepWPp_extract_pure
    (((optCt1SentCap g.b.gCt1Sampled.uc v.uc ^^^ 0x8000000000000000#64).ult 11#64) = false)
    (fun R' hm => by
      dsimp only [chunkedCt1SampledPBPinnedAt] at hm
      rw [optCt1SentPBPinnedAt_eq A g.b.gCt1Sampled.uc (a + 128#64) v.uc] at hm
      have hm' : s.mem ⊨ optCt1SentRest A g.b.gCt1Sampled.uc (a + 128#64) v.uc ∗
          (((a + 128#64) ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc) ∗
           optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (a + 128#64 + 128#64) v.sendingCt1 ∗
           optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (a + 128#64 + 184#64) v.receivingEk ∗
           (roBase ↦ᵣ encodeToVecJumpTableBytes) ∗
           vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
           stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
        convert hm using 1; ac_rfl
      exact (optCt1SentRest_disc_bounds hm').2.2)
    fun hult => ?_
  simp only [hult, Bool.false_eq_true, ↓reduceIte] at hx8
  rw [encodeToVecJumpTableBytes_eq roBase]
  step_etv_jump16_to entry 2620 s 7#64 hx8
  intro hinv1
  refine step_encodeToVec_v1_ct1Sampled hres b A ext hfn
    hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec
    a sp cap ptr g.b.gCt1Sampled v bs hv_len hfit halign
    (F := encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  rw [encodeToVecJumpTableBytes_eq roBase]
  exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_ekSentCt1Received_at_1880 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 : State}
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
    (v : V1State.Chunked.EkSentCt1Received) :
    StepInnerStateAt1880 resStack b A ext entry roBase s0 (.ekSentCt1Received v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  etv_fetches b (Rust.withPanics ext) hfn 1880 1896
  examples_hide_fetches; subst hP
  have hx8 : s.readReg64 .x8 = 4#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq roBase]
  step_etv_jump16_to entry 1976 s 4#64 hx8
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h240 : (a + 128#64) + 112#64 = a + 240#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240]
  refine step_encodeToVec_v1_ekSentCt1Received hres b A ext hfn
    hekLen hpolyDecLen hvarint hekEnc hpolyDec
    a sp cap ptr g.a.gEkSentCt1Received v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000004#64) ∗
      memRegion (a + 128#64 + 152#64) 72 ∗
      encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240, encodeToVecJumpTableBytes_eq roBase]
  exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_ct1Acknowledged_at_1880 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 : State}
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
    (v : V1State.Chunked.Ct1Acknowledged) :
    StepInnerStateAt1880 resStack b A ext entry roBase s0 (.ct1Acknowledged v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  etv_fetches b (Rust.withPanics ext) hfn 1880 1896
  examples_hide_fetches; subst hP
  have hx8 : s.readReg64 .x8 = 9#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq roBase]
  step_etv_jump16_to entry 2076 s 9#64 hx8
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h264 : (a + 128#64) + 136#64 = a + 264#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h264]
  refine step_encodeToVec_v1_ct1Acknowledged hres b A ext hfn
    hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec
    a sp cap ptr g.b.gCt1Acknowledged v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000009#64) ∗
      memRegion (a + 128#64 + 176#64) 48 ∗
      encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h264, encodeToVecJumpTableBytes_eq roBase]
  exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_ct1Received_at_1880 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 : State}
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
    (v : V1State.Chunked.Ct1Received) :
    StepInnerStateAt1880 resStack b A ext entry roBase s0 (.ct1Received v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  etv_fetches b (Rust.withPanics ext) hfn 1880 1896
  examples_hide_fetches; subst hP
  have hx8 : s.readReg64 .x8 = 3#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq roBase]
  step_etv_jump16_to entry 2520 s 3#64 hx8
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h240 : (a + 128#64) + 112#64 = a + 240#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240]
  refine step_encodeToVec_v1_ct1Received hres b A ext hfn
    hekLen hpolyEncLen hvarint hekEnc hpolyEnc
    a sp cap ptr g.a.gCt1Received v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000003#64) ∗
      memRegion (a + 128#64 + 168#64) 56 ∗
      encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240, encodeToVecJumpTableBytes_eq roBase]
  exact Entails.of_eq (by ac_rfl)

/-! ## Master Phase 2d Theorem (`+1740 .. +1808`, `0x6d6dc .. 0x6d720`) -/

/-- Step `+1740 .. +1808` (`0x6d6dc .. 0x6d720`): encodes `st.inner`
into `vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr`,
producing `PqRatchetState.encodeRaw st`. -/
theorem step_encodeToVec_phase2d {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (hjt : HasEncodeToVecJumpTableAddr b ext entry roBase)
    {s0 s : State}
    (hv1Len : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709530600#64)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hInnerAt1880 : ∀ is : V1State.InnerState, StepInnerStateAt1880 resStack b A ext entry roBase s0 is)
    (sret a sp ptr : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1740#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx27 : s.readReg64 .x27 = sret)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner)
    (hfp : s.readReg64 .fp = sp - 96#64) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      (roBase ↦ᵣ encodeToVecJumpTableBytes) ∗
      vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
        (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation ++
          Proto.encodeOptMessage ChainPB.encodeRaw 2#32 st.chain) ∗
      A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = sret → sm.readReg64 .fp = sp - 96#64 → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((pqRatchetStatePBPinnedAt A g a st ∗
          ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
          (roBase ↦ᵣ encodeToVecJumpTableBytes) ∗
          vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  let cap := BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)
  let bs0 := Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation ++
    Proto.encodeOptMessage ChainPB.encodeRaw 2#32 st.chain
  have hcap_toNat : cap.toNat = pqRatchetStatePBEncodedLen st := by
    dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  cases hin : st.inner with
  | none =>
    rw [hin] at hx28
    refine step_encodeToVec_inner_none b ext hfn sp hpc hrun hsp htr hx28 hinv0 ?_
    intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
    rw [hx27] at hx27m; rw [hfp] at hfpm
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
    have henc : PqRatchetState.encodeRaw st = bs0 := by
      unfold PqRatchetState.encodeRaw
      rw [hin]; simp only [bs0, List.append_nil]
    rw [henc]
    exact Entails.of_eq (by ac_rfl)
  | some inner =>
    cases inner with
    | v1 v1 =>
      rw [hin] at hx28
      have ⟨hv1_len64, _, _⟩ := v1StatePBEncodedLen_lt_of_state hin hlen
      have hv1_all : bs0.length + (PqRatchetState.Inner.encode (.v1 v1)).length ≤ cap.toNat := by
        rw [hcap_toNat, ← pqRatchetStatePBEncodedLen_eq_proto st]
        unfold PqRatchetState.encodeRaw
        rw [hin]; simp only [bs0, List.length_append]
        exact Nat.le_refl _
      rw [encodeInner_v1_eq v1] at hv1_all
      simp only [List.length_append, List.length_singleton,
        show (V1State.encodeRaw v1).length = v1StatePBEncodedLen v1 from v1StatePBEncodedLen_eq_proto v1] at hv1_all
      let F_outer : SepProp :=
        optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
          optChainPBPinnedAt A g.chain (a + 48#64) st.chain ∗
          (roBase ↦ᵣ encodeToVecJumpTableBytes) ∗ F
      refine step_encodeToVec_inner_some_hdr hres b A ext hfn hv1Len hvarint
        a sp cap ptr g.inner v1 bs0 hv1_len64 (by omega) halign
        (F := F_outer)
        hpc hrun hsp htr hx20 hx21 hx28 hinv0
        (by unfold pqRatchetStatePBPinnedAt; rw [hin]; dsimp only [optPqRatchetInnerPBPinnedAt, cap, bs0, F_outer]; ac_rfl) ?_
      intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_20 hs1_21 hs1_27 hs1_28 hs1_fp hinv_s1
      rw [hx27] at hs1_27; rw [hfp] at hs1_fp
      let bs_hdr := (bs0 ++ [0x1a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))
      cases his : v1.innerState with
      | none =>
        have hx28_none : s1.readReg64 .x28 = noneCap2 := by
          rw [hs1_28]; dsimp only [optPqRatchetInnerCap]; rw [his]
        refine step_encodeToVec_inner_v1_none b ext hfn sp hpcs1 hruns1 hsps1 htrs1
          hx28_none hinv_s1 ?_
        intro sm hpcm hrunm hspm htrm hm27 hmfp hinv_m
        rw [hs1_27] at hm27; rw [hs1_fp] at hmfp
        refine SepWPp.weaken_pre ?_
          (hnext sm hpcm hrunm hspm htrm hm27 hmfp hinv_m)
        have henc : PqRatchetState.encodeRaw st = bs_hdr := by
          unfold PqRatchetState.encodeRaw
          rw [hin]; dsimp only
          rw [encodeInner_v1_eq v1]
          dsimp only [V1State.encodeRaw]
          rw [his]
          simp only [List.append_nil, bs0, bs_hdr, List.append_assoc]
        rw [henc]
        unfold pqRatchetStatePBPinnedAt
        rw [hin]
        dsimp only [optPqRatchetInnerPBPinnedAt, cap, bs_hdr, F_outer]
        exact Entails.of_eq (by ac_rfl)
      | some is =>
        have hx28_some : s1.readReg64 .x28 = v1StateInnerCap g.inner is := by
          rw [hs1_28]; dsimp only [optPqRatchetInnerCap]; rw [his]
        refine sepWPp_extract_pure
          ((v1StateInnerCap g.inner is + 2#64 == 0#64) = false ∧
            (v1StateInnerCap g.inner is + 2#64 != 0#64) = true)
          (fun R' hm => by
            dsimp only [v1StatePBPinnedAt] at hm
            rw [his] at hm
            dsimp only at hm
            have hm' : s1.mem ⊨ v1StateInnerPBPinnedAt A g.inner (a + 128#64) is ∗
                (((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
                 vecU8At A (sp - 120#64) cap ptr bs_hdr ∗ A.pool ∗
                 stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F_outer ∗ R') := by
              convert hm using 1; dsimp only [bs_hdr]; ac_rfl
            exact v1StateInnerCap_add_two_bounds hm')
          fun ⟨hw_beq2, hw_bne2⟩ => ?_
        refine step_encodeToVec_inner_to_1880 b ext hfn hjt sp (v1StateInnerCap g.inner is)
          hw_beq2 hw_bne2 hpcs1 hruns1 hsps1 htrs1 hx28_some hinv_s1 ?_
        intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_9 hs2_20 hs2_21 hs2_27 hs2_28 hs2_fp hinv_s2
        rw [hs1_20] at hs2_20; rw [hs1_21] at hs2_21; rw [hs1_27] at hs2_27; rw [hs1_fp] at hs2_fp
        have hv_len64' : v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64 := by
          have : v1 = ⟨some is⟩ := by cases v1; subst his; rfl
          rw [← this]; exact hv1_len64
        have his_fit : bs_hdr.length + (V1State.InnerState.encode is).length ≤ cap.toNat := by
          have hlen_is : (V1State.InnerState.encode is).length = v1StatePBEncodedLen v1 := by
            rw [← v1StatePBEncodedLen_eq_proto v1]
            dsimp only [V1State.encodedLen, V1State.encodeRaw]; rw [his]
          simp only [bs_hdr, List.length_append, List.length_singleton, hlen_is]
          omega
        refine hInnerAt1880 is a sp cap ptr g.inner bs_hdr hv_len64' his_fit halign
          hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_9 hs2_20 hs2_21 hs2_28 hinv_s2
          (F := optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
            optChainPBPinnedAt A g.chain (a + 48#64) st.chain ∗
            ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗ F)
          (by dsimp only [v1StatePBPinnedAt, bs_hdr, F_outer]; rw [his]; dsimp only; ac_rfl) ?_
        intro sm hpcm hrunm hspm htrm hm27 hmfp hinv_m
        rw [hs2_27] at hm27; rw [hs2_fp] at hmfp
        refine SepWPp.weaken_pre ?_
          (hnext sm hpcm hrunm hspm htrm hm27 hmfp hinv_m)
        have henc : PqRatchetState.encodeRaw st = bs_hdr ++ V1State.InnerState.encode is := by
          unfold PqRatchetState.encodeRaw
          rw [hin]; dsimp only
          rw [encodeInner_v1_eq v1]
          dsimp only [V1State.encodeRaw]
          rw [his]
          simp only [bs0, bs_hdr, List.append_assoc]
        rw [henc]
        unfold pqRatchetStatePBPinnedAt
        rw [hin]
        dsimp only [optPqRatchetInnerPBPinnedAt, v1StatePBPinnedAt, cap]
        rw [his]
        exact Entails.of_eq (by ac_rfl)

/-! ## Master End-to-End Composition (`0x6d010 .. 0x6d74c`) -/

/-- General end-to-end `SepWPp` execution of `PqRatchetState::encode_to_vec` (`0x6d010`),
chaining Phase 1, Phase 2a, Phase 2b, Phase 2c, Phase 2d, and Epilogue. -/
theorem pqRatchetStateEncodeToVec_gen_ok_ext {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : PqRatchetStateEncodeToVecPinnedGhost} {R : SepProp} {s0 : State}
    (hjt : HasEncodeToVecJumpTableAddr b ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")))
    (hChainLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr chainEncodedLenLocal2Name)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hV1StateLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr v1StateEncodedLenLocal2Name)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))))
    (hshim : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (shimStackSpecOf resStack)))
    (halloc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (rustAllocStackSpecOf resStack A)))
    (hhandle : (spqrProgAtExt b ext).externAt?
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")) = some Rust.panicked)
    (hvarint : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      etvMemcpyRegionSpec)
    (hcp_call : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709441376#64)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (hep_call : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709524204#64)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)))
    (hed_call : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442992#64)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A)))
    (hInnerAt1880 : ∀ is : V1State.InnerState,
      StepInnerStateAt1880 resStack b A ext
        ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 is)
    (hpc : s0.pc = (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (pqRatchetStateEncodeToVecRoPinnedSpecOf resStack b A).pre x s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (spqrProgAtExt b ext) (s0.readReg64 .lr) s0 P
        (fun sf Q =>
          ((sf.mem ⊨ Q ∗ R) →
            StepInv s0 sf ∧
            (sf.mem ⊨ (pqRatchetStateEncodeToVecRoPinnedSpecOf resStack b A).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (pqRatchetStateEncodeToVecRoPinnedSpecOf resStack b A).onPanic x s0 sf ∗ R)) := by
  let entry := (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName
  have hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry := rfl
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hpre_pure := hpre; dsimp only [pqRatchetStateEncodeToVecRoPinnedSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hlen_raw⟩, hpre_mem⟩ := hpre_pure
  have hlen : pqRatchetStatePBEncodedLen x.st < 2 ^ 63 := by
    rw [← pqRatchetStatePBEncodedLen_eq_proto x.st]; exact hlen_raw
  have hv1Len_call : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709530600#64)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))) := by
    rw [encodeToVec_v1StateEncodedLen_fnAddr_eq b ext hfn]; exact hV1StateLen
  have hpre_rewritten : s0.mem ⊨
      ((pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
        ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
        stackAt s0.sp (encodeToVecStackOf resStack)) ∗
       (memRegion x.sret 24 ∗ ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes) ∗ A.pool)) ∗ R := by
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  refine step_encodeToVec_phase1 hres b A ext hfn hChainLen hV1StateLen
    x.sret x.a s0.sp x.g x.st hlen halign
    hpc hrun rfl hx0 hx1 rfl ?_
  intro s1 v0 v1 v2 v3 v4 v5 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hfp1 hinv1
  refine step_encodeToVec_alloc b A ext hfn hshim halloc hhandle
    x.sret x.a s0.sp v0 v1 v2 v3 v4 v5 x.g x.st hlen halign
    (F := memRegion x.sret 24 ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes))
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hfp1 hinv1
    (by ac_rfl) ?_
  intro s2 ptr hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hx25_2 hx27_2 hx28_2 hfp2 hinv2
  refine step_encodeToVec_versionNeg b A ext hfn hvarint hmemcpy hcp_call
    x.sret x.a s0.sp ptr v0 v1 v2 x.g x.st hlen halign
    (F := memRegion x.sret 24 ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes))
    hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hx27_2 hx28_2 hfp2 hinv2
    rfl ?_
  intro s3 w1 w2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx27_3 hx28_3 hfp3 hinv3
  refine step_encodeToVec_chain hres b A ext hfn hChainLen hep_call hvarint hmemcpy hed_call hcp_call
    x.sret x.a s0.sp ptr x.g x.st hlen halign
    (F := ((s0.sp - 144#64) ↦₆₄ v0) ∗ ((s0.sp - 136#64) ↦₆₄ w1) ∗ ((s0.sp - 128#64) ↦₆₄ w2) ∗
      encodeToVecSavedRegs s0.sp s0 ∗ memRegion x.sret 24 ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes))
    hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx27_3 hx28_3 hfp3 hinv3
    (by ac_rfl) ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hx20_4 hx21_4 hx27_4 hx28_4 hfp4 hinv4
  refine step_encodeToVec_phase2d hres b A ext hfn hjt hv1Len_call hvarint hInnerAt1880
    x.sret x.a s0.sp ptr x.g x.st hlen halign
    (F := memRegion x.sret 24 ∗
      ((s0.sp - 144#64) ↦₆₄ v0) ∗ ((s0.sp - 136#64) ↦₆₄ w1) ∗ ((s0.sp - 128#64) ↦₆₄ w2) ∗
      encodeToVecSavedRegs s0.sp s0)
    hpc4 hrun4 hsp4 htr4 hx20_4 hx21_4 hx27_4 hx28_4 hfp4 hinv4
    (by ac_rfl) ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx27_5 hfp5 hinv5
  refine step_encodeToVec_epilogue hres b A ext hfn
    x.sret s0.sp (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen x.st)) ptr v0 w1 w2
    (PqRatchetState.encodeRaw x.st)
    (F := pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes) ∗ A.pool)
    hpc5 hrun5 hsp5 halign htr5 hx27_5 hinv5
    (by ac_rfl) ?_
  intro sf _ _ hspf htrf hcsf hinvf
  refine ⟨fun hm => ⟨hinvf, ?_⟩, hspf, hcsf⟩
  dsimp only [pqRatchetStateEncodeToVecRoPinnedSpecOf]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  convert hm using 1; ac_rfl

/-! ## `.rodata` Jump-Table Facts and Top-Level `subroutine_ok` Wrappers -/

open ProofLib.ProgramReflection in
theorem rodata_0x82480_eq_encodeToVecJumpTable :
    (libsignalSessionImage.data.drop (num% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601") - num% (ls_xref% 0x2440 0x2444))).take 22 =
      encodeToVecJumpTableBytes := by
  rfl_kernel

open ProofLib.ProgramReflection in
theorem rodata_encodeToVecJumpTable_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) (secLen := 22) (dataOff := num% (ls_xref% 0x2440 0x2444))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x82480_eq_encodeToVecJumpTable] at h

theorem pqRatchetStateEncodeToVec_ro_ok_of_pinned {resStack : Nat}
    {prog : Program} {entry b : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (pqRatchetStateEncodeToVecRoPinnedSpecOf resStack b A)) :
    subroutine_ok prog entry (pqRatchetStateEncodeToVecRoSpecOf resStack b A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [pqRatchetStateEncodeToVecRoSpecOf] at hpre
  rw [pqRatchetStatePBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨x.sret, x.a, g, x.st⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [pqRatchetStateEncodeToVecRoSpecOf]
    rw [pqRatchetStatePBAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem pqRatchetStateEncodeToVec_ok_x_of_pinned {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry ((pqRatchetStateEncodeToVecPinnedSpecOf resStack A).inImage img)) :
    subroutine_ok prog entry ((pqRatchetStateEncodeToVecSpecOf resStack A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [Spec.inImage, pqRatchetStateEncodeToVecSpecOf] at hpre
  rw [pqRatchetStatePBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨x.sret, x.a, g, x.st⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, pqRatchetStateEncodeToVecSpecOf]
    rw [pqRatchetStatePBAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

section TopLevelWrappers
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Prost.MessageEncode

theorem encodeToVec_encodeVarint4_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709422336#64 =
      (spqrProgAtExt b ext).fnAddr encodeVarint4Name := by
  have h2 := (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]")
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff, encodeVarint4Name, h2]
  bv_omega

theorem encodeToVec_encodeChainParams2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709441376#64 =
      (spqrProgAtExt b ext).fnAddr encodeChainParams2Name := by
  have h2 := (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#2]")
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff, encodeChainParams2Name, h2]
  bv_omega

theorem encodeToVec_epochEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709524204#64 =
      (spqrProgAtExt b ext).fnAddr epochEncodedLenLocal2Name := by
  have h2 := (ls_lemma% fnOff "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#2]")
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff, epochEncodedLenLocal2Name, h2]
  bv_omega

theorem encodeToVec_encodeEpochDirection2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442992#64 =
      (spqrProgAtExt b ext).fnAddr encodeEpochDirection2Name := by
  have h2 := (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#2]")
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff, encodeEpochDirection2Name, h2]
  bv_omega

theorem subroutine_ok_withStepInv_x {α : Type} {prog : Program} {call_pc : BitVec 64}
    (img : Obj.Image) (s0 : State)
    (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) {S : Spec α}
    (hS : subroutine_ok prog call_pc (S.inImage img)) :
    subroutine_ok prog call_pc (withStepInv s0 S) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv_s, hpre'⟩
  have hpre_img : s.mem ⊨ (S.inImage img).pre x s ∗ R := by
    dsimp only [Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hinv_s.1 img hinv0.1, hinv_s.2.1.trans hinv0.2⟩, hpre'⟩
  exact hS.mono_outcome x R s hpc hrun hpre_img hal fun _ hout => hout

theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (hQ : ∀ sf P_f, Q sf P_f → Q' sf P_f)
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hQ sf P_f hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`0x6d010`) on
`pqRatchetStateEncodeToVecRoPinnedSpecOf doReserveStack b A`, discharging the 4 `V1StateChunked1`
variants and taking the remaining 7 `StepInnerStateAt1880` variants from `V1StateChunked2/3`. -/
theorem pqRatchetStateEncodeToVec_ro_pinned_ok_ext_of_variants
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (hKeysUnsampled : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.keysSampled v))
    (hHeaderSent : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.ct2Sampled v)) :
    subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName)
      (pqRatchetStateEncodeToVecRoPinnedSpecOf doReserveStack b A) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  have hvarint : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStack A)) := by
    apply etv_encodeVarint_exact_of_fit (by decide)
    rw [encodeToVec_encodeVarint4_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (encode_varint4_fit_ok_ext hA)
  have hcp_call : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709441376#64)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStack A)) := by
    apply etv_encodeChainParams_exact_of_spec (by decide)
    rw [encodeToVec_encodeChainParams2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (encode_chainParams_2_ok_ext hA)
  have hep_call : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709524204#64)
      (withStepInv s0 (epochEncLenStackSpecOf doReserveStack A)) := by
    rw [encodeToVec_epochEncodedLen2_fnAddr_eq]
    exact etv_epochEncodedLen_ok (by decide) b A ext s0
  have hed_call : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442992#64)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStack A)) := by
    apply etv_encodeEpochDirection_exact_of_spec (by decide)
    rw [encodeToVec_encodeEpochDirection2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (encode_epochDirection_2_pinned_ok_ext hA)
  have hpolyEnc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStack A)) := by
    apply etv_polyEncoderEncode_exact_of_spec
    rw [encodeToVec_polyEncoderEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (encode_polyEncoder_2_exact_pinned_ok_ext hA)
  have hpolyDec : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStack A)) := by
    apply etv_polyDecoderEncode_exact_of_spec
    rw [encodeToVec_polyDecoderEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (encode_polyDecoder_2_exact_pinned_ok_ext hA)
  have hekEnc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709443724#64)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStack A)) := by
    apply etv_ekSentCt1ReceivedEncode_of_spec
    rw [encodeToVec_ekSentCt1ReceivedEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (ek_sent_ct1_received_encode_2_pinned_ok_ext hA)
  have hct1SentEnc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709444388#64)
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStack A)) := by
    apply etv_ct1SentEncode_of_spec
    rw [encodeToVec_ct1SentEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (ct1_sent_encode_2_pinned_ok_ext hA)
  have hct1SampledLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709534032#64)
      (withStepInv s0 (leafEncLen48Spec (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen)) := by
    apply etv_leafEncLen48_withStepInv
    rw [encodeToVec_chunkedCt1SampledEncodedLen2_fnAddr_eq]
    exact chunkedCt1SampledEncodedLen_local2_pinned_ok_ext b A ext
  have hekLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709549660#64)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_ekSentCt1ReceivedEncodedLen2_fnAddr_eq]
    exact ekSentCt1ReceivedEncodedLen_local2_pinned_ok_ext b A ext
  have hpolyDecLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709536996#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_polyDecoderEncodedLen2_fnAddr_eq]
    exact polynomialDecoderEncodedLen_local2_pinned_ok_ext b A ext
  have hct1SentLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709534512#64)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_ct1SentEncodedLen2_fnAddr_eq]
    exact ct1SentEncodedLen_local2_pinned_ok_ext b A ext
  have hpolyEncLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709525468#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_polyEncoderEncodedLen2_fnAddr_eq]
    exact polynomialEncoderEncodedLen_local2_pinned_ok_ext b A ext
  have hInnerAt1880 : ∀ is : V1State.InnerState,
      StepInnerStateAt1880 doReserveStack b A ext
        ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 is := by
    intro is; cases is with
    | keysUnsampled v => exact hKeysUnsampled s0 v
    | keysSampled v => exact hKeysSampled s0 v
    | headerSent v => exact hHeaderSent s0 v
    | ct1Received v =>
      exact step_encodeToVec_v1_ct1Received_at_1880 (by decide) b A ext rfl
        hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
    | ekSentCt1Received v =>
      exact step_encodeToVec_v1_ekSentCt1Received_at_1880 (by decide) b A ext rfl
        hekLen hpolyDecLen hvarint hekEnc hpolyDec v
    | noHeaderReceived v => exact hNoHeaderReceived s0 v
    | headerReceived v => exact hHeaderReceived s0 v
    | ct1Sampled v =>
      exact step_encodeToVec_v1_ct1Sampled_at_1880 (by decide) b A ext rfl
        hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
    | ekReceivedCt1Sampled v => exact hEkReceivedCt1Sampled s0 v
    | ct1Acknowledged v =>
      exact step_encodeToVec_v1_ct1Acknowledged_at_1880 (by decide) b A ext rfl
        hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
    | ct2Sampled v => exact hCt2Sampled s0 v
  obtain ⟨P, hP, hwp⟩ := pqRatchetStateEncodeToVec_gen_ok_ext (by decide)
    (hasEncodeToVecJumpTableAddr b ext hb)
    (etv_chainEncodedLen_ok b A ext s0)
    (etv_v1StateEncodedLen_ok b A ext hb s0)
    (etv_shim_ok hA rfl s0)
    (etv_rustAlloc_ok (by decide) (by decide) hA rfl s0)
    (etv_handle_alloc_error b ext rfl)
    hvarint
    (etv_memcpy_ok hA rfl)
    hcp_call hep_call hed_call hInnerAt1880
    hpc hrun hpre hsp
  exact ⟨P, R, hP, sepWPp_mono_post (fun sf Q ⟨hq, hspf, hcsf⟩ => ⟨fun hm => (hq hm).2, hspf, hcsf⟩) hwp⟩

theorem pqRatchetStateEncodeToVec_ro_ok_ext_of_variants
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (hKeysUnsampled : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.keysSampled v))
    (hHeaderSent : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ s0 v, StepInnerStateAt1880 doReserveStack b A ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.ct2Sampled v)) :
    subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName)
      (pqRatchetStateEncodeToVecRoSpecOf doReserveStack b A) :=
  pqRatchetStateEncodeToVec_ro_ok_of_pinned
    (pqRatchetStateEncodeToVec_ro_pinned_ok_ext_of_variants hA hb
      hKeysUnsampled hKeysSampled hHeaderSent hNoHeaderReceived
      hHeaderReceived hEkReceivedCt1Sampled hCt2Sampled)

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`0x6d010`) on
`(pqRatchetStateEncodeToVecPinnedSpecOf doReserveStackX A).inImage img` (eliminating both `.rodata`
jump-table atoms via `Obj.Loads libsignalSessionImage img`). -/
theorem pqRatchetStateEncodeToVec_pinned_ok_ext_x_of_variants
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hKeysUnsampled : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.keysSampled v))
    (hHeaderSent : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.ct2Sampled v)) :
    subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName)
      ((pqRatchetStateEncodeToVecPinnedSpecOf doReserveStackX A).inImage img) := by
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hdoReserve := do_reserve_7_ok_ext_x (img := img) hA
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  have hro0 : img.RoDataLoaded s0.mem := (Obj.Image.frozenLoaded_iff.mp hinv0.1).2.1
  have hpre_ro1 := rodata_v1StateJumpTable_local2_intro himg hro0 hpre
  have hpre_ro2 := rodata_encodeToVecJumpTable_intro himg hro0 hpre_ro1
  have hpre_ro : s0.mem ⊨
      (pqRatchetStateEncodeToVecRoPinnedSpecOf doReserveStackX img.base A).pre x s0 ∗ R := by
    dsimp only [pqRatchetStateEncodeToVecPinnedSpecOf,
      pqRatchetStateEncodeToVecRoPinnedSpecOf] at hpre_ro2 ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre_ro2
  have hvarint : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStackX A)) := by
    apply etv_encodeVarint_exact_of_fit (by decide)
    rw [encodeToVec_encodeVarint4_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (encodeVarint4_fit_ok_ext_x img A ext hdoReserve)
  have hcp_call : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709441376#64)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStackX A)) := by
    apply etv_encodeChainParams_exact_of_spec (by decide)
    rw [encodeToVec_encodeChainParams2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (encode_chainParams_2_ok_ext_x hA)
  have hep_call : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709524204#64)
      (withStepInv s0 (epochEncLenStackSpecOf doReserveStackX A)) := by
    rw [encodeToVec_epochEncodedLen2_fnAddr_eq]
    exact etv_epochEncodedLen_ok (by decide) img.base A ext s0
  have hed_call : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709442992#64)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStackX A)) := by
    apply etv_encodeEpochDirection_exact_of_spec (by decide)
    rw [encodeToVec_encodeEpochDirection2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (encode_epochDirection_2_pinned_ok_ext_x hA)
  have hpolyEnc : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStackX A)) := by
    apply etv_polyEncoderEncode_exact_of_spec
    rw [encodeToVec_polyEncoderEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (encode_polyEncoder_2_exact_pinned_ok_ext_x hA)
  have hpolyDec : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStackX A)) := by
    apply etv_polyDecoderEncode_exact_of_spec
    rw [encodeToVec_polyDecoderEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (encode_polyDecoder_2_exact_pinned_ok_ext_x hA)
  have hekEnc : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709443724#64)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStackX A)) := by
    apply etv_ekSentCt1ReceivedEncode_of_spec
    rw [encodeToVec_ekSentCt1ReceivedEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (ek_sent_ct1_received_encode_2_pinned_ok_ext_x hA)
  have hct1SentEnc : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709444388#64)
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStackX A)) := by
    apply etv_ct1SentEncode_of_spec
    rw [encodeToVec_ct1SentEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (ct1_sent_encode_2_pinned_ok_ext_x hA)
  have hct1SampledLen : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709534032#64)
      (withStepInv s0 (leafEncLen48Spec (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen)) := by
    apply etv_leafEncLen48_withStepInv
    rw [encodeToVec_chunkedCt1SampledEncodedLen2_fnAddr_eq]
    exact chunkedCt1SampledEncodedLen_local2_pinned_ok_ext img.base A ext
  have hekLen : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709549660#64)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_ekSentCt1ReceivedEncodedLen2_fnAddr_eq]
    exact ekSentCt1ReceivedEncodedLen_local2_pinned_ok_ext img.base A ext
  have hpolyDecLen : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709536996#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_polyDecoderEncodedLen2_fnAddr_eq]
    exact polynomialDecoderEncodedLen_local2_pinned_ok_ext img.base A ext
  have hct1SentLen : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709534512#64)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_ct1SentEncodedLen2_fnAddr_eq]
    exact ct1SentEncodedLen_local2_pinned_ok_ext img.base A ext
  have hpolyEncLen : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709525468#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_polyEncoderEncodedLen2_fnAddr_eq]
    exact polynomialEncoderEncodedLen_local2_pinned_ok_ext img.base A ext
  have hInnerAt1880 : ∀ is : V1State.InnerState,
      StepInnerStateAt1880 doReserveStackX img.base A ext
        ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 is := by
    intro is; cases is with
    | keysUnsampled v => exact hKeysUnsampled s0 v
    | keysSampled v => exact hKeysSampled s0 v
    | headerSent v => exact hHeaderSent s0 v
    | ct1Received v =>
      exact step_encodeToVec_v1_ct1Received_at_1880 (by decide) img.base A ext rfl
        hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
    | ekSentCt1Received v =>
      exact step_encodeToVec_v1_ekSentCt1Received_at_1880 (by decide) img.base A ext rfl
        hekLen hpolyDecLen hvarint hekEnc hpolyDec v
    | noHeaderReceived v => exact hNoHeaderReceived s0 v
    | headerReceived v => exact hHeaderReceived s0 v
    | ct1Sampled v =>
      exact step_encodeToVec_v1_ct1Sampled_at_1880 (by decide) img.base A ext rfl
        hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
    | ekReceivedCt1Sampled v => exact hEkReceivedCt1Sampled s0 v
    | ct1Acknowledged v =>
      exact step_encodeToVec_v1_ct1Acknowledged_at_1880 (by decide) img.base A ext rfl
        hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
    | ct2Sampled v => exact hCt2Sampled s0 v
  obtain ⟨P, hP, hwp⟩ := pqRatchetStateEncodeToVec_gen_ok_ext (by decide)
    (hasEncodeToVecJumpTableAddr img.base ext hb)
    (etv_chainEncodedLen_ok img.base A ext s0)
    (etv_v1StateEncodedLen_ok img.base A ext hb s0)
    (etv_shim_ok hA rfl s0)
    (etv_rustAlloc_ok (by decide) (by decide) hA rfl s0)
    (etv_handle_alloc_error img.base ext rfl)
    hvarint
    (etv_memcpy_ok hA rfl)
    hcp_call hep_call hed_call hInnerAt1880
    hpc hrun hpre_ro hsp
  refine ⟨P, R, hP, sepWPp_mono_post (fun sf Q ⟨hq, hspf, hcsf⟩ => ⟨fun hm => ?_, hspf, hcsf⟩) hwp⟩
  obtain ⟨_, hpost_ro⟩ := hq hm
  dsimp only [Spec.inImage, pqRatchetStateEncodeToVecRoPinnedSpecOf,
    pqRatchetStateEncodeToVecPinnedSpecOf] at hpost_ro ⊢
  have hpost_perm : sf.mem ⊨
      (((img.base + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
       ((img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes)) ∗
      ((⌜sf.trace = s0.trace⌝ ∗
        vecU8 A x.sret (PqRatchetState.encodeRaw x.st) ∗
        pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
        A.pool ∗ stackAt s0.sp (encodeToVecStackOf doReserveStackX)) ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost_ro
  exact Satisfies.of_sep_right hpost_perm

theorem pqRatchetStateEncodeToVec_ok_ext_x_of_variants
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hKeysUnsampled : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.keysSampled v))
    (hHeaderSent : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ s0 v, StepInnerStateAt1880 doReserveStackX img.base A ext
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName) (img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 (.ct2Sampled v)) :
    subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName)
      ((pqRatchetStateEncodeToVecSpecOf doReserveStackX A).inImage img) :=
  pqRatchetStateEncodeToVec_ok_x_of_pinned
    (pqRatchetStateEncodeToVec_pinned_ok_ext_x_of_variants hA himg
      hKeysUnsampled hKeysSampled hHeaderSent hNoHeaderReceived
      hHeaderReceived hEkReceivedCt1Sampled hCt2Sampled)

end TopLevelWrappers

end CryptoVerification.SpqrV1.Prost.EncodeToVec

