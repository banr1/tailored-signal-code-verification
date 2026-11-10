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
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2
import ProofLib.SepLogic.WPp

/-!
# Phase 2c (Part 3a): `V1State::encode_raw` Variants `idx = 10, 6` in `PqRatchetState::encode_to_vec`

Proves shared pure unfolding/bytes-field helpers and symbolic execution of the `V1State.InnerState`
branches `idx = 10` (`.ct2Sampled`, `+3008 .. +5712`) and `idx = 6` (`.headerReceived`, `+2908 .. +5208`)
in `PqRatchetState::encode_to_vec` (`0x6d010`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

local macro "etv_cs" mid:term : tactic =>
  `(tactic| (apply SepWPp.of_sepWP_cs (mid := $mid); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])))
local macro "s_an" : term => `(by simp only [arm64_norm, *])
local macro "s_an0" : term => `(by simp only [arm64_norm])

/-! ## 1. Pure Encoding Unfolding & Shared Stepping Helpers -/

theorem etv3_encodeBytesField_5_eq (bs : List (BitVec 8)) :
    Proto.encodeBytesField 5#32 bs = if bs.isEmpty then [] else [0x2a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond; rw [show Proto.encodeKey 5#32 .lengthDelimited = [0x2a#8] from rfl]

theorem etv3_bv_optCt2Sent_some_eq (u : V1State.Unchunked.Ct2Sent) :
    BitVec.ofNat 64 (ct2SentPBEncodedLen u) + BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (ct2SentPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optCt2SentPBFieldEncodedLen (some u)) := by
  dsimp only [optCt2SentPBFieldEncodedLen]; simp only [← BitVec.ofNat_add]; congr 1; omega

theorem etv3_encodeOptCt2Sent_some_eq (u : V1State.Unchunked.Ct2Sent) :
    Proto.encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw 1#32 (some u) =
      (([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (ct2SentPBEncodedLen u))) ++
        Proto.encodeUint64Field 1#32 u.epoch) ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth := by
  rw [show Proto.encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw 1#32 (some u) = Proto.encodeMessage V1State.Unchunked.Ct2Sent.encodeRaw 1#32 u from rfl]
  dsimp only [Proto.encodeMessage]; rw [show Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] from rfl, ← V1State.Unchunked.Ct2Sent.encodedLen, ct2SentPBEncodedLen_eq_proto]
  dsimp only [V1State.Unchunked.Ct2Sent.encodeRaw]; simp only [List.append_assoc]

theorem etv3_encodeInnerState_ct2Sampled_eq (v : V1State.Chunked.Ct2Sampled) :
    V1State.InnerState.encode (.ct2Sampled v) =
      (([0x5a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw 1#32 v.uc) ++ Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingCt2 := by
  have hlen : (V1State.Chunked.Ct2Sampled.encodeRaw v).length = v1StateInnerPayloadEncodedLen (.ct2Sampled v) := by
    dsimp only [V1State.Chunked.Ct2Sampled.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append, optCt2SentPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩, optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 v.sendingCt2 ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 11#32 .lengthDelimited = [0x5a#8] from rfl, hlen]
  dsimp only [V1State.Chunked.Ct2Sampled.encodeRaw]; simp only [List.append_assoc]

theorem etv3_bv_optHeaderReceived_some_eq (u : V1State.Unchunked.HeaderReceived) :
    BitVec.ofNat 64 (headerReceivedPBEncodedLen u) + BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optHeaderReceivedPBFieldEncodedLen (some u)) := by
  dsimp only [optHeaderReceivedPBFieldEncodedLen]; simp only [← BitVec.ofNat_add]; congr 1; omega

theorem etv3_encodeOptHeaderReceived_some_eq (u : V1State.Unchunked.HeaderReceived) :
    Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u) =
      ((([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))) ++
        Proto.encodeUint64Field 1#32 u.epoch) ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth) ++ Proto.encodeBytesField 3#32 u.hdr := by
  rw [show Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u) = Proto.encodeMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 u from rfl]
  dsimp only [Proto.encodeMessage]
  rw [show Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] from rfl, ← V1State.Unchunked.HeaderReceived.encodedLen, headerReceivedPBEncodedLen_eq_proto]
  dsimp only [V1State.Unchunked.HeaderReceived.encodeRaw]; simp only [List.append_assoc]

theorem etv3_encodeInnerState_headerReceived_eq (v : V1State.Chunked.HeaderReceived) :
    V1State.InnerState.encode (.headerReceived v) =
      (([0x3a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 v.uc) ++ Proto.encodeOptMessage PolynomialDecoder.encodeRaw 2#32 v.receivingEk := by
  have hlen : (V1State.Chunked.HeaderReceived.encodeRaw v).length = v1StateInnerPayloadEncodedLen (.headerReceived v) := by
    dsimp only [V1State.Chunked.HeaderReceived.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append, optHeaderReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩, optPolynomialDecoderPBFieldEncodedLen_eq_proto 2#32 v.receivingEk ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 7#32 .lengthDelimited = [0x3a#8] from rfl, hlen]
  dsimp only [V1State.Chunked.HeaderReceived.encodeRaw]; simp only [List.append_assoc]

theorem etv3_bv_optHeaderSent_some_eq (u : V1State.Unchunked.HeaderSent) :
    BitVec.ofNat 64 (headerSentPBEncodedLen u) + BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (headerSentPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optHeaderSentPBFieldEncodedLen (some u)) := by
  dsimp only [optHeaderSentPBFieldEncodedLen]; simp only [← BitVec.ofNat_add]; congr 1; omega

theorem etv3_bv_optCt1SentEkReceived_some_eq (u : V1State.Unchunked.Ct1SentEkReceived) :
    BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u) + BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u))) + 1#64 =
      BitVec.ofNat 64 (optCt1SentEkReceivedPBFieldEncodedLen (some u)) := by
  dsimp only [optCt1SentEkReceivedPBFieldEncodedLen]; simp only [← BitVec.ofNat_add]; congr 1; omega

theorem etv3_encodeOptCt1SentEkReceived_some_eq (u : V1State.Unchunked.Ct1SentEkReceived) :
    Proto.encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some u) =
      ((((([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u))) ++
        Proto.encodeUint64Field 1#32 u.epoch) ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth) ++
        Proto.encodeBytesField 3#32 u.es) ++ Proto.encodeBytesField 4#32 u.ek) ++ Proto.encodeBytesField 5#32 u.ct1 := by
  rw [show Proto.encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some u) = Proto.encodeMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 u from rfl]
  dsimp only [Proto.encodeMessage]
  rw [show Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] from rfl, ← V1State.Unchunked.Ct1SentEkReceived.encodedLen, ct1SentEkReceivedPBEncodedLen_eq_proto]
  dsimp only [V1State.Unchunked.Ct1SentEkReceived.encodeRaw]; simp only [List.append_assoc]

theorem etv3_encodeInnerState_ekReceivedCt1Sampled_eq (v : V1State.Chunked.EkReceivedCt1Sampled) :
    V1State.InnerState.encode (.ekReceivedCt1Sampled v) =
      (([0x4a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled v)))) ++
        Proto.encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 v.uc) ++ Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingCt1 := by
  have hlen : (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw v).length = v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled v) := by
    dsimp only [V1State.Chunked.EkReceivedCt1Sampled.encodeRaw, v1StateInnerPayloadEncodedLen]
    rw [List.length_append, optCt1SentEkReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩, optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 v.sendingCt1 ⟨by decide, by decide⟩]
  dsimp only [V1State.InnerState.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 9#32 .lengthDelimited = [0x4a#8] from rfl, hlen]
  dsimp only [V1State.Chunked.EkReceivedCt1Sampled.encodeRaw]; simp only [List.append_assoc]

/-- Shared helper for `BL encode_varint` + slice exposure inside non-empty `Vec<u8>` bytes fields. -/
theorem etv3_step_bytes_varint {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (bytesToWord64LE : BitVec 8) (sp cap ptr ret_pc : BitVec 64) (bs srcBs : List (BitVec 8)) (hemp : srcBs.isEmpty = false)
    (hfit : bs.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 srcBs.length)).length + srcBs.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 18446744073709422336#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .x30 = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 srcBs.length) (hx1 : s.readReg64 .x1 = sp - 120#64) (hinv0 : StepInv s0 s)
    (hP : P = ((((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗ ((sp - 104#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦₈ bytesToWord64LE) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1)) ∗
      A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      let bs_mid := (bs ++ [bytesToWord64LE]) ++ Proto.encodeVarint (BitVec.ofNat 64 srcBs.length)
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm → bs_mid.length + srcBs.length ≤ cap.toNat →
      BitVec.ult (cap - BitVec.ofNat 64 bs_mid.length) (BitVec.ofNat 64 srcBs.length) = false →
      SepWPp (spqrProgAtExt b ext) ret sm
        (((((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗ ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
            A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs_mid) ∗ memRegion (ptr + BitVec.ofNat 64 bs_mid.length) srcBs.length ∗
            memRegion (ptr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 srcBs.length) (cap.toNat - bs_mid.length - srcBs.length)) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 := ⟨by bv_omega, by bv_omega⟩
  have hlt_tag : bs.length < cap.toNat := by omega
  have hpack_tag := vecU8At_pack_one A (sp - 120#64) cap ptr bs bytesToWord64LE hlt_tag hcap hptr; rw [h112, h104] at hpack_tag
  refine step_etv_encode_varint_call b A ext hvarint (BitVec.ofNat 64 srcBs.length) (sp - 120#64) cap ptr sp ret_pc (bs ++ [bytesToWord64LE])
    (by simp only [List.length_append, List.length_singleton]; omega) (F := F) hpc hrun hsp halign htr hlr hx0 hx1 hinv0 (by rw [← hpack_tag]) ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  let bs_mid := (bs ++ [bytesToWord64LE]) ++ Proto.encodeVarint (BitVec.ofNat 64 srcBs.length)
  have hpos : 0 < srcBs.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
  have hfit_mc : bs_mid.length + srcBs.length ≤ cap.toNat := by dsimp only [bs_mid]; simp only [List.length_append, List.length_singleton]; omega
  have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
  refine SepWPp.weaken_pre (Entails.of_eq (by rw [vecU8At_expose_slice A (sp - 120#64) cap ptr bs_mid srcBs.length hfit_mc hcap hptr hpos, h112, h104]))
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm hfit_mc hcmp_mc)

/-! ## 2. Variant `idx = 10`: `.ct2Sampled` (`+3008 .. +5712`) -/

theorem step_encodeToVec_v1_ct2Sampled {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) {s0 s : State}
    (hct2Len : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709516504#64) (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A) ct2SentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709525468#64) (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441712#64) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442756#64) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : PolynomialEncoderPBGhost × Unchunked2PBGhost) (v : V1State.Chunked.Ct2Sampled) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ct2Sampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct2Sampled v)).length ≤ cap.toNat) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 3008#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) v.sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (a + 192#64) v.uc) ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm (((optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) v.sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (a + 192#64) v.uc) ∗
        vecU8At A (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.ct2Sampled v)) ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 3008 3068; etv_fetches b (Rust.withPanics ext) hfn 3464 3576
  etv_fetches b (Rust.withPanics ext) hfn 4176 4344; examples_hide_fetches; subst hP; rcases v with ⟨uc, sendingCt2⟩
  rw [etv3_encodeInnerState_ct2Sampled_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x5a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (a + 192#64) uc ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optCt2SentCap g.2 uc + 2#64 == 0#64) = !uc.isSome ∧ (optCt2SentCap g.2 uc + 2#64 != 0#64) = uc.isSome) ∧
     ((optPolyEncCap g.1 sendingCt2 + 1#64 == 0#64) = !sendingCt2.isSome ∧ (optPolyEncCap g.1 sendingCt2 + 1#64 != 0#64) = sendingCt2.isSome))
    (fun R' hm => ⟨optCt2SentPBPinnedAt_cap_bounds (p := a + 192#64)
        (R := optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
      optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 136#64)
        (R := optCt2SentPBPinnedAt A g.2 (a + 192#64) uc ∗ vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x5a#8 hlt1 hcap hptr; rw [h112, h104] at hpack
  suffices h3512 : ∀ sm1 : State, sm1.pc = entry + 3512#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = optCt2SentCap g.2 uc → sm1.readReg64 .x20 = a → sm1.readReg64 .x21 = a + 192#64 →
      sm1.readReg64 .x23 = BitVec.ofNat 64 (optCt2SentPBFieldEncodedLen uc) → sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrProgAtExt b ext) ret sm1 (((optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (a + 192#64) uc) ∗
        vecU8At A (sp - 120#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optCt2SentPBPinnedAt_eq A g.2 (a + 192#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      etv_cs (entry + 3512#64); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← optCt2SentPBPinnedAt_eq A g.2 (a + 192#64) none, ← hpack]))
        (h3512 _ s_an s_an s_an s_an s_an s_an s_an (by simp only [optCt2SentPBFieldEncodedLen, arm64_norm, *]) s_an s_an (hinv0.trans hinv1))
    | some u =>
      rw [optCt2SentPBPinnedAt_eq A g.2 (a + 192#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ct2SentPBEncodedLen u < 2 ^ 64 ∧ optCt2SentPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optCt2SentPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (ct2SentPBEncodedLen u)) < optCt2SentPBFieldEncodedLen (some u) := by dsimp only [optCt2SentPBFieldEncodedLen]; omega
      have ⟨⟨hu1, hu2, hu3, hu4, hu5⟩, hult_u, hopt_u_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt, etv3_bv_optCt2Sent_some_eq u⟩ : _ ∧ _ ∧ _)
      etv_cs (entry + 18446744073709516504#64); intro hinv1; rw [← optCt2SentPBPinnedAt_eq A g.2 (a + 192#64) (some u)]
      refine step_etv_leaf_encLen16_call hres b ext (ct2SentPBPinnedAt A) ct2SentPBEncodedLen hct2Len (a + 192#64) sp (entry + 3472#64) g.2 u hu_fit
        (F := optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ vecU8At A (sp - 120#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool ∗ F)
        s_an0 s_an s_an halign s_an s_an0 s_an (hinv0.trans hinv1) (by rw [← hpack]; dsimp only [optCt2SentPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 ⟨hm19, hm20, hm21, _, _, _, _, _, hm27, _, hmfp, _⟩ hinv_m1
      simp only [arm64_norm, hx20] at hm19 hm20 hm21 hm27 hmfp; etv_cs (entry + 3512#64); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [optCt2SentPBPinnedAt]; ac_rfl))
        (h3512 _ s_an s_an s_an s_an s_an s_an s_an s_an s_an s_an (hinv_m1.trans hinv2))
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx23_1 hx27_1 hfp_1 hinv_1
  suffices h4180 : ∀ sm2 : State, sm2.pc = entry + 4180#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingCt2) →
      sm2.readReg64 .x19 = optCt2SentCap g.2 uc → sm2.readReg64 .x20 = a → sm2.readReg64 .x21 = a + 192#64 →
      sm2.readReg64 .x22 = optPolyEncCap g.1 sendingCt2 → sm2.readReg64 .x23 = BitVec.ofNat 64 (optCt2SentPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrProgAtExt b ext) ret sm2 (((optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (a + 192#64) uc) ∗
        vecU8At A (sp - 120#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases sendingCt2 with
    | none =>
      rw [optPolynomialEncoderPBPinnedAt_eq A g.1 (a + 136#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      etv_cs (entry + 4180#64); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← optPolynomialEncoderPBPinnedAt_eq A g.1 (a + 136#64) none]))
        (h4180 _ s_an s_an s_an s_an (by simp only [optPolynomialEncoderPBFieldEncodedLen, arm64_norm, *]) s_an s_an s_an s_an s_an s_an s_an (hinv_1.trans hinv2))
    | some enc =>
      rw [optPolynomialEncoderPBPinnedAt_eq A g.1 (a + 136#64) (some enc)]; simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have ⟨henc_fit, hopt_e_lt⟩ : polynomialEncoderPBEncodedLen enc < 2 ^ 64 ∧ optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialEncoderPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_e_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc)) < optPolynomialEncoderPBFieldEncodedLen (some enc) := by dsimp only [optPolynomialEncoderPBFieldEncodedLen]; omega
      have ⟨⟨he1, he2, he3, he4, he5⟩, hult_e, hopt_e_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_e_lt hopt_e_lt, ult_of_lt_of_fit hvar_e_lt hopt_e_lt, bv_optPolyEnc_some_eq enc⟩ : _ ∧ _ ∧ _)
      etv_cs (entry + 18446744073709525468#64); intro hinv2; rw [← optPolynomialEncoderPBPinnedAt_eq A g.1 (a + 136#64) (some enc)]
      refine step_etv_leaf_encLen16_call hres b ext (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen hpolyEncLen (a + 136#64) sp (entry + 3532#64) g.1 enc henc_fit
        (F := optCt2SentPBPinnedAt A g.2 (a + 192#64) uc ∗ vecU8At A (sp - 120#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool ∗ F)
        s_an0 s_an s_an halign s_an s_an0 s_an (hinv_1.trans hinv2) (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, _, _, hm2_27, _, hm2_fp, _⟩ hinv_m2
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx23_1, hx27_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_27 hm2_fp
      etv_cs (entry + 4180#64); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl))
        (h4180 _ s_an s_an s_an s_an s_an s_an s_an s_an s_an s_an s_an s_an (hinv_m2.trans hinv3))
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx27_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen sendingCt2) (b := optCt2SentPBFieldEncodedLen uc) (c := v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)) rfl hsub_len
  etv_cs (entry + 18446744073709422336#64); intro hinv3
  set bs1 := (bs ++ [0x5a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)))
  refine step_etv_encode_varint_call b A ext hvarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)))
    (sp - 120#64) cap ptr sp (entry + 4196#64) (bs ++ [0x5a#8]) hfit_var
    (F := (optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (a + 192#64) uc) ∗ F)
    s_an0 s_an s_an halign s_an s_an0 s_an s_an (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 ⟨hm3_19, hm3_20, hm3_21, hm3_22, _, _, _, _, hm3_27, _, hm3_fp, _⟩ hinv_m3
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx27_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_27 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw 1#32 uc
  suffices h4328 : ∀ sm4 : State, sm4.pc = entry + 4328#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x20 = a → sm4.readReg64 .x22 = optPolyEncCap g.1 sendingCt2 → sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrProgAtExt b ext) ret sm4 (((optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (a + 192#64) uc) ∗
        vecU8At A (sp - 120#64) cap ptr bs2 ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne; etv_cs (entry + 4328#64); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl))
        (h4328 _ s_an s_an s_an s_an s_an s_an s_an s_an (hinv_m3.trans hinv4))
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      rw [etv3_encodeOptCt2Sent_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
      have hu_lt : ct2SentPBEncodedLen u < 2 ^ 64 := by dsimp only [v1StateInnerPayloadEncodedLen, optCt2SentPBFieldEncodedLen] at hsub_len; omega
      have hlt_tag : bs1.length < cap.toNat := by dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      have hbeq_tag := cap_beq_len_false_of_lt hlt_tag hcap
      rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs1 hlt_tag hcap hptr, h112, h104]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
      etv_cs (entry + 18446744073709516504#64); intro hinv4
      have hpack_tag := vecU8At_pack_one A (sp - 120#64) cap ptr bs1 0x0a#8 hlt_tag hcap hptr; rw [h112, h104] at hpack_tag
      refine step_etv_leaf_encLen16_call hres b ext (ct2SentPBPinnedAt A) ct2SentPBEncodedLen hct2Len (a + 192#64) sp (entry + 4248#64) g.2 u hu_lt
        (F := optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ vecU8At A (sp - 120#64) cap ptr (bs1 ++ [0x0a#8]) ∗ A.pool ∗ F)
        s_an0 s_an s_an halign s_an s_an0 s_an (hinv_m3.trans hinv4) (by rw [← hpack_tag]; dsimp only [optCt2SentPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx0m4 ⟨hm4_19, hm4_20, hm4_21, hm4_22, _, _, _, _, hm4_27, _, hm4_fp, _⟩ hinv_m4
      simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_22, hm3_27, hm3_fp] at hm4_19 hm4_20 hm4_21 hm4_22 hm4_27 hm4_fp
      etv_cs (entry + 18446744073709422336#64); intro hinv5
      set bs_u1 := (bs1 ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (ct2SentPBEncodedLen u))
      have hfit_uvar : (bs1 ++ [0x0a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (ct2SentPBEncodedLen u))).length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      refine step_etv_encode_varint_call b A ext hvarint (BitVec.ofNat 64 (ct2SentPBEncodedLen u)) (sp - 120#64) cap ptr sp (entry + 4256#64) (bs1 ++ [0x0a#8]) hfit_uvar
        (F := optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ ct2SentPBPinnedAt A g.2 (a + 192#64) u ∗ F)
        s_an0 s_an s_an halign s_an s_an0 s_an s_an (hinv_m4.trans hinv5) (by ac_rfl) ?_
      intro sm5 hpcm5 hrunm5 hspm5 htrm5 ⟨hm5_19, hm5_20, hm5_21, hm5_22, _, _, _, _, hm5_27, _, hm5_fp, _⟩ hinv_m5
      simp only [arm64_norm, hm4_19, hm4_20, hm4_21, hm4_22, hm4_27, hm4_fp] at hm5_19 hm5_20 hm5_21 hm5_22 hm5_27 hm5_fp
      dsimp only [ct2SentPBPinnedAt, unchunked2PinnedAt]
      have h192_48 : (a + 192#64) + 0x30#64 = a + 240#64 := by bv_omega
      rw [h192_48]
      refine sepWPp_extract_pure
        ((optAuthCap g.2 u.auth + 1#64 == 0#64) = !u.auth.isSome ∧ (optAuthCap g.2 u.auth + 1#64 != 0#64) = u.auth.isSome)
        (fun R' hm => etv2_optAuth_cap_bounds (A := A) (p := a + 192#64)
          (R := optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ ((a + 240#64) ↦₆₄ u.epoch) ∗
            vecU8At A (sp - 120#64) cap ptr bs_u1 ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
          (Satisfies.mono (Entails.of_eq (by dsimp only [bs_u1]; ac_rfl)) hm))
        fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
      set bs_u2 := bs_u1 ++ Proto.encodeUint64Field 1#32 u.epoch
      suffices h4308 : ∀ sm6 : State, sm6.pc = entry + 4308#64 → sm6.status = .Running → sm6.sp = sp - 144#64 → sm6.trace = s0.trace →
          sm6.readReg64 .x19 = optCt2SentCap g.2 (some u) → sm6.readReg64 .x20 = a →
          sm6.readReg64 .x21 = a + 192#64 → sm6.readReg64 .x22 = optPolyEncCap g.1 sendingCt2 →
          sm6.readReg64 .x27 = s.readReg64 .x27 → sm6.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm6 →
          SepWPp (spqrProgAtExt b ext) ret sm6 (((optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ optAuthenticatorPBPinnedAt A g.2 (a + 192#64) u.auth ∗ ((a + 240#64) ↦₆₄ u.epoch)) ∗
            vecU8At A (sp - 120#64) cap ptr bs_u2 ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
            Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
        cases hep : u.epoch == 0#64
        · have hfit_ep : bs_u1.length + 1 + (Proto.encodeVarint u.epoch).length ≤ cap.toNat := by
            rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs_u1, bs1]
            simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
          have hlt_ep : bs_u1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
          have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
          rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs_u1 hlt_ep hcap hptr, h112, h104]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b2 => ?_
          etv_cs (entry + 18446744073709422336#64); intro hinv6
          have hpack_ep := vecU8At_pack_one A (sp - 120#64) cap ptr bs_u1 0x08#8 hlt_ep hcap hptr; rw [h112, h104] at hpack_ep
          refine step_etv_encode_varint_call b A ext hvarint u.epoch (sp - 120#64) cap ptr sp (entry + 4308#64) (bs_u1 ++ [0x08#8])
            (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
            (F := (optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ optAuthenticatorPBPinnedAt A g.2 (a + 192#64) u.auth ∗ ((a + 240#64) ↦₆₄ u.epoch)) ∗ F)
            s_an0 s_an s_an halign s_an s_an0 s_an s_an (hinv_m5.trans hinv6) (by rw [← hpack_ep]; ac_rfl) ?_
          intro sm6 hpcm6 hrunm6 hspm6 htrm6 ⟨hm6_19, hm6_20, hm6_21, hm6_22, _, _, _, _, hm6_27, _, hm6_fp, _⟩ hinv_m6
          simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_27, hm5_fp] at hm6_19 hm6_20 hm6_21 hm6_22 hm6_27 hm6_fp
          refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs_u2, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte, List.append_assoc]; ac_rfl))
            (h4308 sm6 hpcm6 hrunm6 hspm6 htrm6 hm6_19 hm6_20 hm6_21 hm6_22 hm6_27 hm6_fp hinv_m6)
        · etv_cs (entry + 4308#64); intro hinv6
          refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs_u2, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; ac_rfl))
            (h4308 _ s_an s_an s_an s_an s_an s_an s_an s_an s_an s_an (hinv_m5.trans hinv6))
      intro sm6 hpcm6 hrunm6 hspm6 htrm6 hx19_6 hx20_6 hx21_6 hx22_6 hx27_6 hfp_6 hinv_6
      have hx19_eq : optCt2SentCap g.2 (some u) = optAuthCap g.2 u.auth := rfl; rw [hx19_eq] at hx19_6
      cases hauth : u.auth with
      | none =>
        simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne; etv_cs (entry + 4328#64); intro hinv7
        refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [bs2]; rw [etv3_encodeOptCt2Sent_some_eq]; simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, Proto.encodeOptMessage, optCt2SentPBPinnedAt, ct2SentPBPinnedAt, unchunked2PinnedAt, h192_48, List.append_nil, List.append_assoc]))
          (h4328 _ s_an s_an s_an s_an s_an s_an s_an s_an (hinv_6.trans hinv7))
      | some auth =>
        simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
        have hfit_auth : bs_u2.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
          rw [hauth] at hfit; dsimp only [bs_u2, bs_u1, bs1, Proto.encodeOptMessage] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
        etv_cs (entry + 18446744073709441712#64); intro hinv7
        refine step_etv_encode_auth_call b A ext hauthEnc (a + 192#64) (sp - 120#64) cap ptr sp (entry + 4328#64) g.2 auth bs_u2 hfit_auth
          (F := (optPolynomialEncoderPBPinnedAt A g.1 (a + 136#64) sendingCt2 ∗ ((a + 240#64) ↦₆₄ u.epoch)) ∗ F)
          s_an0 s_an s_an halign s_an s_an0 s_an s_an (hinv_6.trans hinv7) (by simp only [hauth, optAuthenticatorPBPinnedAt]; ac_rfl) ?_
        intro sm7 hpcm7 hrunm7 hspm7 htrm7 ⟨_, hm7_20, _, hm7_22, _, _, _, _, hm7_27, _, hm7_fp, _⟩ hinv_m7
        simp only [arm64_norm, hx20_6, hx22_6, hx27_6, hfp_6] at hm7_20 hm7_22 hm7_27 hm7_fp
        refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4328 sm7 hpcm7 hrunm7 hspm7 htrm7 hm7_20 hm7_22 hm7_27 hm7_fp hinv_m7)
        dsimp only [bs2]; rw [etv3_encodeOptCt2Sent_some_eq]
        simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, Proto.encodeOptMessage, optCt2SentPBPinnedAt, ct2SentPBPinnedAt, unchunked2PinnedAt, optAuthenticatorPBPinnedAt, h192_48, List.append_assoc]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx20_4 hx22_4 hx27_4 hfp_4 hinv_4
  cases sendingCt2 with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne; etv_cs (entry + 1808#64); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [etv3_encodeInnerState_ct2Sampled_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]))
      (hnext _ s_an s_an s_an s_an s_an s_an (hinv_4.trans hinv5))
  | some enc =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
    have hfit_enc : bs2.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    etv_cs (entry + 5700#64); intro hinv5
    refine step_encodeToVec_tail_5700_polyEnc b A ext hfn hpolyEnc (a + 136#64) sp cap ptr g.1 enc bs2 hfit_enc halign
      (F := optCt2SentPBPinnedAt A g.2 (a + 192#64) uc ∗ F) s_an0 s_an s_an s_an s_an (hinv_4.trans hinv5) (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5
    simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [etv3_encodeInnerState_ct2Sampled_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, optPolynomialEncoderPBPinnedAt, List.append_assoc]; ac_rfl))
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5)

/-! ## 3. Variant `idx = 6`: `.headerReceived` (`+2908 .. +5208`) -/

theorem etv3_step_headerReceived_some {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) {s0 s : State}
    (hhrLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709529772#64) (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441712#64) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext) (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")) etvMemcpyRegionSpec)
    (a sp cap ptr : BitVec 64) (g : Unchunked3PBGhost) (u : V1State.Unchunked.HeaderReceived) (bs : List (BitVec 8))
    (hu_lt : headerReceivedPBEncodedLen u < 2 ^ 64)
    (hfit : bs.length + (Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u)).length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 4944#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (headerReceivedPBPinnedAt A g (a + 136#64) u ∗ vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = entry + 5180#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm ((headerReceivedPBPinnedAt A g (a + 136#64) u ∗
        vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u)) ∗
        A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 4944 5180; examples_hide_fetches; subst hP
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 := ⟨by bv_omega, by bv_omega⟩
  rw [etv3_encodeOptHeaderReceived_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hlt1 : bs.length < cap.toNat := by omega
  have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
  etv_cs (entry + 18446744073709529772#64); intro hinv1
  have hpack1 := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x0a#8 hlt1 hcap hptr; rw [h112, h104] at hpack1
  refine step_etv_leaf_encLen16_call hres b ext (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen hhrLen (a + 136#64) sp (entry + 4988#64) g u hu_lt
    (F := vecU8At A (sp - 120#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool ∗ F) s_an0 s_an s_an halign s_an s_an0 s_an (hinv0.trans hinv1) (by rw [← hpack1]; ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 ⟨hm19, hm20, hm21, _, _, _, _, _, hm27, _, hmfp, _⟩ hinv_m1
  simp only [arm64_norm, hx20] at hm19 hm20 hm21 hm27 hmfp; etv_cs (entry + 18446744073709422336#64); intro hinv2
  set bs1 := (bs ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))
  have hfit_var : (bs ++ [0x0a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine step_etv_encode_varint_call b A ext hvarint (BitVec.ofNat 64 (headerReceivedPBEncodedLen u)) (sp - 120#64) cap ptr sp (entry + 4996#64) (bs ++ [0x0a#8]) hfit_var
    (F := headerReceivedPBPinnedAt A g (a + 136#64) u ∗ F) s_an0 s_an s_an halign s_an s_an0 s_an s_an (hinv_m1.trans hinv2) (by ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 ⟨hm2_19, hm2_20, hm2_21, _, _, _, _, _, hm2_27, _, hm2_fp, _⟩ hinv_m2
  simp only [arm64_norm, hm19, hm20, hm21, hm27, hmfp] at hm2_19 hm2_20 hm2_21 hm2_27 hm2_fp
  dsimp only [headerReceivedPBPinnedAt, unchunked3PinnedAt]
  have ⟨h136_24, h136_72⟩ : (a + 136#64) + 0x18#64 = a + 160#64 ∧ (a + 136#64) + 0x48#64 = a + 208#64 := ⟨by bv_omega, by bv_omega⟩
  rw [h136_24, h136_72]
  refine sepWPp_extract_pure
    ((optAuthCap g.auth u.auth + 1#64 == 0#64) = !u.auth.isSome ∧ (optAuthCap g.auth u.auth + 1#64 != 0#64) = u.auth.isSome)
    (fun R' hm => etv2_optAuth_cap_bounds (A := A) (p := a + 160#64)
      (R := vecU8At A (a + 136#64) g.f3.cap g.f3.ptr u.hdr ∗ ((a + 208#64) ↦₆₄ u.epoch) ∗
        vecU8At A (sp - 120#64) cap ptr bs1 ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      (Satisfies.mono (Entails.of_eq (by dsimp only [bs1]; ac_rfl)) hm))
    fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
  set bs2 := bs1 ++ Proto.encodeUint64Field 1#32 u.epoch
  suffices h5048 : ∀ sm3 : State, sm3.pc = entry + 5048#64 → sm3.status = .Running → sm3.sp = sp - 144#64 → sm3.trace = s0.trace →
      sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x20 = a → sm3.readReg64 .x21 = s.readReg64 .x21 →
      sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
      SepWPp (spqrProgAtExt b ext) ret sm3 (((vecU8At A (a + 136#64) g.f3.cap g.f3.ptr u.hdr ∗ optAuthenticatorPBPinnedAt A g.auth (a + 160#64) u.auth ∗ ((a + 208#64) ↦₆₄ u.epoch)) ∗
        vecU8At A (sp - 120#64) cap ptr bs2 ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases hep : u.epoch == 0#64
    · have hfit_ep : bs1.length + 1 + (Proto.encodeVarint u.epoch).length ≤ cap.toNat := by
        rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs1]; simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
      have hlt_ep : bs1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
      have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
      rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs1 hlt_ep hcap hptr, h112, h104]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
      etv_cs (entry + 18446744073709422336#64); intro hinv3
      have hpack_ep := vecU8At_pack_one A (sp - 120#64) cap ptr bs1 0x08#8 hlt_ep hcap hptr; rw [h112, h104] at hpack_ep
      refine step_etv_encode_varint_call b A ext hvarint u.epoch (sp - 120#64) cap ptr sp (entry + 5048#64) (bs1 ++ [0x08#8])
        (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
        (F := (vecU8At A (a + 136#64) g.f3.cap g.f3.ptr u.hdr ∗ optAuthenticatorPBPinnedAt A g.auth (a + 160#64) u.auth ∗ ((a + 208#64) ↦₆₄ u.epoch)) ∗ F)
        s_an0 s_an s_an halign s_an s_an0 s_an s_an (hinv_m2.trans hinv3) (by rw [← hpack_ep]) ?_
      intro sm3 hpcm3 hrunm3 hspm3 htrm3 ⟨hm3_19, hm3_20, hm3_21, _, _, _, _, _, hm3_27, _, hm3_fp, _⟩ hinv_m3
      simp only [arm64_norm, hm2_19, hm2_20, hm2_21, hm2_27, hm2_fp] at hm3_19 hm3_20 hm3_21 hm3_27 hm3_fp
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte, List.append_assoc]; ac_rfl))
        (h5048 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_20 hm3_21 hm3_27 hm3_fp hinv_m3)
    · etv_cs (entry + 5048#64); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; ac_rfl))
        (h5048 _ s_an s_an s_an s_an s_an s_an s_an s_an s_an (hinv_m2.trans hinv3))
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx20_3 hx21_3 hx27_3 hfp_3 hinv_3
  set bs3 := bs2 ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
  suffices h5072 : ∀ sm4 : State, sm4.pc = entry + 5072#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = a → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrProgAtExt b ext) ret sm4 (((vecU8At A (a + 136#64) g.f3.cap g.f3.ptr u.hdr ∗ optAuthenticatorPBPinnedAt A g.auth (a + 160#64) u.auth ∗ ((a + 208#64) ↦₆₄ u.epoch)) ∗
        vecU8At A (sp - 120#64) cap ptr bs3 ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases hauth : u.auth with
    | none =>
      rw [optAuthenticatorPBPinnedAt_eq A g.auth (a + 160#64) none]; simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
      etv_cs (entry + 5072#64); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← optAuthenticatorPBPinnedAt_eq A g.auth (a + 160#64) none]; simp +zetaDelta only [bs3, hauth, Proto.encodeOptMessage, List.append_nil]))
        (h5072 _ s_an s_an s_an s_an s_an s_an s_an s_an s_an (hinv_3.trans hinv4))
    | some auth =>
      rw [optAuthenticatorPBPinnedAt_eq A g.auth (a + 160#64) (some auth)]; simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
      have hfit_auth : bs2.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
        rw [hauth] at hfit; dsimp only [bs2, bs1, Proto.encodeOptMessage] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      etv_cs (entry + 18446744073709441712#64); intro hinv4; rw [← optAuthenticatorPBPinnedAt_eq A g.auth (a + 160#64) (some auth)]
      refine step_etv_encode_auth_call b A ext hauthEnc (a + 160#64) (sp - 120#64) cap ptr sp (entry + 5072#64) g.auth auth bs2 hfit_auth
        (F := (vecU8At A (a + 136#64) g.f3.cap g.f3.ptr u.hdr ∗ ((a + 208#64) ↦₆₄ u.epoch)) ∗ F)
        s_an0 s_an s_an halign s_an s_an0 s_an s_an (hinv_3.trans hinv4) (by dsimp only [optAuthenticatorPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
      rcases hcsm4 with ⟨hm4_19, hm4_20, hm4_21, _, _, _, _, _, hm4_27, _, hm4_fp, _⟩
      simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx27_3, hfp_3] at hm4_19 hm4_20 hm4_21 hm4_27 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h5072 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_27 hm4_fp hinv_m4)
      simp +zetaDelta only [bs3, hauth, Proto.encodeOptMessage, optAuthenticatorPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx27_4 hfp_4 hinv_4
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := a + 136#64) (cap := g.f3.cap) (ptr := g.f3.ptr) (bs := u.hdr)
    (F := optAuthenticatorPBPinnedAt A g.auth (a + 160#64) u.auth ∗ ((a + 208#64) ↦₆₄ u.epoch) ∗ vecU8At A (sp - 120#64) cap ptr bs3 ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by dsimp only [bs3]; ac_rfl) fun hhdr_le hhdr_cap _ => ?_
  have ⟨h144, h152⟩ : (a + 136#64) + 8#64 = a + 144#64 ∧ (a + 136#64) + 16#64 = a + 152#64 := ⟨by bv_omega, by bv_omega⟩
  rw [EncodedLen.vecU8At_eq_header_sep_buf A (a + 136#64), vecHeader, h144, h152]
  have hhdr_lt : u.hdr.length < 2 ^ 64 := by omega
  obtain ⟨hbeqz, hbnez⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hhdr_lt
  cases hemp : u.hdr.isEmpty
  · simp only [hemp, Bool.not_false] at hbeqz hbnez
    have hne_hdr : u.hdr ≠ [] := List.isEmpty_eq_false_iff.mp hemp
    have henc_eq : Proto.encodeBytesField 3#32 u.hdr = [0x1a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 u.hdr.length) ++ u.hdr := by
      rw [etv2_encodeBytesField_3_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_all : bs3.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 u.hdr.length)).length + u.hdr.length ≤ cap.toNat := by
      rw [henc_eq] at hfit; dsimp only [bs3, bs2, bs1] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
    have hlt_tag : bs3.length < cap.toNat := by omega
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs3 hlt_tag hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b2 => ?_
    etv_cs (entry + 18446744073709422336#64); intro hinv5
    refine etv3_step_bytes_varint b A ext hvarint 0x1a#8 sp cap ptr (entry + 5132#64) bs3 u.hdr hemp hfit_all hcap hptr halign
      (F := (((a + 136#64) ↦₆₄ g.f3.cap) ∗ ((a + 144#64) ↦₆₄ g.f3.ptr) ∗ ((a + 152#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length)) ∗
        EncodedLen.vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗ optAuthenticatorPBPinnedAt A g.auth (a + 160#64) u.auth ∗ ((a + 208#64) ↦₆₄ u.epoch) ∗ F)
      s_an0 s_an s_an s_an s_an0 s_an s_an (hinv_4.trans hinv5) (by ac_rfl) ?_
    intro sm5 bs4 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5 hfit_mc hcmp_mc
    rcases hcsm5 with ⟨hm5_19, hm5_20, hm5_21, hm5_22, _, _, _, _, hm5_27, _, hm5_fp, _⟩
    simp only [arm64_norm, hx19_4, hx20_4, hx21_4, hx27_4, hfp_4] at hm5_19 hm5_20 hm5_21 hm5_22 hm5_27 hm5_fp
    etv_cs (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")); intro hinv6
    refine etv2_step_memcpy_slice b A ext hmemcpy sp cap ptr g.f3.cap g.f3.ptr (entry + 5172#64) bs4 u.hdr hemp hhdr_le halign
      (F := (((a + 136#64) ↦₆₄ g.f3.cap) ∗ ((a + 144#64) ↦₆₄ g.f3.ptr) ∗ ((a + 152#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length)) ∗
        optAuthenticatorPBPinnedAt A g.auth (a + 160#64) u.auth ∗ ((a + 208#64) ↦₆₄ u.epoch) ∗ F)
      s_an0 s_an s_an s_an s_an0 s_an s_an s_an hhdr_lt (hinv_m5.trans hinv6) (by ac_rfl) ?_
    intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
    rcases hcsm6 with ⟨hm6_19, _, hm6_21, hm6_22, hm6_23, _, _, _, hm6_27, _, hm6_fp, _⟩
    simp only [arm64_norm, hm5_19, hm5_21, hm5_22, hm5_27, hm5_fp] at hm6_19 hm6_21 hm6_22 hm6_23 hm6_27 hm6_fp
    etv_cs (entry + 5180#64); intro hinv7
    have hpack_mc := vecU8At_pack_slice A (sp - 120#64) cap ptr bs4 u.hdr hfit_mc hcap hptr hne_hdr
    have hbs_eq : bs4 ++ u.hdr = bs ++ Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u) := by
      rw [etv3_encodeOptHeaderReceived_some_eq, henc_eq]; dsimp only [bs4, bs3, bs2, bs1]; simp only [List.append_assoc]
    rw [h112, h104, hbs_eq] at hpack_mc
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ s_an s_an s_an s_an s_an s_an s_an s_an (hinv_m6.trans hinv7))
    dsimp only [headerReceivedPBPinnedAt, unchunked3PinnedAt]
    rw [h136_24, h136_72, EncodedLen.vecU8At_eq_header_sep_buf A (a + 136#64), vecHeader, h144, h152, ← hpack_mc]; ac_rfl
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have henc_nil : Proto.encodeBytesField 3#32 u.hdr = [] := by rw [etv2_encodeBytesField_3_eq, hemp]; simp only [↓reduceIte]
    etv_cs (entry + 5180#64); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ s_an s_an s_an s_an s_an s_an s_an s_an (hinv_4.trans hinv5))
    dsimp only [headerReceivedPBPinnedAt, unchunked3PinnedAt]
    rw [h136_24, h136_72, EncodedLen.vecU8At_eq_header_sep_buf A (a + 136#64), vecHeader, h144, h152, etv3_encodeOptHeaderReceived_some_eq, henc_nil]
    dsimp only [bs3, bs2, bs1]; simp only [List.append_nil, List.append_assoc]

theorem step_encodeToVec_v1_headerReceived {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) {s0 s : State}
    (hhrLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709529772#64) (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709536996#64) (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441712#64) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext) (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")) etvMemcpyRegionSpec)
    (hpolyDec : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442356#64) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : Unchunked3PBGhost × PolynomialDecoderPBGhost) (v : V1State.Chunked.HeaderReceived) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.headerReceived v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.headerReceived v)).length ≤ cap.toNat) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 2908#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optHeaderReceivedPBPinnedAt A g.1 (a + 136#64) v.uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (a + 216#64) v.receivingEk) ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm (((optHeaderReceivedPBPinnedAt A g.1 (a + 136#64) v.uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (a + 216#64) v.receivingEk) ∗
        vecU8At A (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.headerReceived v)) ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 2908 3008; etv_fetches b (Rust.withPanics ext) hfn 3860 3932
  etv_fetches b (Rust.withPanics ext) hfn 4916 4944; etv_fetches b (Rust.withPanics ext) hfn 5180 5196
  examples_hide_fetches; subst hP; rcases v with ⟨uc, receivingEk⟩
  rw [etv3_encodeInnerState_headerReceived_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x3a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optHeaderReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (a + 216#64) receivingEk ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optHeaderReceivedCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧ (optHeaderReceivedCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyDecCap g.2 receivingEk + 1#64 == 0#64) = !receivingEk.isSome ∧ (optPolyDecCap g.2 receivingEk + 1#64 != 0#64) = receivingEk.isSome))
    (fun R' hm => ⟨optHeaderReceivedPBPinnedAt_cap_bounds (p := a + 136#64)
        (R := optPolynomialDecoderPBPinnedAt A g.2 (a + 216#64) receivingEk ∗ vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
      optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 216#64)
        (R := optHeaderReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗ vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x3a#8 hlt1 hcap hptr; rw [h112, h104] at hpack
  suffices h3864 : ∀ sm1 : State, sm1.pc = entry + 3864#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x20 = a → sm1.readReg64 .x22 = optHeaderReceivedCap g.1 uc →
      sm1.readReg64 .x23 = BitVec.ofNat 64 (optHeaderReceivedPBFieldEncodedLen uc) → sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrProgAtExt b ext) ret sm1 (((optHeaderReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (a + 216#64) receivingEk) ∗
        vecU8At A (sp - 120#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optHeaderReceivedPBPinnedAt_eq A g.1 (a + 136#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      etv_cs (entry + 3864#64); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3864 _ s_an s_an s_an s_an s_an s_an (by simp only [optHeaderReceivedPBFieldEncodedLen, arm64_norm, *]) s_an s_an (hinv0.trans hinv1))
      rw [← optHeaderReceivedPBPinnedAt_eq A g.1 (a + 136#64) none, ← hpack]
    | some u =>
      rw [optHeaderReceivedPBPinnedAt_eq A g.1 (a + 136#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : headerReceivedPBEncodedLen u < 2 ^ 64 ∧ optHeaderReceivedPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optHeaderReceivedPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (headerReceivedPBEncodedLen u)) < optHeaderReceivedPBFieldEncodedLen (some u) := by dsimp only [optHeaderReceivedPBFieldEncodedLen]; omega
      have ⟨⟨hu1, hu2, hu3, hu4, hu5⟩, hult_u, hopt_u_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt, etv3_bv_optHeaderReceived_some_eq u⟩ : _ ∧ _ ∧ _)
      etv_cs (entry + 18446744073709529772#64); intro hinv1; rw [← optHeaderReceivedPBPinnedAt_eq A g.1 (a + 136#64) (some u)]
      refine step_etv_leaf_encLen16_call hres b ext (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen hhrLen (a + 136#64) sp (entry + 2964#64) g.1 u hu_fit
        (F := optPolynomialDecoderPBPinnedAt A g.2 (a + 216#64) receivingEk ∗ vecU8At A (sp - 120#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool ∗ F)
        s_an0 s_an s_an halign s_an s_an0 s_an (hinv0.trans hinv1) (by rw [← hpack]; dsimp only [optHeaderReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
      rcases hcsm1 with ⟨_, hm20, _, hm22, _, _, _, _, hm27, _, hmfp, _⟩; simp only [arm64_norm, hx20] at hm20 hm22 hm27 hmfp
      etv_cs (entry + 3864#64); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h3864 _ s_an s_an s_an s_an s_an s_an s_an s_an s_an (hinv_m1.trans hinv2))
      dsimp only [optHeaderReceivedPBPinnedAt]; ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx20_1 hx22_1 hx23_1 hx27_1 hfp_1 hinv_1
  suffices h4920 : ∀ sm2 : State, sm2.pc = entry + 4920#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingEk) →
      sm2.readReg64 .x19 = optPolyDecCap g.2 receivingEk → sm2.readReg64 .x20 = a → sm2.readReg64 .x21 = a + 216#64 →
      sm2.readReg64 .x22 = optHeaderReceivedCap g.1 uc → sm2.readReg64 .x23 = BitVec.ofNat 64 (optHeaderReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrProgAtExt b ext) ret sm2 (((optHeaderReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (a + 216#64) receivingEk) ∗
        vecU8At A (sp - 120#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases receivingEk with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 216#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      etv_cs (entry + 4920#64); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4920 _ s_an s_an s_an s_an (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *]) s_an s_an s_an s_an s_an s_an s_an (hinv_1.trans hinv2))
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 216#64) none]
    | some dec =>
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 216#64) (some dec)]; simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have ⟨hdec_fit, hopt_d_lt⟩ : polynomialDecoderPBEncodedLen dec < 2 ^ 64 ∧ optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialDecoderPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_d_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) < optPolynomialDecoderPBFieldEncodedLen (some dec) := by dsimp only [optPolynomialDecoderPBFieldEncodedLen]; omega
      have ⟨⟨hd1, hd2, hd3, hd4, hd5⟩, hult_d, hopt_d_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_d_lt hopt_d_lt, ult_of_lt_of_fit hvar_d_lt hopt_d_lt, bv_optPolyDec_some_eq dec⟩ : _ ∧ _ ∧ _)
      etv_cs (entry + 18446744073709536996#64); intro hinv2; rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 216#64) (some dec)]
      refine step_etv_leaf_encLen16_call hres b ext (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen hpolyDecLen (a + 216#64) sp (entry + 3888#64) g.2 dec hdec_fit
        (F := optHeaderReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗ vecU8At A (sp - 120#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool ∗ F)
        s_an0 s_an s_an halign s_an s_an0 s_an (hinv_1.trans hinv2) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, _, _, hm2_27, _, hm2_fp, _⟩
      simp only [arm64_norm, hx20_1, hx22_1, hx23_1, hx27_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_27 hm2_fp
      etv_cs (entry + 4920#64); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h4920 _ s_an s_an s_an s_an s_an s_an s_an s_an s_an s_an s_an s_an (hinv_m2.trans hinv3))
      dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx27_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen receivingEk) (b := optHeaderReceivedPBFieldEncodedLen uc) (c := v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)) rfl hsub_len
  etv_cs (entry + 18446744073709422336#64); intro hinv3
  set bs1 := (bs ++ [0x3a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)))
  refine step_etv_encode_varint_call b A ext hvarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)))
    (sp - 120#64) cap ptr sp (entry + 4936#64) (bs ++ [0x3a#8]) hfit_var
    (F := (optHeaderReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (a + 216#64) receivingEk) ∗ F)
    s_an0 s_an s_an halign s_an s_an0 s_an s_an (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, _, _, _, _, hm3_27, _, hm3_fp, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx27_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_27 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 uc
  suffices h5180 : ∀ sm4 : State, sm4.pc = entry + 5180#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = optPolyDecCap g.2 receivingEk → sm4.readReg64 .x21 = a + 216#64 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrProgAtExt b ext) ret sm4 (((optHeaderReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (a + 216#64) receivingEk) ∗
        vecU8At A (sp - 120#64) cap ptr bs2 ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      etv_cs (entry + 5180#64); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h5180 _ s_an s_an s_an s_an s_an s_an s_an s_an (hinv_m3.trans hinv4))
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hu_lt : headerReceivedPBEncodedLen u < 2 ^ 64 := by dsimp only [v1StateInnerPayloadEncodedLen, optHeaderReceivedPBFieldEncodedLen] at hsub_len; omega
      have hfit_u : bs1.length + (Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u)).length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      etv_cs (entry + 4944#64); intro hinv4
      refine etv3_step_headerReceived_some hres b A ext hfn hhrLen hvarint hauthEnc hmemcpy a sp cap ptr g.1 u bs1 hu_lt hfit_u hcap hptr halign
        (F := optPolynomialDecoderPBPinnedAt A g.2 (a + 216#64) receivingEk ∗ F)
        s_an0 s_an s_an s_an s_an (hinv_m3.trans hinv4) (by dsimp only [bs1, optHeaderReceivedPBPinnedAt]; simp only [List.append_assoc]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_27 hm4_fp hinv_m4
      simp only [arm64_norm, hm3_19, hm3_21, hm3_27, hm3_fp] at hm4_19 hm4_21 hm4_27 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h5180 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_27 hm4_fp hinv_m4)
      dsimp only [bs2, optHeaderReceivedPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx21_4 hx27_4 hfp_4 hinv_4
  cases receivingEk with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
    etv_cs (entry + 1808#64); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ s_an s_an s_an s_an s_an s_an (hinv_4.trans hinv5))
    rw [etv3_encodeInnerState_headerReceived_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    etv_cs (entry + 5196#64); intro hinv5
    refine step_encodeToVec_tail_5196_polyDec b A ext hfn hpolyDec 2#32 (a + 216#64) sp cap ptr g.2 dec bs2 hfit_dec halign
      (F := optHeaderReceivedPBPinnedAt A g.1 (a + 136#64) uc ∗ F) s_an0 s_an s_an s_an s_an s_an s_an (hinv_4.trans hinv5) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5
    simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5)
    rw [etv3_encodeInnerState_headerReceived_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, optPolynomialDecoderPBPinnedAt, List.append_assoc]; ac_rfl


end CryptoVerification.SpqrV1.Prost.EncodeToVec
