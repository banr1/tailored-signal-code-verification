/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 8 (`EkReceivedCt1Sampled`, `+1764`) — Part A

Helpers and error exits for Variant 8 (`InnerState.ekReceivedCt1Sampled`, tag `0x8000000000000008#64`,
jump-table target `+1764`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
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

@[local simp, local arm64_norm, local wp_norm]
theorem v8_bv_sub_sub_lit (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v8_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## 1. Pure Model Reduction Lemmas for `InnerState.ekReceivedCt1Sampled` -/

theorem v8_states_from_pb_uc_none_eq {F : ShaCompress}
    (sendingCt1 : Option PolynomialEncoder) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekReceivedCt1Sampled { uc := none, sendingCt1 := sendingCt1 }) } =
    .error (.err .stateDecode) := rfl

theorem v8_states_from_pb_len_err_eq {F : ShaCompress}
    (u : V1State.Unchunked.Ct1SentEkReceived)
    (sendingCt1 : Option PolynomialEncoder)
    (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = false) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) } =
    .error (.err .stateDecode) := by
  simp only [States.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
    Unchunked.SendCt.Ct1SentEkReceived.from_pb, hlen, Bool.false_eq_true, ↓reduceIte,
    Bind.bind, Except.bind, Functor.map, Except.map]

theorem v8_states_from_pb_auth_none_eq {F : ShaCompress}
    (u : V1State.Unchunked.Ct1SentEkReceived)
    (sendingCt1 : Option PolynomialEncoder)
    (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = true)
    (hauth : u.auth = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) } =
    .error (.err .stateDecode) := by
  simp only [States.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
    Unchunked.SendCt.Ct1SentEkReceived.from_pb, hlen, hauth, ↓reduceIte,
    Bind.bind, Except.bind, Functor.map, Except.map]

theorem v8_states_from_pb_sendingCt1_none_eq {F : ShaCompress}
    (u : V1State.Unchunked.Ct1SentEkReceived)
    (auth : ProtoAuthenticator)
    (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = true)
    (hauth : u.auth = some auth) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := none }) } =
    .error (.err .stateDecode) := by
  simp only [States.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
    Unchunked.SendCt.Ct1SentEkReceived.from_pb, hlen, hauth, ↓reduceIte,
    encoderFromPbStateDecode, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v8_states_from_pb_sendingCt1_err_eq {F : ShaCompress}
    (u : V1State.Unchunked.Ct1SentEkReceived)
    (auth : ProtoAuthenticator)
    (pbEnc : PolynomialEncoder)
    (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = true)
    (hauth : u.auth = some auth)
    (henc : fromPbResult (pbToProtoPolyEncoder pbEnc) = .error .serializationInvalid) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := some pbEnc }) } =
    .error (.err .stateDecode) := by
  have henc' := fromPb_eq_ok (pbToProtoPolyEncoder pbEnc)
  rw [henc] at henc'
  simp only [States.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
    Unchunked.SendCt.Ct1SentEkReceived.from_pb, hlen, hauth, ↓reduceIte,
    encoderFromPbStateDecode, spqrPolyApi, henc', StatesResult.ofPanic, Except.mapError,
    Bind.bind, Except.bind, Functor.map, Except.map]

theorem v8_states_from_pb_ok_eq {F : ShaCompress}
    (u : V1State.Unchunked.Ct1SentEkReceived)
    (auth : ProtoAuthenticator)
    (pbEnc : PolynomialEncoder)
    (enc : PolyEncoder)
    (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = true)
    (hauth : u.auth = some auth)
    (henc : fromPbResult (pbToProtoPolyEncoder pbEnc) = .ok enc) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := some pbEnc }) } =
    .ok (.ekReceivedCt1Sampled
      { uc := { epoch := u.epoch, auth := Authenticator.fromPb auth,
                es := u.es, ek := u.ek, ct1 := u.ct1 }
        sending_ct1 := enc }) := by
  have henc' := fromPb_eq_ok (pbToProtoPolyEncoder pbEnc)
  rw [henc] at henc'
  simp only [States.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
    Unchunked.SendCt.Ct1SentEkReceived.from_pb, hlen, hauth, ↓reduceIte,
    encoderFromPbStateDecode, spqrPolyApi, spqrAuthApi, henc', StatesResult.ofPanic, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]

/-! ## 2. Error Exit at `+4240` and `sendingCt1` Drop at `+4216` / `+4212` -/

/-- Shared `Err(StateDecode)` exit at `+4240` (`0x5b134 -> +60 -> s0.x30`):
when `x20` has low byte `spqrErrorByte .stateDecode` (`0#8`) and `x19 = out`,
sets `x8 = noneCap`, writes `x20` to `[out + 8]`, `x8, x28` to `[out + 16..32]`, and branches to `+60`. -/
theorem v8_err_4240
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4240#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : (s1.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
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
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 60#64)
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
  · states_from_pb_fetches_range b (Rust.withPanics ext) 4240 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
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
    exact states_from_pb_epilogue_60 s0 s2 out .stateDecode v0 Rest
      hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

theorem v8_merge_stack_1520_56_728 (fsp : BitVec 64) :
    memRegion fsp 1520 ∗
      memRegion (fsp + 1520#64) 56 ∗
      memRegion (fsp + 1576#64) 728 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

/-- Drop `Option<ProtoPolynomialEncoder>` at `fsp + 1520` (`s0.sp - 880`) and return
`Err(StateDecode)` (`+4216 -> +4240 -> s0.x30`). -/
theorem v8_drop_sendingCt1_4216
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4216#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : (s1.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
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
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4240#64)
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
    · states_from_pb_fetches_range b (Rust.withPanics ext) 4216 12
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, v1_optProtoPolyEncoderWordsAt,
        noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
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
      have herr := v8_err_4240 (A := A) (F := F) s0 s2 out (A.pool ∗ Rest)
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 htr2
      refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩
  | some pbEnc =>
    have hpack := v1_optProtoPolyEncoderAt_pack_some A (s0.sp - 2400#64 + 1520#64) pbEnc
      w0 w8 w16 w24 w32 w40 w48
    have hne := cap_add_one_beq_zero_false hw0_cond
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hdrop := v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb hA
    simp only [dropProtoPolyEncoderSpec] at hdrop
    have h880 : s0.sp - 2400#64 + 1520#64 = s0.sp - 880#64 := by bv_omega
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4236#64)
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
    · states_from_pb_fetches_range b (Rust.withPanics ext) 4216 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, v1_optProtoPolyEncoderWordsAt,
        BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
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
    · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx20_2, htr2⟩
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4240#64)
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
      · states_from_pb_fetches_range b (Rust.withPanics ext) 4236 8
        dsimp only [tripleRatchetProgAtExt, statesFromPbName,
          BitVec.ofNat_eq_ofNat] at hdrop hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
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
        have herr := v8_err_4240 (A := A) (F := F) s0 s3 out (A.pool ∗ Rest)
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 htr3
        refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-- Error exit at `+4212` (`0x5b118 -> +4216 -> s0.x30`): sets `x20 = 0`, drops `sendingCt1`, and returns `Err(StateDecode)`. -/
theorem v8_drop_sendingCt1_4212
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4212#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
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
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4216#64)
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
  · states_from_pb_fetches_range b (Rust.withPanics ext) 4212 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, spqrErrorByte,
      BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, htr2⟩
    exact v8_drop_sendingCt1_4216 (A := A) (F := F) hA s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48 Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 htr2

/-! ## 3. Word Unpacking & Heap Predicates for `uc` (`128`B) and `pbA` (`184`B) -/

/-- Sixteen 64-bit words of a 128-byte `Option<V1State.Unchunked.Ct1SentEkReceived>` at `a`. -/
def v8_ucWordsAt (a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64) : SepProp :=
  (a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ u24) ∗
  ((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ u48) ∗
  ((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ u72) ∗
  ((a + 72#64) ↦₆₄ u80) ∗ ((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96) ∗
  ((a + 96#64) ↦₆₄ u104) ∗ ((a + 104#64) ↦₆₄ u112) ∗ ((a + 112#64) ↦₆₄ u120) ∗
  ((a + 120#64) ↦₆₄ u128)

theorem v8_ucWordsAt_entails_128
    (a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64) :
    v8_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ⊢
      memRegion a 128 := by
  unfold v8_ucWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

/-- Eleven 128-bit (`↦₁₂₈`) chunks plus one 64-bit word covering `pbA + 8..192` (`184` bytes). -/
def v8_pb128At (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  ((pbA + 8#64) ↦₁₂₈ (u16 ++ u8)) ∗
  ((pbA + 24#64) ↦₁₂₈ (u32 ++ u24)) ∗
  ((pbA + 40#64) ↦₁₂₈ (u48 ++ u40)) ∗
  ((pbA + 56#64) ↦₁₂₈ (u64 ++ u56)) ∗
  ((pbA + 72#64) ↦₁₂₈ (u80 ++ u72)) ∗
  ((pbA + 88#64) ↦₁₂₈ (u96 ++ u88)) ∗
  ((pbA + 104#64) ↦₁₂₈ (u112 ++ u104)) ∗
  ((pbA + 120#64) ↦₁₂₈ (u128 ++ u120)) ∗
  ((pbA + 136#64) ↦₁₂₈ (w8 ++ w0)) ∗
  ((pbA + 152#64) ↦₁₂₈ (w24 ++ w16)) ∗
  ((pbA + 168#64) ↦₁₂₈ (w40 ++ w32)) ∗
  ((pbA + 184#64) ↦₆₄ w48)

theorem v8_uc_and_enc_words_eq_pb128
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
     w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
      v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 =
      v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
        w0 w8 w16 w24 w32 w40 w48 := by
  dsimp only [v8_ucWordsAt, v1_optProtoPolyEncoderWordsAt, v8_pb128At]
  simp only [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128, arm64_norm]

theorem v8_pb128_entails_full_224
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
     w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000008#64) ∗
      v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
        w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (pbA + 192#64) 32 ⊢
      memRegion pbA optProtoInnerStateSize := by
  rw [← v8_uc_and_enc_words_eq_pb128]
  have h128 := v8_ucWordsAt_entails_128 (pbA + 8#64)
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48
  have h224 : (pbA ↦₆₄ 0x8000000000000008#64) ∗
      memRegion (pbA + 8#64) 128 ∗
      memRegion (pbA + 136#64) 56 ∗
      memRegion (pbA + 192#64) 32 ⊢
      memRegion pbA optProtoInnerStateSize :=
    collapse_top <|
      collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (pbA ↦₆₄ 0x8000000000000008#64) ∗
    v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
    v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (pbA + 192#64) 32 by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_right (sepConj_mono h128 (sepConj_mono_left h56))) h224

/-! ## 4. Error Cleanup for `uc` (`es`, `ek`, `ct1`, `auth`) + `sendingCt1` (`+2100 -> +2148 -> +2208 -> +4216`) -/

theorem v8_merge_stack_896_128_496_1520 (fsp : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64) :
    memRegion fsp 896 ∗
      v8_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
      memRegion (fsp + 1024#64) 496 ⊢
      memRegion fsp 1520 := by
  have h128 := v8_ucWordsAt_entails_128 (fsp + 896#64)
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
  have hm : memRegion fsp 896 ∗ memRegion (fsp + 896#64) 128 ∗ memRegion (fsp + 1024#64) 496 ⊢
      memRegion fsp 1520 :=
    collapse_top <|
      collapse_step0 (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      Entails.refl _
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left h128)) hm

/-- Error transition `+2208 -> +4216 -> s0.x30`: sets `x20 = 0`, drops `sendingCt1` at `fsp + 1520`,
and returns `Err(StateDecode)`. -/
theorem v8_drop_sendingCt1_2208
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2208#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
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
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4216#64)
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
  · states_from_pb_fetches_range b (Rust.withPanics ext) 2208 20
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, spqrErrorByte,
      BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, htr2⟩
    exact v8_drop_sendingCt1_4216 (A := A) (F := F) hA s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48 Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 htr2

/-- Cleanup `es` (`x26 = u8`, `[fsp+904] = u16`), `ek` (`[fsp+920] = u32`, `[fsp+928] = u40`),
`ct1` (`[fsp+944] = u56`, `[fsp+952] = u64`), and `sendingCt1` at `fsp + 1520..1576`,
returning `Err(StateDecode)` (`+2148 -> +2208 -> +4216 -> s0.x30`). -/
theorem v8_drop_uc_and_sendingCt1_2148
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2148#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
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
  have hdealloc := v1_dealloc_ok_at_statesFromPb hA
  simp only [rustDeallocSpec] at hdealloc
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2168#64)
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
  · states_from_pb_fetches_range b (Rust.withPanics ext) 2148 20
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, v8_ucWordsAt, vecCapPtrDealloc,
      BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_cases hc1 : (u8 == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply
      refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2188#64)
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
    · states_from_pb_fetches_range b (Rust.withPanics ext) 2168 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, v8_ucWordsAt, vecCapPtrDealloc,
        BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      by_cases hc2 : (u32 == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply
        refine EncoderFromPb.align_pre (by rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, htr3⟩
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2208#64)
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
      · states_from_pb_fetches_range b (Rust.withPanics ext) 2188 20
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, v8_ucWordsAt, vecCapPtrDealloc,
          BitVec.ofNat_eq_ofNat] at hdealloc hpc3 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
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
      · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, htr4⟩
        exact v8_drop_sendingCt1_2208 (A := A) (F := F) hA s0 s4 out optEnc
          w0 w8 w16 w24 w32 w40 w48 Rest hsp0_align hpc4 hrun4 hsp4 hx19_4 htr4

/-- Cleanup `optAuth` (`[fsp+968..1016] = u80..u120`), `es`, `ek`, `ct1`, and `sendingCt1`,
returning `Err(StateDecode)` (`+2100 -> +2148 -> +2208 -> +4216 -> s0.x30`). -/
theorem v8_drop_uc_and_sendingCt1_2100
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optAuth : Option ProtoAuthenticator)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2100#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx26_1 : s1.readReg64 .x26 = u8)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
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
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2148#64)
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
    · states_from_pb_fetches_range b (Rust.withPanics ext) 2100 12
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, v8_ucWordsAt, noneCap,
        BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps; wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
      exact v8_drop_uc_and_sendingCt1_2148 (A := A) (F := F) hA s0 s2 out
        u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u128
        optEnc w0 w8 w16 w24 w32 w40 w48 Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2
  | some auth =>
    dsimp only [v1_optProtoAuthHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; rintro ⟨hu80, _, _⟩
    have hcmn : (u80 + 1#64 == 0#64) = false :=
      Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hu80)
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
    have hdealloc := v1_dealloc_ok_at_statesFromPb hA
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
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2128#64)
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
    · states_from_pb_fetches_range b (Rust.withPanics ext) 2100 28
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, v8_ucWordsAt, vecCapPtrDealloc,
        BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      by_cases hc_r : (u80 == 0#64) = true <;>
        simp only [hc_r, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply
        refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2148#64)
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
      · states_from_pb_fetches_range b (Rust.withPanics ext) 2128 20
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, v8_ucWordsAt, vecCapPtrDealloc,
          BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
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
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
        exact v8_drop_uc_and_sendingCt1_2148 (A := A) (F := F) hA s0 s3 out
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          optEnc w0 w8 w16 w24 w32 w40 w48 Rest hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3

/-! ## 5. Error Cleanup when `u.auth = none` (`+10544 -> +2208 -> +4216 -> s0.x30`) -/

theorem v8_drop_glue_ct1_sent_ek_received_ok_at_statesFromPb {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName +
        18446744073709497836#64)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A) := by
  have h := drop_proto_unchunked_ct1_sent_ek_received_ok_ext hA.dealloc
  have haddr : (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName +
      18446744073709497836#64 =
      (dropProgAtExt b ext).fnAddr dropProtoUnchunkedCt1SentEkReceivedName := by
    simp only [tripleRatchetProgAtExt, dropProgAtExt, Program.fnAddr_rebase,
      statesFromPbName, dropProtoUnchunkedCt1SentEkReceivedName,
      statesFromPb_fnOff, fnOff_drop_proto_ct1_sent_ek_received]
    bv_omega
  rw [haddr]
  exact h

theorem v8_stackAt_encoder_split_dropStack32 (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack =
      memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 :=
  ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)

theorem v8_pack_protoUnchunkedCt1SentEkReceived_auth_none
    (A : RustAlloc) (a : BitVec 64) (u : V1State.Unchunked.Ct1SentEkReceived)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u88 u96 u104 u112 u120 : BitVec 64)
    (hu8 : u8.toNat < 2 ^ 63) (hu24 : u24 = (u.es.length : BitVec 64))
    (hu32 : u32.toNat < 2 ^ 63) (hu48 : u48 = (u.ek.length : BitVec 64))
    (hu56 : u56.toNat < 2 ^ 63) (hu72 : u72 = (u.ct1.length : BitVec 64))
    (hauth : u.auth = none) :
    v8_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u.epoch ∗
      vecU8Payload A u8 u16 u.es ∗
      vecU8Payload A u32 u40 u.ek ∗
      vecU8Payload A u56 u64 u.ct1 ⊢
      protoUnchunkedCt1SentEkReceivedAt A a u := by
  subst hu24 hu48 hu72
  unfold protoUnchunkedCt1SentEkReceivedAt
  rw [hauth, optProtoAuthenticatorAt_none]
  have hes : (a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ (u.es.length : BitVec 64)) ∗
      vecU8Payload A u8 u16 u.es ⊢ vecU8 A a u.es := by
    unfold vecU8
    refine Entails.sepExists_right u8 (Entails.sepExists_right u16 ?_)
    dsimp only [vecU8At, vecHeader, vecU8Payload]
    exact Entails.of_eq (by simp only [arm64_norm]; ac_rfl)
  have hek : ((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ (u.ek.length : BitVec 64)) ∗
      vecU8Payload A u32 u40 u.ek ⊢ vecU8 A (a + 24#64) u.ek := by
    unfold vecU8
    refine Entails.sepExists_right u32 (Entails.sepExists_right u40 ?_)
    dsimp only [vecU8At, vecHeader, vecU8Payload]
    exact Entails.of_eq (by simp only [arm64_norm]; ac_rfl)
  have hct1 : ((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ (u.ct1.length : BitVec 64)) ∗
      vecU8Payload A u56 u64 u.ct1 ⊢ vecU8 A (a + 48#64) u.ct1 := by
    unfold vecU8
    refine Entails.sepExists_right u56 (Entails.sepExists_right u64 ?_)
    dsimp only [vecU8At, vecHeader, vecU8Payload]
    exact Entails.of_eq (by simp only [arm64_norm]; ac_rfl)
  have h40 : ((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96) ∗ ((a + 96#64) ↦₆₄ u104) ∗
      ((a + 104#64) ↦₆₄ u112) ∗ ((a + 112#64) ↦₆₄ u120) ⊢ memRegion (a + 72#64 + 8#64) 40 := by
    have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
    have h88 : a + 88#64 = (a + 80#64) + 8#64 := by bv_omega
    have h96 : a + 96#64 = (a + 80#64) + 16#64 := by bv_omega
    have h104 : a + 104#64 = (a + 80#64) + 24#64 := by bv_omega
    have h112 : a + 112#64 = (a + 80#64) + 32#64 := by bv_omega
    rw [h80, h88, h96, h104, h112]
    exact collapse_top <|
      collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _
  refine Entails.trans (Entails.of_eq (show _ =
    ((a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ (u.es.length : BitVec 64)) ∗
      vecU8Payload A u8 u16 u.es) ∗
    (((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ (u.ek.length : BitVec 64)) ∗
      vecU8Payload A u32 u40 u.ek) ∗
    (((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ (u.ct1.length : BitVec 64)) ∗
      vecU8Payload A u56 u64 u.ct1) ∗
    ((a + 72#64) ↦₆₄ noneCap) ∗
    (((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96) ∗ ((a + 96#64) ↦₆₄ u104) ∗
      ((a + 104#64) ↦₆₄ u112) ∗ ((a + 112#64) ↦₆₄ u120)) ∗
    ((a + 120#64) ↦₆₄ u.epoch) by
      dsimp only [v8_ucWordsAt]; ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono hes (sepConj_mono hek (sepConj_mono hct1 (sepConj_mono_right (sepConj_mono_left h40))))) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Error path at `+10544 -> +2208 -> +4216 -> s0.x30` when `u.auth = none`:
calls `0x4ce90` (`drop_glue::<ProtoUnchunkedCt1SentEkReceived>`) on `fsp + 896`, then drops `sendingCt1`
and returns `Err(StateDecode)`. -/
theorem v8_drop_uc_auth_none_10544
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out : BitVec 64) (u : V1State.Unchunked.Ct1SentEkReceived)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u88 u96 u104 u112 u120 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63) (hu24 : u24 = (u.es.length : BitVec 64))
    (hu32 : u32.toNat < 2 ^ 63) (hu48 : u48 = (u.ek.length : BitVec 64))
    (hu56 : u56.toNat < 2 ^ 63) (hu72 : u72 = (u.ct1.length : BitVec 64))
    (hauth : u.auth = none)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10544#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
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
  have hdrop := v8_drop_glue_ct1_sent_ek_received_ok_at_statesFromPb hA
  simp only [dropProtoUnchunkedCt1SentEkReceivedSpec] at hdrop
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
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2208#64)
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
  · states_from_pb_fetches_range b (Rust.withPanics ext) 10544 12
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, protoUnchunkedCt1SentEkReceivedSize,
      BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
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
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    exact v8_drop_sendingCt1_2208 (A := A) (F := F) hA s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48 Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2

end CryptoVerification.SpqrV1.States.FromPb
