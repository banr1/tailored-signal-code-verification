/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 10 (`Ct2Sampled`, `+1632`) — Early Errors & `Authenticator` Cloning

Proves the `+1632` early error exits (`s.uc = none` and `auth = none`), original `Authenticator`
buffer deallocation (`+5688 -> +5728`), and `rootKey` (`+1720 -> +5540`) / `macKey` (`+5540 -> +5688`)
cloning steps.
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
open CryptoVerification.Swarm.IC10.Variant10a

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::from_pb")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")

/-! ## 1. `Ct2Sampled` (`+1632`) Early Error Paths (`s.uc = none` and `auth = none`) -/

theorem v10_protoChunkedCt2SampledAt_uc_none (A : RustAlloc) (pbA : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB) :
    protoChunkedCt2SampledAt A (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } =
      optProtoPolynomialEncoderAt A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
      ((pbA + 64#64) ↦₆₄ none2Cap) ∗
      memRegion (pbA + 72#64) 48 := by
  dsimp only [protoChunkedCt2SampledAt, optProtoUnchunkedCt2SentAt]
  have h64 : (pbA + 8#64) + 56#64 = pbA + 64#64 := by bv_omega
  have h72 : (pbA + 64#64) + 8#64 = pbA + 72#64 := by bv_omega
  rw [h64, h72]

theorem v10_protoChunkedCt2SampledAt_auth_none (A : RustAlloc) (pbA epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB) :
    protoChunkedCt2SampledAt A (pbA + 8#64)
        { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } =
      optProtoPolynomialEncoderAt A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
      ((pbA + 64#64) ↦₆₄ noneCap) ∗
      memRegion (pbA + 72#64) 40 ∗
      ((pbA + 112#64) ↦₆₄ epoch) := by
  dsimp only [protoChunkedCt2SampledAt, optProtoUnchunkedCt2SentAt, protoUnchunkedCt2SentAt,
    optProtoAuthenticatorAt]
  have h64 : (pbA + 8#64) + 56#64 = pbA + 64#64 := by bv_omega
  have h72 : (pbA + 64#64) + 8#64 = pbA + 72#64 := by bv_omega
  have h112 : (pbA + 64#64) + 48#64 = pbA + 112#64 := by bv_omega
  rw [h64, h72, h112]
  ac_rfl

@[simp]
theorem v10_states_from_pb_ct2Sampled_uc_none (F : ShaCompress)
    (sendingCt2 : Option PolynomialEncoderPB) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct2Sampled { sendingCt2 := sendingCt2, uc := none }) } =
      .error (.err .stateDecode) := rfl

@[simp]
theorem v10_states_from_pb_ct2Sampled_auth_none (F : ShaCompress) (epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct2Sampled
          { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } }) } =
      .error (.err .stateDecode) := rfl

theorem v10_fsp_unsplit_0 (fsp : BitVec 64) :
    (fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 2296 ⊢
      memRegion fsp 2304 := by
  rw [ProofLib.memRegion_split fsp 8 2296 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion fsp 0#64)

theorem v10_ct2Sent_expose_pre_uc_none (A : RustAlloc) (fsp out pbA b : BitVec 64)
    (s0 : State) (sendingCt2 : Option PolynomialEncoderPB) :
    stackAt fsp encoderFromPbStack ∗
      (fsp ↦₆₄ 0#64) ∗
      memRegion (fsp + 8#64) 2296 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       protoChunkedCt2SampledAt A (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
       memRegion (pbA + 120#64) 104) ∗
      statesFromPbJumpTableAt b ∗
      A.pool ⊢
    ∃∗ cap_enc : BitVec 64,
      ⌜v10_optEncoderCapProp cap_enc (sendingCt2.map pbToProtoPolyEncoder)⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       memRegion fsp 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 8#64) ↦₆₄ cap_enc) ∗
       v10_optProtoPolyEncoderTail A (pbA + 8#64) cap_enc (sendingCt2.map pbToProtoPolyEncoder) ∗
       ((pbA + 64#64) ↦₆₄ none2Cap) ∗
       memRegion (pbA + 72#64) 48 ∗
       memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTableAt b ∗
       A.pool) := by
  rw [v10_protoChunkedCt2SampledAt_uc_none]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ((fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 2296) ∗
      optProtoPolynomialEncoderAt A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
      (stackAt fsp encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 64#64) ↦₆₄ none2Cap) ∗
       memRegion (pbA + 72#64) 48 ∗
       memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTableAt b ∗
       A.pool) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono (v10_fsp_unsplit_0 fsp)
      (sepConj_mono_left (v10_optProtoPolyEncoder_expose_cap A (pbA + 8#64)
        (sendingCt2.map pbToProtoPolyEncoder)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro cap_enc
  refine Entails.sepExists_right cap_enc ?_
  exact Entails.of_eq (by ac_rfl)

theorem v10_ct2Sent_expose_pre_auth_none (A : RustAlloc) (fsp out pbA epoch b : BitVec 64)
    (s0 : State) (sendingCt2 : Option PolynomialEncoderPB) :
    stackAt fsp encoderFromPbStack ∗
      (fsp ↦₆₄ 0#64) ∗
      memRegion (fsp + 8#64) 2296 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       protoChunkedCt2SampledAt A (pbA + 8#64)
         { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
       memRegion (pbA + 120#64) 104) ∗
      statesFromPbJumpTableAt b ∗
      A.pool ⊢
    ∃∗ cap_enc : BitVec 64,
      ⌜v10_optEncoderCapProp cap_enc (sendingCt2.map pbToProtoPolyEncoder)⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       memRegion fsp 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 8#64) ↦₆₄ cap_enc) ∗
       v10_optProtoPolyEncoderTail A (pbA + 8#64) cap_enc (sendingCt2.map pbToProtoPolyEncoder) ∗
       ((pbA + 64#64) ↦₆₄ noneCap) ∗
       memRegion (pbA + 72#64) 40 ∗
       ((pbA + 112#64) ↦₆₄ epoch) ∗
       memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTableAt b ∗
       A.pool) := by
  rw [v10_protoChunkedCt2SampledAt_auth_none]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ((fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 2296) ∗
      optProtoPolynomialEncoderAt A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
      (stackAt fsp encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 64#64) ↦₆₄ noneCap) ∗
       memRegion (pbA + 72#64) 40 ∗
       ((pbA + 112#64) ↦₆₄ epoch) ∗
       memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTableAt b ∗
       A.pool) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono (v10_fsp_unsplit_0 fsp)
      (sepConj_mono_left (v10_optProtoPolyEncoder_expose_cap A (pbA + 8#64)
        (sendingCt2.map pbToProtoPolyEncoder)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro cap_enc
  refine Entails.sepExists_right cap_enc ?_
  exact Entails.of_eq (by ac_rfl)

private theorem v10_ct2Sent_err_1632_uc_none_v10a
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : V10Alloc b A ext)
    (s0 s1 : State) (out pbA : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1632#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (v10_ct2Sent_expose_pre_uc_none A (s0.sp - 2400#64) out pbA b s0 sendingCt2) ?_
  apply ProofLib.SepWP.exists_left; intro cap_enc
  apply ProofLib.SepWP.pure_elim; intro hcap
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2064#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoPolynomialEncoderAt A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
      A.pool ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       memRegion (pbA + 64#64) 160 ∗
       statesFromPbJumpTableAt b))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = pbA + 8#64 ∧
      sm.readReg64 .x22 = cap_enc ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 1632 20
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat, none2Cap] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hunexp := v10_optProtoPolyEncoder_unexpose_cap A (pbA + 8#64) cap_enc
        (sendingCt2.map pbToProtoPolyEncoder)
      have hpb64 := v10_pb_64_none_entails_160 pbA
      unfold none2Cap at hpb64
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 8#64) ↦₆₄ cap_enc) ∗
           v10_optProtoPolyEncoderTail A (pbA + 8#64) cap_enc (sendingCt2.map pbToProtoPolyEncoder)) ∗
          (((pbA + 64#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
           memRegion (pbA + 72#64) 48 ∗
           memRegion (pbA + 120#64) 104) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           (pbA ↦₆₄ 0x800000000000000a#64) ∗
           statesFromPbJumpTableAt b ∗
           A.pool) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hunexp (sepConj_mono_left hpb64)) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx22_2, htr2⟩
    have hx22_prop : match sendingCt2.map pbToProtoPolyEncoder with
        | none => s2.readReg64 .x22 = noneCap
        | some _ => (s2.readReg64 .x22).toNat < 2 ^ 63 := by
      rw [hx22_2]
      exact hcap
    have h2064 := v10_states_from_pb_err_2064_v10a (F := F) hA s0 s2 out (pbA + 8#64)
      (sendingCt2.map pbToProtoPolyEncoder)
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       memRegion (pbA + 64#64) 160 ∗
       statesFromPbJumpTableAt b)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx22_prop htr2
    refine SepWP.mono h2064 ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
    have hpb := v10_pb_tag_56_160_entails_224 pbA 0x800000000000000a#64
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 8#64) 56 ∗ memRegion (pbA + 64#64) 160) ∗
        (resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
         statesFromPbJumpTableAt b ∗
         A.pool ∗ stackAt s0.sp statesFromPbStack) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))

private theorem v10_ct2Sent_err_1632_auth_none_v10a
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : V10Alloc b A ext)
    (s0 s1 : State) (out pbA epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1632#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A (pbA + 8#64)
           { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (v10_ct2Sent_expose_pre_auth_none A (s0.sp - 2400#64) out pbA epoch b s0 sendingCt2) ?_
  apply ProofLib.SepWP.exists_left; intro cap_enc
  apply ProofLib.SepWP.pure_elim; intro hcap
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2064#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoPolynomialEncoderAt A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
      A.pool ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       memRegion (pbA + 64#64) 160 ∗
       statesFromPbJumpTableAt b))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = pbA + 8#64 ∧
      sm.readReg64 .x22 = cap_enc ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 1632 28
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat, noneCap] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hunexp := v10_optProtoPolyEncoder_unexpose_cap A (pbA + 8#64) cap_enc
        (sendingCt2.map pbToProtoPolyEncoder)
      have hpb64 := v10_pb_64_auth_none_entails_160 pbA epoch
      unfold noneCap at hpb64
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 8#64) ↦₆₄ cap_enc) ∗
           v10_optProtoPolyEncoderTail A (pbA + 8#64) cap_enc (sendingCt2.map pbToProtoPolyEncoder)) ∗
          (((pbA + 64#64) ↦₆₄ 0xffffffffffffffff#64) ∗
           memRegion (pbA + 72#64) 40 ∗
           ((pbA + 112#64) ↦₆₄ epoch) ∗
           memRegion (pbA + 120#64) 104) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           (pbA ↦₆₄ 0x800000000000000a#64) ∗
           statesFromPbJumpTableAt b ∗
           A.pool) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hunexp (sepConj_mono_left hpb64)) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx22_2, htr2⟩
    have hx22_prop : match sendingCt2.map pbToProtoPolyEncoder with
        | none => s2.readReg64 .x22 = noneCap
        | some _ => (s2.readReg64 .x22).toNat < 2 ^ 63 := by
      rw [hx22_2]
      exact hcap
    have h2064 := v10_states_from_pb_err_2064_v10a (F := F) hA s0 s2 out (pbA + 8#64)
      (sendingCt2.map pbToProtoPolyEncoder)
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       memRegion (pbA + 64#64) 160 ∗
       statesFromPbJumpTableAt b)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx22_prop htr2
    refine SepWP.mono h2064 ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
    have hpb := v10_pb_tag_56_160_entails_224 pbA 0x800000000000000a#64
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 8#64) 56 ∗ memRegion (pbA + 64#64) 160) ∗
        (resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
         statesFromPbJumpTableAt b ∗
         A.pool ∗ stackAt s0.sp statesFromPbStack) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))

theorem Ext4K.v10_ct2Sent_err_1632_uc_none
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s1 : State) (out pbA : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
         memRegion (pbA + 120#64) 104) ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_ct2Sent_err_1632_uc_none_v10a (.of_4k hA) s0 s1 out pbA
    sendingCt2 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

theorem Ext4K.v10_ct2Sent_err_1632_auth_none
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s1 : State) (out pbA epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A (pbA + 8#64)
           { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
         memRegion (pbA + 120#64) 104) ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_ct2Sent_err_1632_auth_none_v10a (.of_4k hA) s0 s1 out pbA epoch
    sendingCt2 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

theorem v10_ct2Sent_err_1632_uc_none
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s1 : State) (out pbA : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
         memRegion (pbA + 120#64) 104) ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_ct2Sent_err_1632_uc_none_v10a (.of_allocContracts hA) s0 s1 out pbA
    sendingCt2 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

theorem v10_ct2Sent_err_1632_auth_none
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s1 : State) (out pbA epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A (pbA + 8#64)
           { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
         memRegion (pbA + 120#64) 104) ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_ct2Sent_err_1632_auth_none_v10a (.of_allocContracts hA) s0 s1 out pbA epoch
    sendingCt2 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-! ## 2. Vector Payload & Deallocation Helpers (`+5688 -> +5728`) -/

theorem v10_vecU8Payload_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Payload A c p bs ⊢ vecCapPtrDealloc A c p := by
  unfold vecU8Payload vecCapPtrDealloc
  apply Entails.pure_left; intro ⟨hle, _, _⟩
  by_cases hc : c = 0#64
  · subst hc; simp only [beq_self_eq_true, ↓reduceIte]; exact Entails.refl _
  · have hcf : (c == 0#64) = false := beq_false_of_ne hc
    simp only [hc, hcf, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepConj_mono_right
    have h1 := ProofLib.pointsToBytes_entails_memRegion p bs
    have hadd : bs.length + (c.toNat - bs.length) = c.toNat := Nat.add_sub_of_le hle
    have h2 : memRegion p bs.length ∗ memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length) =
        memRegion p c.toNat := by
      rw [← ProofLib.memRegion_split' (b := p) (n := bs.length) (k := c.toNat - bs.length)
        (b' := p + BitVec.ofNat 64 bs.length) hadd.symm rfl (by omega)]
    rw [← h2]
    exact sepConj_mono_left h1

theorem v10_pointsTo64_split_1_4_2_1 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗
      ((a + 1#64) ↦₃₂ w.extractLsb' 8 32) ∗
      ((a + 5#64) ↦₁₆ w.extractLsb' 40 16) ∗
      ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hb1 : (w.extractLsb' 8 32).extractLsb' 0 8 = w.extractLsb' 8 8 := by bv_kernel
  have hb2 : (w.extractLsb' 8 32).extractLsb' 8 8 = w.extractLsb' 16 8 := by bv_kernel
  have hb3 : (w.extractLsb' 8 32).extractLsb' 16 8 = w.extractLsb' 24 8 := by bv_kernel
  have hb4 : (w.extractLsb' 8 32).extractLsb' 24 8 = w.extractLsb' 32 8 := by bv_kernel
  have hb5 : (w.extractLsb' 40 16).extractLsb' 0 8 = w.extractLsb' 40 8 := by bv_kernel
  have hb6 : (w.extractLsb' 40 16).extractLsb' 8 8 = w.extractLsb' 48 8 := by bv_kernel
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      ProofLib.pointsTo32_eq_pointsToBytes (a + 1#64) (w.extractLsb' 8 32),
      ProofLib.pointsTo16_eq_pointsToBytes (a + 5#64) (w.extractLsb' 40 16)]
  simp only [unpack64, unpack32, unpack16,
    ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
    hb1, hb2, hb3, hb4, hb5, hb6,
    sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]

private theorem v10_ct2Sent_dealloc_5688_to_5728_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : V10Alloc b A ext)
    (s0 s1 : State) (out p1 p1_new cap_enc c1 c2 p2 l2 pbA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5688#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = p1)
    (hx21_1 : s1.readReg64 .x21 = p1_new) (hx22_1 : s1.readReg64 .x22 = cap_enc)
    (hx23_1 : s1.readReg64 .x23 = pbA + 8#64) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = c2) (hx26_1 : s1.readReg64 .x26 = l2)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5728#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x22 = cap_enc ∧ sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x26 = l2 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5708#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗ vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = p1_new ∧
      sm.readReg64 .x22 = cap_enc ∧ sm.readReg64 .x23 = pbA + 8#64 ∧ sm.readReg64 .x25 = c2 ∧
      sm.readReg64 .x26 = l2 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc1 : (c1 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hc1, ↓reduceIte, sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 5688 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_done
    · have hbeq : (c1 == 0#64) = false := Bool.eq_false_iff.mpr hc1
      dsimp only [vecCapPtrDealloc]
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
        spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
      have hdealloc := v10_sub_ok_dealloc_125316_v10a hA
      simp only [rustDeallocSpec] at hdealloc
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 5688 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        have h232 : (s0.sp - 2400#64) + 232#64 = s0.sp - 2168#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp1] at hst; rw [h232]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2168#64) ↦₆₄ p2) ∗
             (if (c2 == 0#64) = true then emp else A.live p2 c2.toNat 1 ∗ memRegion p2 c2.toNat) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx22_2, hx23_2, hx25_2, hx26_2, hx27_2, htr2⟩
    by_cases hc2 : (c2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hc2, ↓reduceIte, sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 5708 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_done
    · have hbeq : (c2 == 0#64) = false := Bool.eq_false_iff.mpr hc2
      dsimp only [vecCapPtrDealloc]
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
        spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
      have hdealloc := v10_sub_ok_dealloc_125316_v10a hA
      simp only [rustDeallocSpec] at hdealloc
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 5708 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        have h232 : (s0.sp - 2400#64) + 232#64 = s0.sp - 2168#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp2] at hst; rw [h232]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s2.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2168#64) ↦₆₄ p2) ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done

theorem Ext4K.v10_ct2Sent_dealloc_5688_to_5728
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out p1 p1_new cap_enc c1 c2 p2 l2 pbA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5688#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = p1)
    (hx21_1 : s1.readReg64 .x21 = p1_new) (hx22_1 : s1.readReg64 .x22 = cap_enc)
    (hx23_1 : s1.readReg64 .x23 = pbA + 8#64) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = c2) (hx26_1 : s1.readReg64 .x26 = l2)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5728#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x22 = cap_enc ∧ sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x26 = l2 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) :=
  v10_ct2Sent_dealloc_5688_to_5728_v10a (.of_4k hA) s0 s1 out p1 p1_new
    cap_enc c1 c2 p2 l2 pbA Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1
    hx24_1 hx25_1 hx26_1 hx27_1 htr1

theorem v10_ct2Sent_dealloc_5688_to_5728
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out p1 p1_new cap_enc c1 c2 p2 l2 pbA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5688#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = p1)
    (hx21_1 : s1.readReg64 .x21 = p1_new) (hx22_1 : s1.readReg64 .x22 = cap_enc)
    (hx23_1 : s1.readReg64 .x23 = pbA + 8#64) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = c2) (hx26_1 : s1.readReg64 .x26 = l2)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5728#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗ A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x22 = cap_enc ∧ sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x26 = l2 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) :=
  v10_ct2Sent_dealloc_5688_to_5728_v10a (.of_allocContracts hA) s0 s1 out p1 p1_new
    cap_enc c1 c2 p2 l2 pbA Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1
    hx24_1 hx25_1 hx26_1 hx27_1 htr1

/-! ## 3. Cloning `Authenticator` Buffers (`+1720 -> +5540` and `+5540 -> +5688`) -/

theorem v10_live_bytes_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64)
    (bs : List (BitVec 8)) (hc : c ≠ 0#64) (hle : bs.length ≤ c.toNat) :
    A.live p c.toNat 1 ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length) ⊢
      vecCapPtrDealloc A c p := by
  unfold vecCapPtrDealloc
  have hcf : (c == 0#64) = false := beq_false_of_ne hc
  simp only [hcf, Bool.false_eq_true, ↓reduceIte]
  apply sepConj_mono_right
  have h1 := ProofLib.pointsToBytes_entails_memRegion p bs
  have hadd : bs.length + (c.toNat - bs.length) = c.toNat := Nat.add_sub_of_le hle
  have h2 : memRegion p bs.length ∗ memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length) =
      memRegion p c.toNat := by
    rw [← ProofLib.memRegion_split' (b := p) (n := bs.length) (k := c.toNat - bs.length)
      (b' := p + BitVec.ofNat 64 bs.length) hadd.symm rfl (by omega)]
  rw [← h2]
  exact sepConj_mono_left h1

theorem v10_ite_nil_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64) :
    (if c = 0#64 then emp
     else A.live p c.toNat 1 ∗ (p ↦ₛ ([] : List (BitVec 8))) ∗
       memRegion (p + 0#64) (c.toNat - 0)) ⊢
      vecCapPtrDealloc A c p := by
  unfold vecCapPtrDealloc
  by_cases hc : c = 0#64
  · subst hc; simp only [beq_self_eq_true, ↓reduceIte]; exact Entails.refl _
  · have hcf : (c == 0#64) = false := beq_false_of_ne hc
    simp only [hc, hcf, Bool.false_eq_true, ↓reduceIte,
      ProofLib.pointsToBytes_nil, emp_sepConj, BitVec.add_zero, Nat.sub_zero]
    exact Entails.refl _

/-- Shared OOM cold path at `+11572` (`mov w0, #1; mov x1, x28; bl handle_error`)
with `Entails`-form panic postcondition (`fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf`). -/
theorem v10_oom_11572_entails
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (target_pc : BitVec 64) (P : SepProp)
    (Q : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11572#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s P Q
      (fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf) := by
  have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error")))
    (by rw [hfn, stubOff_handle_error])
  states_from_pb_fetches_range b (Rust.withPanics ext) 11572 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpanic hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error")))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
  unfold statesFromPbOnPanic
  exact Entails.pure_right
    (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *]))
    (entails_anyHeap _)

theorem v10_sepWP_exists_post {α : Type} {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {Q : α → State → SepProp → Prop} (a : α)
    (h : SepWP prog target s P (Q a)) :
    SepWP prog target s P (fun sm Pm => ∃ x : α, Q x sm Pm) :=
  SepWP.mono h fun _ _ _ _ hq => ⟨a, hq⟩

private theorem v10_ct2Sent_clone_rootKey_1720_to_5540_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : V10Alloc b A ext)
    (s0 s1 : State) (out p1 cap_enc c1 c2 l2 pbA : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1720#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = p1)
    (hx22_1 : s1.readReg64 .x22 = cap_enc) (hx23_1 : s1.readReg64 .x23 = pbA + 8#64)
    (hx24_1 : s1.readReg64 .x24 = c1) (hx25_1 : s1.readReg64 .x25 = c2)
    (hx26_1 : s1.readReg64 .x26 = l2) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = BitVec.ofNat 64 rootKey.length)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5540#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ vecU8Payload A c1 p1 rootKey ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        ∃ p1_new : BitVec 64,
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecCapPtrDealloc A c1 p1 ∗ A.pool ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = p1 ∧
          sm.readReg64 .x21 = p1_new ∧ sm.readReg64 .x22 = cap_enc ∧
          sm.readReg64 .x23 = pbA + 8#64 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = c2 ∧
          sm.readReg64 .x26 = l2 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hpure :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecU8Payload A c1 p1 rootKey ∗ A.pool ∗ Rest =
      ⌜rootKey.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0#64⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (if c1 = 0#64 then emp
        else A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
          memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length)) ∗
       A.pool ∗ Rest) := by
    unfold vecU8Payload; ac_rfl
  rw [hpure]
  refine SepWPp.pure_left fun ⟨hr_le, hr_cap, _⟩ => ?_
  have hr_cases : rootKey = [] ∨ 0 < rootKey.length := by cases rootKey <;> simp
  rcases hr_cases with rfl | hr_pos
  · simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx28_1 ⊢
    refine v10_sepWPp_seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5536#64)
      (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ vecCapPtrDealloc A c1 p1 ∗ A.pool ∗ Rest)
      (Q_regs := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = p1 ∧
        sm.readReg64 .x22 = cap_enc ∧ sm.readReg64 .x23 = pbA + 8#64 ∧ sm.readReg64 .x24 = c1 ∧
        sm.readReg64 .x25 = c2 ∧ sm.readReg64 .x26 = l2 ∧ sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 1720 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · exact sepConj_mono_right (sepConj_mono_left (v10_ite_nil_entails_vecCapPtrDealloc A c1 p1))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, htr2⟩
      apply SepWPp.of_sepWP_ret
      refine v10_sepWP_exists_post 1#64 ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 5536 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hv0 := vecU8Payload_zero A
        refine Entails.trans
          (Entails.of_eq (show _ =
            emp ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ vecCapPtrDealloc A c1 p1 ∗
              A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hv0) (Entails.of_eq (by ac_rfl))
      · wp_done
  · have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hc1_ne : c1 ≠ 0#64 := cap_ne_zero_of_pos hr_pos hr_le
    have hr_lt63 : rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : rootKey.length < 2 ^ 64 := by omega
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false := ofNat_beq_zero_false hr_pos hr_lt64
    have hr_toNat : (BitVec.ofNat 64 rootKey.length).toNat = rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hlay : LayoutOk rootKey.length 1 := ⟨hr_pos, hpow1, by omega⟩
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hshim := hA.shim_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    have halloc := hA.alloc_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc"))
    have hmc := hA.session_memcpy_region_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy"))
    have hoom_step := @v10_oom_11572_entails b ext s0
    simp only [hc1_ne, ↓reduceIte, sepConj_assoc]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    states_from_pb_fetches_range b (Rust.withPanics ext) 1720 44
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
      at hshim halloc hmc hoom_step hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 1740#64)
    wp_steps; wp_apply; wp_steps
    nth_rw 1 [← hsp1]; nth_rw 1 [← h_1]
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte]
      rw [v10_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      have htr_sf1 : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htrace]; simp only [wp_norm, arm64_norm, *]
      refine v10_sepWPp_seq_clean
        (mid := entry + 11572#64)
        (P_mid := A.pool ∗ stackAt sf.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056 ∗
          A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
          memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length) ∗ Rest)
        (Q_regs := fun sm => sm.trace = s0.trace ++ [allocFailedEvent]) ?_ ?_
      · wp_steps; wp_done
      · intro s3 hpc3 hrun3 htr3; exact hoom_step s3 _ _ _ hpc3 hrun3 htr3
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
      rw [v10_pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      have hsp_sf1 : sf_1.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      refine v10_sepWP_exists_post (sf_1.readReg64 (Reg.gpr 0#5)) ?_
      wp_steps
      have hsp_eq_sf : sf_1.sp = sf.sp := by simp only [wp_norm, arm64_norm, *]
      wp_simp_pre [← hsp_eq_sf]; wp_apply; wp_simp_pre [hsp_eq_sf]; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp_sf1] at hst; rw [hsp_sf] at hst
        have hv_new := vecU8Payload_pos A (sf_1.readReg64 (Reg.gpr 0#5)) rootKey hr_pos hr_lt63 hoom
        have hv_old := v10_live_bytes_entails_vecCapPtrDealloc A c1 p1 rootKey hc1_ne hr_le
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt sf.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (A.live (sf_1.readReg64 (Reg.gpr 0#5)) rootKey.length 1 ∗ (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ rootKey)) ∗
            (A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
              memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length)) ∗
            (A.pool ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono hst (sepConj_mono hv_new (sepConj_mono_left hv_old))) ?_
        exact Entails.of_eq (by ac_rfl)
      · wp_done

private theorem v10_ct2Sent_clone_macKey_5540_to_5688_v10a
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : V10Alloc b A ext)
    (s0 s1 : State) (out p1 p1_new cap_enc c1 c2 p2 v184 pbA : BitVec 64)
    (macKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5540#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = p1)
    (hx21_1 : s1.readReg64 .x21 = p1_new) (hx22_1 : s1.readReg64 .x22 = cap_enc)
    (hx23_1 : s1.readReg64 .x23 = pbA + 8#64) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = c2)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 macKey.length)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5688#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗ vecU8Payload A c2 p2 macKey ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        ∃ p2_new : BitVec 64,
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
            vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = p1 ∧
          sm.readReg64 .x21 = p1_new ∧ sm.readReg64 .x22 = cap_enc ∧
          sm.readReg64 .x23 = pbA + 8#64 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = c2 ∧
          sm.readReg64 .x26 = BitVec.ofNat 64 macKey.length ∧ sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
  have h232 : (s0.sp - 2400#64) + 232#64 = s0.sp - 2168#64 := by bv_omega
  have hpure :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗ vecU8Payload A c2 p2 macKey ∗ A.pool ∗ Rest =
      ⌜macKey.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0#64⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
       (if c2 = 0#64 then emp
        else A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
          memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length)) ∗
       A.pool ∗ Rest) := by
    unfold vecU8Payload; ac_rfl
  rw [hpure]
  refine SepWPp.pure_left fun ⟨hm_le, hm_cap, _⟩ => ?_
  have hm_cases : macKey = [] ∨ 0 < macKey.length := by cases macKey <;> simp
  rcases hm_cases with rfl | hm_pos
  · simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx26_1 ⊢
    apply SepWPp.of_sepWP_ret
    refine v10_sepWP_exists_post 1#64 ?_
    states_from_pb_fetches_range b (Rust.withPanics ext) 5540 148
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [h184, h232]
      have hv0 := vecU8Payload_zero A
      have hite := v10_ite_nil_entails_vecCapPtrDealloc A c2 p2
      refine Entails.trans
        (Entails.of_eq (show _ =
          emp ∗
          (if c2 = 0#64 then emp
           else A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ ([] : List (BitVec 8))) ∗
             memRegion (p2 + 0#64) (c2.toNat - 0)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2216#64) ↦₆₄ 1#64) ∗
           ((s0.sp - 2168#64) ↦₆₄ p2) ∗ A.pool ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hv0 (sepConj_mono_left hite)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hc2_ne : c2 ≠ 0#64 := cap_ne_zero_of_pos hm_pos hm_le
    have hm_lt63 : macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : macKey.length < 2 ^ 64 := by omega
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false := ofNat_beq_zero_false hm_pos hm_lt64
    have hm_toNat : (BitVec.ofNat 64 macKey.length).toNat = macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hlay : LayoutOk macKey.length 1 := ⟨hm_pos, hpow1, by omega⟩
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hshim := hA.shim_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    have halloc := hA.alloc_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc"))
    have hmc := hA.session_memcpy_region_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy"))
    have hoom_step := @v10_oom_11572_entails b ext s0
    simp only [hc2_ne, ↓reduceIte, sepConj_assoc]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    states_from_pb_fetches_range b (Rust.withPanics ext) 5540 48
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat]
      at hshim halloc hmc hoom_step hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 5564#64)
    wp_steps; wp_apply; wp_steps
    nth_rw 1 [← hsp1]; nth_rw 1 [← h_1]
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte]
      rw [v10_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      have htr_sf1 : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htrace]; simp only [wp_norm, arm64_norm, *]
      refine v10_sepWPp_seq_clean
        (mid := entry + 11572#64)
        (P_mid := A.pool ∗ stackAt sf.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056 ∗
          ((s0.sp - 2216#64) ↦₆₄ v184) ∗ ((s0.sp - 2168#64) ↦₆₄ p2) ∗
          A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
          memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length) ∗ Rest)
        (Q_regs := fun sm => sm.trace = s0.trace ++ [allocFailedEvent]) ?_ ?_
      · wp_steps; wp_done
      · intro s3 hpc3 hrun3 htr3; exact hoom_step s3 _ _ _ hpc3 hrun3 htr3
    · simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
      rw [v10_pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      have hsp_sf1 : sf_1.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      refine v10_sepWP_exists_post (sf_1.readReg64 (Reg.gpr 0#5)) ?_
      wp_steps
      have hsp_eq_sf : sf_1.sp = sf.sp := by simp only [wp_norm, arm64_norm, *]
      wp_simp_pre [← hsp_eq_sf]; wp_apply; wp_simp_pre [hsp_eq_sf]; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h184, h232]
        have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst; nth_rw 1 [← hsp_sf1] at hst; rw [hsp_sf] at hst
        have hv_new := vecU8Payload_pos A (sf_1.readReg64 (Reg.gpr 0#5)) macKey hm_pos hm_lt63 hoom
        have hv_old := v10_live_bytes_entails_vecCapPtrDealloc A c2 p2 macKey hc2_ne hm_le
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt sf.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (A.live (sf_1.readReg64 (Reg.gpr 0#5)) macKey.length 1 ∗ (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ macKey)) ∗
            (A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
              memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length)) ∗
            (((s0.sp - 2216#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
             ((s0.sp - 2168#64) ↦₆₄ p2) ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono hst (sepConj_mono hv_new (sepConj_mono_left hv_old))) ?_
        exact Entails.of_eq (by ac_rfl)
      · wp_done

theorem Ext4K.v10_ct2Sent_clone_rootKey_1720_to_5540
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s1 : State) (out p1 cap_enc c1 c2 l2 pbA : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1720#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = p1)
    (hx22_1 : s1.readReg64 .x22 = cap_enc) (hx23_1 : s1.readReg64 .x23 = pbA + 8#64)
    (hx24_1 : s1.readReg64 .x24 = c1) (hx25_1 : s1.readReg64 .x25 = c2)
    (hx26_1 : s1.readReg64 .x26 = l2) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = BitVec.ofNat 64 rootKey.length)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5540#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ vecU8Payload A c1 p1 rootKey ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        ∃ p1_new : BitVec 64,
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecCapPtrDealloc A c1 p1 ∗ A.pool ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = p1 ∧
          sm.readReg64 .x21 = p1_new ∧ sm.readReg64 .x22 = cap_enc ∧
          sm.readReg64 .x23 = pbA + 8#64 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = c2 ∧
          sm.readReg64 .x26 = l2 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) :=
  v10_ct2Sent_clone_rootKey_1720_to_5540_v10a (.of_4k hA) s0 s1 out p1
    cap_enc c1 c2 l2 pbA rootKey Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx22_1 hx23_1
    hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1

theorem Ext4K.v10_ct2Sent_clone_macKey_5540_to_5688
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s1 : State) (out p1 p1_new cap_enc c1 c2 p2 v184 pbA : BitVec 64)
    (macKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5540#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = p1)
    (hx21_1 : s1.readReg64 .x21 = p1_new) (hx22_1 : s1.readReg64 .x22 = cap_enc)
    (hx23_1 : s1.readReg64 .x23 = pbA + 8#64) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = c2) (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 macKey.length)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5688#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗ vecU8Payload A c2 p2 macKey ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        ∃ p2_new : BitVec 64,
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
            vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = p1 ∧
          sm.readReg64 .x21 = p1_new ∧ sm.readReg64 .x22 = cap_enc ∧
          sm.readReg64 .x23 = pbA + 8#64 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = c2 ∧
          sm.readReg64 .x26 = BitVec.ofNat 64 macKey.length ∧ sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) :=
  v10_ct2Sent_clone_macKey_5540_to_5688_v10a (.of_4k hA) s0 s1 out p1
    p1_new cap_enc c1 c2 p2 v184 pbA macKey Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1
    hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 htr1

theorem v10_ct2Sent_clone_rootKey_1720_to_5540
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s1 : State) (out p1 cap_enc c1 c2 l2 pbA : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1720#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = p1)
    (hx22_1 : s1.readReg64 .x22 = cap_enc) (hx23_1 : s1.readReg64 .x23 = pbA + 8#64)
    (hx24_1 : s1.readReg64 .x24 = c1) (hx25_1 : s1.readReg64 .x25 = c2)
    (hx26_1 : s1.readReg64 .x26 = l2) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = BitVec.ofNat 64 rootKey.length)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5540#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ vecU8Payload A c1 p1 rootKey ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        ∃ p1_new : BitVec 64,
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecCapPtrDealloc A c1 p1 ∗ A.pool ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = p1 ∧
          sm.readReg64 .x21 = p1_new ∧ sm.readReg64 .x22 = cap_enc ∧
          sm.readReg64 .x23 = pbA + 8#64 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = c2 ∧
          sm.readReg64 .x26 = l2 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) :=
  v10_ct2Sent_clone_rootKey_1720_to_5540_v10a (.of_allocContracts hA) s0 s1 out p1
    cap_enc c1 c2 l2 pbA rootKey Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx22_1 hx23_1
    hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1

theorem v10_ct2Sent_clone_macKey_5540_to_5688
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s1 : State) (out p1 p1_new cap_enc c1 c2 p2 v184 pbA : BitVec 64)
    (macKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5540#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = p1)
    (hx21_1 : s1.readReg64 .x21 = p1_new) (hx22_1 : s1.readReg64 .x22 = cap_enc)
    (hx23_1 : s1.readReg64 .x23 = pbA + 8#64) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = c2) (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 macKey.length)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5688#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗ vecU8Payload A c2 p2 macKey ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        ∃ p2_new : BitVec 64,
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
            vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = p1 ∧
          sm.readReg64 .x21 = p1_new ∧ sm.readReg64 .x22 = cap_enc ∧
          sm.readReg64 .x23 = pbA + 8#64 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = c2 ∧
          sm.readReg64 .x26 = BitVec.ofNat 64 macKey.length ∧ sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) :=
  v10_ct2Sent_clone_macKey_5540_to_5688_v10a (.of_allocContracts hA) s0 s1 out p1
    p1_new cap_enc c1 c2 p2 v184 pbA macKey Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1
    hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 htr1

end CryptoVerification.SpqrV1.States.FromPb

