/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10c
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 10 (`Ct2Sampled`, `+1632`) — Top-Level Composition

Composes all Variant 10 (`InnerState.ct2Sampled`, jump-table offset `+1632`) error, cloning,
`<PolyEncoder>::from_pb`, and epilogue sub-steps into `states_from_pb_ct2Sampled_1632`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

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

/-! ## 1. Early Error Paths (`s.uc = none` and `s.uc = some { auth := none, .. }`) -/

theorem v10_ct2Sent_expose_pre_uc_none_2304 (A : RustAlloc) (fsp out pbA b : BitVec 64)
    (s0 : State) (sendingCt2 : Option PolynomialEncoderPB) :
    stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗ protoChunkedCt2SampledAt A (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
       memRegion (pbA + 120#64) 104) ∗ statesFromPbJumpTableAt b ∗ A.pool ⊢
    ∃∗ cap_enc : BitVec 64, ⌜v10_optEncoderCapProp cap_enc (sendingCt2.map pbToProtoPolyEncoder)⌝ ∗
      (stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ cap_enc) ∗
       v10_optProtoPolyEncoderTail A (pbA + 8#64) cap_enc (sendingCt2.map pbToProtoPolyEncoder) ∗
       ((pbA + 64#64) ↦₆₄ none2Cap) ∗ memRegion (pbA + 72#64) 48 ∗ memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTableAt b ∗ A.pool) := by
  rw [v10_protoChunkedCt2SampledAt_uc_none]
  refine Entails.trans (Entails.of_eq (show _ =
    optProtoPolynomialEncoderAt A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
    (stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 64#64) ↦₆₄ none2Cap) ∗
     memRegion (pbA + 72#64) 48 ∗ memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (v10_optProtoPolyEncoder_expose_cap A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim fun cap_enc => Entails.sepExists_right cap_enc (Entails.of_eq (by ac_rfl))

theorem v10_ct2Sent_err_1632_uc_none_2304
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s1 : State) (out pbA : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
         memRegion (pbA + 120#64) 104) ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (v10_ct2Sent_expose_pre_uc_none_2304 A (s0.sp - 2400#64) out pbA b s0 sendingCt2) ?_
  apply ProofLib.SepWP.exists_left; intro cap_enc; apply ProofLib.SepWP.pure_elim; intro hcap
  refine EncoderFromPb.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2064#64)
    (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      optProtoPolynomialEncoderAt A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗ A.pool ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 64#64) 160 ∗ statesFromPbJumpTableAt b))
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = pbA + 8#64 ∧ sm.readReg64 .x22 = cap_enc ∧ TraceCalleeSaved sm s0) ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 1632 20
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat, none2Cap] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps; refine EncoderFromPb.align_pre ?_ ?_
    · have hunexp := v10_optProtoPolyEncoder_unexpose_cap A (pbA + 8#64) cap_enc (sendingCt2.map pbToProtoPolyEncoder)
      have hpb64 := v10_pb_64_none_entails_160 pbA; unfold none2Cap at hpb64
      refine Entails.trans (Entails.of_eq (show _ =
        (((pbA + 8#64) ↦₆₄ cap_enc) ∗ v10_optProtoPolyEncoderTail A (pbA + 8#64) cap_enc (sendingCt2.map pbToProtoPolyEncoder)) ∗
        (((pbA + 64#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (pbA + 72#64) 48 ∗ memRegion (pbA + 120#64) 104) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         (pbA ↦₆₄ 0x800000000000000a#64) ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hunexp (sepConj_mono_left hpb64)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx22_2, htr2⟩
    have hx22_prop : match sendingCt2.map pbToProtoPolyEncoder with
        | none => s2.readReg64 .x22 = noneCap | some _ => (s2.readReg64 .x22).toNat < 2 ^ 63 := by rw [hx22_2]; exact hcap
    have h2064 := v10_states_from_pb_err_2064 (F := F) hA s0 s2 out (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder)
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 64#64) 160 ∗ statesFromPbJumpTableAt b)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx22_prop htr2
    refine SepWP.mono h2064 ?_; intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩; refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
    have hpb := v10_pb_tag_56_160_entails_224 pbA 0x800000000000000a#64
    refine Entails.trans (Entails.of_eq (show _ =
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 8#64) 56 ∗ memRegion (pbA + 64#64) 160) ∗
      (resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
       statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))

theorem v10_ct2Sent_expose_pre_auth_none_2304 (A : RustAlloc) (fsp out pbA epoch b : BitVec 64)
    (s0 : State) (sendingCt2 : Option PolynomialEncoderPB) :
    stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       protoChunkedCt2SampledAt A (pbA + 8#64) { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
       memRegion (pbA + 120#64) 104) ∗ statesFromPbJumpTableAt b ∗ A.pool ⊢
    ∃∗ cap_enc : BitVec 64, ⌜v10_optEncoderCapProp cap_enc (sendingCt2.map pbToProtoPolyEncoder)⌝ ∗
      (stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ cap_enc) ∗
       v10_optProtoPolyEncoderTail A (pbA + 8#64) cap_enc (sendingCt2.map pbToProtoPolyEncoder) ∗
       ((pbA + 64#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 72#64) 40 ∗
       ((pbA + 112#64) ↦₆₄ epoch) ∗ memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTableAt b ∗ A.pool) := by
  rw [v10_protoChunkedCt2SampledAt_auth_none]
  refine Entails.trans (Entails.of_eq (show _ =
    optProtoPolynomialEncoderAt A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
    (stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 64#64) ↦₆₄ noneCap) ∗
     memRegion (pbA + 72#64) 40 ∗ ((pbA + 112#64) ↦₆₄ epoch) ∗ memRegion (pbA + 120#64) 104 ∗
     statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (v10_optProtoPolyEncoder_expose_cap A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim fun cap_enc => Entails.sepExists_right cap_enc (Entails.of_eq (by ac_rfl))

theorem v10_ct2Sent_err_1632_auth_none_2304
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s1 : State) (out pbA epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A (pbA + 8#64) { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
         memRegion (pbA + 120#64) 104) ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (v10_ct2Sent_expose_pre_auth_none_2304 A (s0.sp - 2400#64) out pbA epoch b s0 sendingCt2) ?_
  apply ProofLib.SepWP.exists_left; intro cap_enc; apply ProofLib.SepWP.pure_elim; intro hcap
  refine EncoderFromPb.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2064#64)
    (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      optProtoPolynomialEncoderAt A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗ A.pool ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 64#64) 160 ∗ statesFromPbJumpTableAt b))
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = pbA + 8#64 ∧ sm.readReg64 .x22 = cap_enc ∧ TraceCalleeSaved sm s0) ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 1632 28
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat, noneCap] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps; refine EncoderFromPb.align_pre ?_ ?_
    · have hunexp := v10_optProtoPolyEncoder_unexpose_cap A (pbA + 8#64) cap_enc (sendingCt2.map pbToProtoPolyEncoder)
      have hpb64 := v10_pb_64_auth_none_entails_160 pbA epoch; unfold noneCap at hpb64
      refine Entails.trans (Entails.of_eq (show _ =
        (((pbA + 8#64) ↦₆₄ cap_enc) ∗ v10_optProtoPolyEncoderTail A (pbA + 8#64) cap_enc (sendingCt2.map pbToProtoPolyEncoder)) ∗
        (((pbA + 64#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (pbA + 72#64) 40 ∗ ((pbA + 112#64) ↦₆₄ epoch) ∗ memRegion (pbA + 120#64) 104) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         (pbA ↦₆₄ 0x800000000000000a#64) ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hunexp (sepConj_mono_left hpb64)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx22_2, htr2⟩
    have hx22_prop : match sendingCt2.map pbToProtoPolyEncoder with
        | none => s2.readReg64 .x22 = noneCap | some _ => (s2.readReg64 .x22).toNat < 2 ^ 63 := by rw [hx22_2]; exact hcap
    have h2064 := v10_states_from_pb_err_2064 (F := F) hA s0 s2 out (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder)
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 64#64) 160 ∗ statesFromPbJumpTableAt b)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx22_prop htr2
    refine SepWP.mono h2064 ?_; intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩; refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
    have hpb := v10_pb_tag_56_160_entails_224 pbA 0x800000000000000a#64
    refine Entails.trans (Entails.of_eq (show _ =
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 8#64) 56 ∗ memRegion (pbA + 64#64) 160) ∗
      (resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
       statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))

/-! ## 2. `ProtoPolynomialEncoder` (`56`B) Relocation Helpers (`pbA + 8 -> fsp + 1392`) -/

theorem v10_pointsTo64_eq_loByte_hiBytes7 (a w : BitVec 64) :
    (a ↦₆₄ w) = (a ↦₈ loByte w) ∗ ((a + 1#64) ↦ₛ hiBytes7 w) := by
  rw [pointsTo64_eq_pointsToBytes a w]; have hcons : unpack64 w = loByte w :: hiBytes7 w := rfl
  rw [hcons, ProofLib.pointsToBytes_cons]

theorem v10_seven_words_entails_memRegion_56 (a w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗ ((a + 24#64) ↦₆₄ w24) ∗
      ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗ ((a + 48#64) ↦₆₄ w48) ⊢ memRegion a 56 := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (ProofLib.pointsTo64_entails_memRegion (a + 48#64) w48))))))) ?_
  exact protoPolyEncoderHeaders_entails_memRegion_56 a w0 w8 w16 w24 w32 w40

theorem v10_protoPolynomialEncoderAt_relocate (A : RustAlloc) (pbA d : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    protoPolynomialEncoderAt A (pbA + 8#64) pb ⊢
      ∃∗ cap_pts : BitVec 64, ∃∗ ptr_pts : BitVec 64, ∃∗ cap_polys : BitVec 64,
      ∃∗ ptr_polys : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ P_enc_heap : SepProp,
        ⌜cap_pts.toNat < 2 ^ 63 ∧
          ((d ↦₆₄ cap_pts) ∗ ((d + 8#64) ↦₆₄ ptr_pts) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           ((d + 24#64) ↦₆₄ cap_polys) ∗ ((d + 32#64) ↦₆₄ ptr_polys) ∗ ((d + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
           ((d + 48#64) ↦₆₄ w56) ∗ P_enc_heap ⊢ protoPolynomialEncoderAt A d pb)⌝ ∗
        ((pbA + 8#64) ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ ptr_pts) ∗ ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
        ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗ P_enc_heap := by
  conv =>
    lhs
    unfold protoPolynomialEncoderAt vecVecU8At vecOf Poly.vecHeaderBytes
      protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize vecAt vecHeader
  rw [ProofLib.memRegion_four ((pbA + 8#64) + 52#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro hi32; apply Entails.sepExists_elim; intro cap_polys
  apply Entails.sepExists_elim; intro ptr_polys; apply Entails.sepExists_elim; intro cap_pts; apply Entails.sepExists_elim; intro ptr_pts
  have ha16 : (pbA + 8#64) + 8#64 = pbA + 16#64 := by bv_omega
  have ha24 : (pbA + 8#64) + 16#64 = pbA + 24#64 := by bv_omega
  have ha32 : (pbA + 8#64) + 24#64 = pbA + 32#64 := by bv_omega
  have ha40 : (pbA + 32#64) + 8#64 = pbA + 40#64 := by bv_omega
  have ha48 : (pbA + 32#64) + 16#64 = pbA + 48#64 := by bv_omega
  have ha56 : (pbA + 8#64) + 48#64 = pbA + 56#64 := by bv_omega
  have ha60 : (pbA + 8#64) + 52#64 = (pbA + 56#64) + 4#64 := by bv_omega
  rw [ha16, ha24, ha32, ha40, ha48, ha56, ha60, v10_pointsTo32_pair_eq_pointsTo64 (pbA + 56#64) pb.idx hi32]
  have hcap_extract :
      vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_pts ptr_pts pb.pts ⊢
        ⌜cap_pts.toNat < 2 ^ 63⌝ ∗ vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_pts ptr_pts pb.pts := by
    unfold vecBuf; apply Entails.pure_left; rintro ⟨hle, hlt24, hne⟩
    exact Entails.pure_right (by omega) (Entails.pure_right ⟨hle, hlt24, hne⟩ (Entails.refl _))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hcap_extract)))) ?_
  simp only [sepConj_assoc]
  rw [show ((pbA + 8#64) ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
        ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ ⌜cap_pts.toNat < 2 ^ 63⌝ ∗
        vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_pts ptr_pts pb.pts ∗
        ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
        ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_polys ptr_polys pb.polys ∗
        ((pbA + 56#64) ↦₆₄ (hi32 ++ pb.idx)) =
      ⌜cap_pts.toNat < 2 ^ 63⌝ ∗
      (((pbA + 8#64) ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
       ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ ((pbA + 32#64) ↦₆₄ cap_polys) ∗
       ((pbA + 40#64) ↦₆₄ ptr_polys) ∗ ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       ((pbA + 56#64) ↦₆₄ (hi32 ++ pb.idx)) ∗
       (vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_pts ptr_pts pb.pts ∗
        vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_polys ptr_polys pb.polys)) by ac_rfl]
  apply Entails.pure_left; intro hcap_lt
  refine Entails.sepExists_right cap_pts (Entails.sepExists_right ptr_pts
    (Entails.sepExists_right cap_polys (Entails.sepExists_right ptr_polys
      (Entails.sepExists_right (hi32 ++ pb.idx) (Entails.sepExists_right
        (vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_pts ptr_pts pb.pts ∗
         vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_polys ptr_polys pb.polys) ?_)))))
  refine Entails.pure_right ⟨hcap_lt, ?_⟩ (Entails.of_eq (by ac_rfl))
  unfold protoPolynomialEncoderAt vecVecU8At vecOf Poly.vecHeaderBytes
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize vecAt vecHeader
  rw [ProofLib.memRegion_four (d + 52#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_right hi32 (Entails.sepExists_right cap_polys
    (Entails.sepExists_right ptr_polys (Entails.sepExists_right cap_pts (Entails.sepExists_right ptr_pts ?_))))
  have hd32 : (d + 24#64) + 8#64 = d + 32#64 := by bv_omega
  have hd40 : (d + 24#64) + 16#64 = d + 40#64 := by bv_omega
  have hd52 : d + 52#64 = (d + 48#64) + 4#64 := by bv_omega
  rw [hd32, hd40, hd52, ← v10_pointsTo32_pair_eq_pointsTo64 (d + 48#64) pb.idx hi32]; exact Entails.of_eq (by ac_rfl)

/-! ## 3. Shared Prefix `+1632 -> +5728` for `s.uc = some { auth := some auth, epoch := ep }` -/

theorem v10_sepWPp_bind {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {Q_mid Q Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Q_mid Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q_mid sm Pm → SepWPp prog ret sm Pm Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL; obtain ⟨sm, hsteps1, hout1⟩ := h1 R hm hL
  rcases hout1 with ⟨hpcm, hrunm, Pm, hmm, hqm⟩ | hpan
  · obtain ⟨sf, hsteps2, hout2⟩ := h2 sm Pm hpcm hrunm hqm R hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr hpan⟩

theorem v10_authPBPinnedAt_64_eq_full (A : RustAlloc) (ga : AuthenticatorPBGhost)
    (pbA : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (pbA + 64#64) auth =
      ((pbA + 64#64) ↦₆₄ ga.rootKey.cap) ∗ ((pbA + 72#64) ↦₆₄ ga.rootKey.ptr) ∗
      ((pbA + 80#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((pbA + 88#64) ↦₆₄ ga.macKey.cap) ∗ ((pbA + 96#64) ↦₆₄ ga.macKey.ptr) ∗
      ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
      vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey := by
  unfold authenticatorPBPinnedAt vecU8At vecHeader vecU8Payload
  have h72 : (pbA + 64#64) + 8#64 = pbA + 72#64 := by bv_omega
  have h80 : (pbA + 64#64) + 16#64 = pbA + 80#64 := by bv_omega
  have h88 : (pbA + 64#64) + 24#64 = pbA + 88#64 := by bv_omega
  have h96 : (pbA + 88#64) + 8#64 = pbA + 96#64 := by bv_omega
  have h104 : (pbA + 88#64) + 16#64 = pbA + 104#64 := by bv_omega
  rw [h72, h80, h88, h96, h104]; ac_rfl

theorem v10_vecU8Payload_extract_bounds (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Payload A cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63 ∧ (BitVec.ofNat 64 bs.length).toNat < 2 ^ 63⌝ ∗ vecU8Payload A cap ptr bs := by
  unfold vecU8Payload; apply Entails.pure_left; rintro ⟨hle, hcap_lt, hptr⟩
  have hlen_lt63 : bs.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle hcap_lt
  have hbv_lt63 : (BitVec.ofNat 64 bs.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hlen_lt63
  exact Entails.pure_right ⟨hcap_lt, hbv_lt63⟩ (Entails.pure_right ⟨hle, hcap_lt, hptr⟩ (Entails.refl _))

theorem v10_pbA_64_to_120_entails_56 (pbA c1 p1 l1 c2 p2 l2 ep : BitVec 64) :
    ((pbA + 64#64) ↦₆₄ c1) ∗ ((pbA + 72#64) ↦₆₄ p1) ∗ ((pbA + 80#64) ↦₆₄ l1) ∗
      ((pbA + 88#64) ↦₆₄ c2) ∗ ((pbA + 96#64) ↦₆₄ p2) ∗ ((pbA + 104#64) ↦₆₄ l2) ∗
      ((pbA + 112#64) ↦₆₄ ep) ⊢ memRegion (pbA + 64#64) 56 :=
  collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Drop.pointsTo64_entails_memRegion _ _

theorem v10_ct2Sent_1632_to_5728
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s1 : State) (out pbA cap_enc ep v152 v184 v200 v232 : BitVec 64)
    (b16 : BitVec 8) (v224 : BitVec 32) (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5728#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_enc) ∗
        ((pbA + 16#64) ↦₈ b16) ∗ authenticatorPBPinnedAt A ga (pbA + 64#64) auth ∗
        ((pbA + 112#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        ∃ pa1 pa2 : BitVec 64,
          (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 ∧
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_enc) ∗
            ((pbA + 16#64) ↦₈ b16) ∗ memRegion (pbA + 64#64) 56 ∗
            (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
            (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
            vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
            vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ A.pool ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa1 ∧
          sm.readReg64 .x22 = cap_enc ∧ sm.readReg64 .x23 = pbA + 8#64 ∧
          sm.readReg64 .x26 = BitVec.ofNat 64 auth.macKey.length ∧
          sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  rw [v10_authPBPinnedAt_64_eq_full]
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
      (((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗ ((pbA + 64#64) ↦₆₄ ga.rootKey.cap) ∗
       ((pbA + 72#64) ↦₆₄ ga.rootKey.ptr) ∗ ((pbA + 80#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       ((pbA + 88#64) ↦₆₄ ga.macKey.cap) ∗ ((pbA + 96#64) ↦₆₄ ga.macKey.ptr) ∗
       ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ ((pbA + 112#64) ↦₆₄ ep) ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗
       (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
        vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ A.pool ∗ Rest)) by ac_rfl))
      (Entails.trans (sepConj_mono_left (v10_vecU8Payload_extract_bounds A ga.rootKey.cap ga.rootKey.ptr auth.rootKey))
        (Entails.of_eq (show _ =
          ⌜ga.rootKey.cap.toNat < 2 ^ 63 ∧ (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63⌝ ∗
          (((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗ ((pbA + 64#64) ↦₆₄ ga.rootKey.cap) ∗
           ((pbA + 72#64) ↦₆₄ ga.rootKey.ptr) ∗ ((pbA + 80#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
           ((pbA + 88#64) ↦₆₄ ga.macKey.cap) ∗ ((pbA + 96#64) ↦₆₄ ga.macKey.ptr) ∗
           ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ ((pbA + 112#64) ↦₆₄ ep) ∗
           (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
           (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗
           (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
            vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
            vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ A.pool ∗ Rest)) by ac_rfl)))) ?_
  refine SepWPp.pure_left fun ⟨hc1_lt, hl1_lt⟩ => ?_
  have h1632 := v10_ct2Sent_load_1632_to_1720 s0 s1 out pbA cap_enc
    ga.rootKey.cap ga.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
    ga.macKey.cap ga.macKey.ptr (BitVec.ofNat 64 auth.macKey.length) ep v152 v200 v232 b16 v224
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
     vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
     vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ A.pool ∗ Rest)
    hsp0_align hc1_lt hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine v10_sepWPp_seq_clean h1632 ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
  have hpb56 := v10_pbA_64_to_120_entails_56 pbA
    ga.rootKey.cap ga.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
    ga.macKey.cap ga.macKey.ptr (BitVec.ofNat 64 auth.macKey.length) ep
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (((pbA + 64#64) ↦₆₄ ga.rootKey.cap) ∗ ((pbA + 72#64) ↦₆₄ ga.rootKey.ptr) ∗
       ((pbA + 80#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       ((pbA + 88#64) ↦₆₄ ga.macKey.cap) ∗ ((pbA + 96#64) ↦₆₄ ga.macKey.ptr) ∗
       ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ ((pbA + 112#64) ↦₆₄ ep)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗ A.pool ∗
       (((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗
        (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
        vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ Rest)) by ac_rfl))
      (Entails.trans (sepConj_mono_left hpb56) (Entails.of_eq (show _ =
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗ A.pool ∗
          (memRegion (pbA + 64#64) 56 ∗ ((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗
           (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
           (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
           vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ Rest) by ac_rfl)))) ?_
  have h1720 := v10_ct2Sent_clone_rootKey_1720_to_5540 hA s0 s2 out
    ga.rootKey.ptr cap_enc ga.rootKey.cap ga.macKey.cap (BitVec.ofNat 64 auth.macKey.length) pbA auth.rootKey
    (memRegion (pbA + 64#64) 56 ∗ ((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗
     (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2
  refine v10_sepWPp_bind h1720 ?_
  intro s3 P3 hpc3 hrun3 ⟨pa1, hP3, hsp3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, htr3⟩
  refine SepWPp.weaken_pre (Entails.trans hP3 (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
    (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗ vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ A.pool ∗
    (vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ memRegion (pbA + 64#64) 56 ∗
     ((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗ Rest) by ac_rfl))) ?_
  have h5540 := v10_ct2Sent_clone_macKey_5540_to_5688 hA s0 s3 out
    ga.rootKey.ptr pa1 cap_enc ga.rootKey.cap ga.macKey.cap ga.macKey.ptr v184 pbA auth.macKey
    (vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ memRegion (pbA + 64#64) 56 ∗
     ((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗ Rest)
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 htr3
  refine v10_sepWPp_bind h5540 ?_
  intro s4 P4 hpc4 hrun4 ⟨pa2, hP4, hsp4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, htr4⟩
  refine SepWPp.weaken_pre (Entails.trans hP4 (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
    vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗ A.pool ∗
    (((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗ memRegion (pbA + 64#64) 56 ∗
     (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
     vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ Rest) by ac_rfl))) ?_
  have h5688 := v10_ct2Sent_dealloc_5688_to_5728 hA s0 s4 out
    ga.rootKey.ptr pa1 cap_enc ga.rootKey.cap ga.macKey.cap ga.macKey.ptr
    (BitVec.ofNat 64 auth.macKey.length) pbA
    (((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗ memRegion (pbA + 64#64) 56 ∗
     (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
     vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ Rest)
    hsp0_align hpc4 hrun4 hsp4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 htr4
  apply SepWPp.of_sepWP_ret; refine SepWP.mono h5688 ?_
  intro s5 P5 _ _ ⟨hP5, hsp5, hx19_5, hx21_5, hx22_5, hx23_5, hx26_5, hx27_5, htr5⟩
  exact ⟨pa1, pa2, hl1_lt, Entails.trans hP5 (Entails.of_eq (by ac_rfl)),
    hsp5, hx19_5, hx21_5, hx22_5, hx23_5, hx26_5, hx27_5, htr5⟩

/-! ## 4. Stack & Buffer Layout Helpers for `+1632 .. +5808` -/

theorem v10_fsp_split_1632 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 152 ∗ (∃∗ v152 : BitVec 64, (fsp + 152#64) ↦₆₄ v152) ∗
      memRegion (fsp + 160#64) 24 ∗ (∃∗ v184 : BitVec 64, (fsp + 184#64) ↦₆₄ v184) ∗
      memRegion (fsp + 192#64) 8 ∗ (∃∗ v200 : BitVec 64, (fsp + 200#64) ↦₆₄ v200) ∗
      memRegion (fsp + 208#64) 16 ∗ (∃∗ v224 : BitVec 32, (fsp + 224#64) ↦₃₂ v224) ∗
      (∃∗ v228 : BitVec 32, (fsp + 228#64) ↦₃₂ v228) ∗
      (∃∗ v232 : BitVec 64, (fsp + 232#64) ↦₆₄ v232) ∗ memRegion (fsp + 240#64) 2064 :=
  split_top <| split_step0 (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem32_entails _) <|
    split_step (mem32_entails _) <| split_step (mem64_entails _) <| Entails.refl _

theorem v10_fsp_unsplit_1632 (fsp v152 v184 v200 v232 : BitVec 64) (v224 v228 : BitVec 32) :
    memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ v152) ∗ memRegion (fsp + 160#64) 24 ∗
      ((fsp + 184#64) ↦₆₄ v184) ∗ memRegion (fsp + 192#64) 8 ∗ ((fsp + 200#64) ↦₆₄ v200) ∗
      memRegion (fsp + 208#64) 16 ∗ ((fsp + 224#64) ↦₃₂ v224) ∗ ((fsp + 228#64) ↦₃₂ v228) ∗
      ((fsp + 232#64) ↦₆₄ v232) ∗ memRegion (fsp + 240#64) 2064 ⊢ memRegion fsp 2304 :=
  collapse_top <| collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _

theorem v10_pbA_none_some_entails_224 (pbA : BitVec 64) (b16 : BitVec 8) :
    (pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗ ((pbA + 16#64) ↦₈ b16) ∗
      memRegion (pbA + 17#64) 47 ∗ memRegion (pbA + 64#64) 56 ∗ memRegion (pbA + 120#64) 104 ⊢
      memRegion pbA optProtoInnerStateSize :=
  collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo8_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <| Entails.refl _

theorem v10_pbA_some_some_entails_224 (pbA w8 w16 w24 w32 w40 w48 w56 : BitVec 64) :
    (pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
      ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₆₄ w32) ∗ ((pbA + 40#64) ↦₆₄ w40) ∗
      ((pbA + 48#64) ↦₆₄ w48) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗
      memRegion (pbA + 64#64) 56 ∗ memRegion (pbA + 120#64) 104 ⊢
      memRegion pbA optProtoInnerStateSize :=
  collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <| Entails.refl _

theorem v10_memRegion_15_entails_8_loBytes7 (a : BitVec 64) :
    memRegion a 15 ⊢
      (∃∗ u0 : BitVec 64, a ↦₆₄ u0) ∗ (∃∗ u7 : BitVec 64, (a + 8#64) ↦ₛ EncoderFromPb.loBytes7 u7) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 7) (k := 8) (b' := a + 7#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (mem64_entails (a + 7#64))) ?_
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w7
  rw [v10_pointsTo64_eq_loByte_hiBytes7 (a + 7#64) w7, v10_hiBytes7_eq_loBytes7_lsr8 w7]
  have ha8 : (a + 7#64) + 1#64 = a + 8#64 := by bv_omega
  rw [ha8, ← sepConj_assoc]
  have h8 : memRegion a 7 ∗ ((a + 7#64) ↦₈ loByte w7) ⊢ ∃∗ u0 : BitVec 64, a ↦₆₄ u0 := by
    refine Entails.trans (sepConj_mono_right (pointsTo8_entails_memRegion (a + 7#64) (loByte w7))) ?_
    rw [← ProofLib.memRegion_split' (b := a) (n := 7) (k := 1) (b' := a + 7#64) rfl (by bv_omega) (by decide)]
    exact mem64_entails a
  exact sepConj_mono h8 (Entails.sepExists_right (w7 >>> 8) (Entails.refl _))

theorem v10_fsp_240_split_5728 (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 2064 ⊢
      memRegion (fsp + 240#64) 1152 ∗ (∃∗ u1392 : BitVec 64, (fsp + 1392#64) ↦₆₄ u1392) ∗
      (∃∗ b1400 : BitVec 8, (fsp + 1400#64) ↦₈ b1400) ∗ (∃∗ u1401 : BitVec 64, (fsp + 1401#64) ↦₆₄ u1401) ∗
      ((∃∗ u1409 : BitVec 64, (fsp + 1409#64) ↦₆₄ u1409) ∗
       (∃∗ u1417 : BitVec 64, (fsp + 1417#64) ↦ₛ EncoderFromPb.loBytes7 u1417)) ∗
      (∃∗ u1424 : BitVec 64, (fsp + 1424#64) ↦₆₄ u1424) ∗ (∃∗ u1432 : BitVec 64, (fsp + 1432#64) ↦₆₄ u1432) ∗
      (∃∗ u1440 : BitVec 64, (fsp + 1440#64) ↦₆₄ u1440) ∗
      memRegion (fsp + 1448#64) 440 ∗ memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16 := by
  have h1 : memRegion (fsp + 1400#64) 1 ⊢ ∃∗ b1400 : BitVec 8, (fsp + 1400#64) ↦₈ b1400 := by
    rw [ProofLib.memRegion_one]; exact Entails.refl _
  have h15 : memRegion (fsp + 1409#64) 15 ⊢
      (∃∗ u1409 : BitVec 64, (fsp + 1409#64) ↦₆₄ u1409) ∗
      (∃∗ u1417 : BitVec 64, (fsp + 1417#64) ↦ₛ EncoderFromPb.loBytes7 u1417) := by
    have h := v10_memRegion_15_entails_8_loBytes7 (fsp + 1409#64)
    have ha1417 : (fsp + 1409#64) + 8#64 = fsp + 1417#64 := by bv_omega
    rwa [ha1417] at h
  exact split_top <| split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step h1 <| split_step (mem64_entails _) <| split_step h15 <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (Entails.refl _) <| Entails.refl _

theorem v10_fsp_240_merge_1648 (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 1152 ∗ memRegion (fsp + 1392#64) 56 ∗ memRegion (fsp + 1448#64) 440 ⊢
      memRegion (fsp + 240#64) 1648 :=
  collapse_top <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _

theorem v10_fsp_5808_err_entails_2064 (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 1648 ∗ ((fsp + 1888#64) ↦₆₄ 2#64) ∗
      memRegion (fsp + 1896#64) 392 ∗ memRegion (fsp + 2288#64) 16 ⊢
      memRegion (fsp + 240#64) 2064 :=
  collapse_top <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <| Entails.refl _

/-! ## 5. `+1632 -> s0.x30` when `sendingCt2 = none` and `uc = some { auth := some auth, epoch := ep }` -/

@[simp]
theorem v10_states_from_pb_ct2Sampled_sending_none (F : ShaCompress)
    (auth : ProtoAuthenticator) (ep : BitVec 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct2Sampled
          { sendingCt2 := none, uc := some { auth := some auth, epoch := ep } }) } =
      .error (.err .stateDecode) := rfl

theorem v10_ct2Sent_sending_none_some
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s1 : State) (out pbA ep : BitVec 64)
    (auth : ProtoAuthenticator) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗
        memRegion (pbA + 16#64) 48 ∗ authenticatorPBAt A (pbA + 64#64) auth ∗
        ((pbA + 112#64) ↦₆₄ ep) ∗ memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hm16 : memRegion (pbA + 16#64) 48 =
      (∃∗ b16 : BitVec 8, (pbA + 16#64) ↦₈ b16) ∗ memRegion (pbA + 17#64) 47 := by
    rw [ProofLib.memRegion_split' (b := pbA + 16#64) (n := 1) (k := 47)
          (b' := pbA + 17#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one (pbA + 16#64)]
  rw [hm16, authenticatorPBAt_eq_exists_pinned A (pbA + 64#64) auth]
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (v10_fsp_split_1632 (s0.sp - 2400#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ga => SepWPp.exists_elim fun b16 =>
    SepWPp.exists_elim fun v232 => SepWPp.exists_elim fun v228 =>
    SepWPp.exists_elim fun v224 => SepWPp.exists_elim fun v200 =>
    SepWPp.exists_elim fun v184 => SepWPp.exists_elim fun v152 => ?_
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗
    ((pbA + 16#64) ↦₈ b16) ∗ authenticatorPBPinnedAt A ga (pbA + 64#64) auth ∗
    ((pbA + 112#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗
    (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
    (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗ A.pool ∗
    (memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     (pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 17#64) 47 ∗
     memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
  have h5728 := v10_ct2Sent_1632_to_5728 hA s0 s1 out pbA noneCap ep v152 v184 v200 v232 b16 v224 ga auth
    (memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     (pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 17#64) 47 ∗
     memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTableAt b)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine v10_sepWPp_bind h5728 ?_
  intro s2 P2 hpc2 hrun2 ⟨pa1, pa2, hl1_lt, hP2, hsp2, hx19_2, hx21_2, hx22_2, _, hx26_2, _, htr2⟩
  apply SepWPp.of_sepWP_ret
  have hpb := v10_pbA_none_some_entails_224 pbA b16
  have hd1 := v10_vecU8Payload_entails_vecCapPtrDealloc A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey
  have hd2 := v10_vecU8Payload_entails_vecCapPtrDealloc A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.trans (Entails.of_eq (show _ =
    ((pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗ ((pbA + 16#64) ↦₈ b16) ∗
     memRegion (pbA + 17#64) 47 ∗ memRegion (pbA + 64#64) 56 ∗ memRegion (pbA + 120#64) 104) ∗
    vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
    vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
    ((((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ A.pool ∗
     memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b) by ac_rfl))
    (Entails.trans (sepConj_mono hpb (sepConj_mono hd1 (sepConj_mono_left hd2)))
      (Entails.of_eq (show _ =
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         vecCapPtrDealloc A (BitVec.ofNat 64 auth.rootKey.length) pa1 ∗
         vecCapPtrDealloc A (BitVec.ofNat 64 auth.macKey.length) pa2 ∗ A.pool ∗
         memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
         memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
         (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
         memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl))))) ?_
  have h7212 := v10_ct2Sent_5728_to_7212_none s0 s2 out pa1
    (BitVec.ofNat 64 auth.rootKey.length) (BitVec.ofNat 64 auth.macKey.length)
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     vecCapPtrDealloc A (BitVec.ofNat 64 auth.rootKey.length) pa1 ∗
     vecCapPtrDealloc A (BitVec.ofNat 64 auth.macKey.length) pa2 ∗ A.pool ∗
     memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
    hsp0_align hl1_lt hpc2 hrun2 hsp2 hx19_2 hx21_2 hx22_2 hx26_2 htr2
  refine EncoderFromPb.seq_clean h7212 ?_; intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, hx26_3, htr3⟩
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
    (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ vecCapPtrDealloc A (BitVec.ofNat 64 auth.rootKey.length) pa1 ∗
    vecCapPtrDealloc A (BitVec.ofNat 64 auth.macKey.length) pa2 ∗ A.pool ∗
    (memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
  have h2084 := v10_states_from_pb_err_7212 hA s0 s3 out
    (BitVec.ofNat 64 auth.rootKey.length) pa1 (BitVec.ofNat 64 auth.macKey.length) pa2
    (memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx21_3 hx26_3 htr3
  refine EncoderFromPb.seq_clean h2084 ?_; intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx21_4, htr4⟩
  have hfsp := v10_fsp_unsplit_1632 (s0.sp - 2400#64)
    ep pa2 (BitVec.ofNat 64 auth.rootKey.length) ga.macKey.ptr (b16.zeroExtend 32) v228
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    (memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 2064) ∗
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl))
    (Entails.trans (sepConj_mono_left hfsp) (Entails.of_eq (show _ =
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)))) ?_
  have hx21_byte : (s4.readReg64 .x21).extractLsb' 0 8 = spqrErrorByte .stateDecode := by rw [hx21_4]; rfl
  have herr := v10_states_from_pb_err_2084 (A := A) (F := F) s0 s4 out .stateDecode
    (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc4 hrun4 hsp4 hx19_4 hx21_byte htr4
  refine SepWP.mono herr ?_; intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem v10_sepWPp_entails_to_satisfies {prog : Program} {ret : BitVec 64} {s : State}
    {P R : SepProp} {Q : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (fun sf Pf => Pf ⊢ statesFromPbOnPanic s sf)) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s sf ∗ R)) := by
  intro R' hm hL; obtain ⟨sf, hsteps, hout⟩ := h R' hm hL
  rcases hout with hok | ⟨hst, Pf, hmf, hPf⟩ | hoom
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hst, Pf, hmf, fun hmR => Satisfies.mono (sepConj_mono_left hPf) hmR⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## 6. `+1632 -> s0.x30` when `sendingCt2 = some encPb` and `uc = some { auth := some auth, epoch := ep }` -/

theorem v10_sepWPp_call_ret_entails {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α} (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F : SepProp} {Qpan : State → SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpre : P_step ⊢ spec.pre x s)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf) (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post (fun sf P_f => P_f ⊢ Qpan sf) :=
  SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact Satisfies.mono (sepConj_mono_left hpre) hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ => hpan sf) (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))

theorem v10_states_from_pb_ct2Sampled_sending_some_err (F : ShaCompress)
    (encPb : PolynomialEncoderPB) (auth : ProtoAuthenticator) (ep : BitVec 64)
    (err : PolynomialError) (hres : fromPbResult (pbToProtoPolyEncoder encPb) = .error err) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct2Sampled { sendingCt2 := some encPb, uc := some { auth := some auth, epoch := ep } }) } =
      .error (.err .stateDecode) := by
  simp only [States.from_pb, Chunked.SendCt.Ct2Sampled.from_pb, Unchunked.SendCt.Ct2Sent.from_pb,
    encoderFromPbStateDecode_some, hres, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v10_states_from_pb_ct2Sampled_sending_some_ok (F : ShaCompress)
    (encPb : PolynomialEncoderPB) (auth : ProtoAuthenticator) (ep : BitVec 64)
    (enc : PolyEncoder) (hres : fromPbResult (pbToProtoPolyEncoder encPb) = .ok enc) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct2Sampled { sendingCt2 := some encPb, uc := some { auth := some auth, epoch := ep } }) } =
      .ok (.ct2Sampled { uc := { auth := { rootKey := auth.rootKey, macKey := auth.macKey }, epoch := ep }, sending_ct2 := enc }) := by
  simp only [States.from_pb, Chunked.SendCt.Ct2Sampled.from_pb, Unchunked.SendCt.Ct2Sent.from_pb,
    encoderFromPbStateDecode_some, hres, Bind.bind, Except.bind, Functor.map, Except.map]; rfl

set_option maxHeartbeats 800000 in
theorem v10_ct2Sent_sending_some_some
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hEnc : EncoderFromPbOkExt b A ext) (s0 s1 : State) (out pbA ep : BitVec 64)
    (encPb : PolynomialEncoderPB) (auth : ProtoAuthenticator) (hpts : ∀ bs ∈ encPb.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗
        protoPolynomialEncoderAt A (pbA + 8#64) (pbToProtoPolyEncoder encPb) ∗
        authenticatorPBAt A (pbA + 64#64) auth ∗ ((pbA + 112#64) ↦₆₄ ep) ∗
        memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.ct2Sampled { sendingCt2 := some encPb, uc := some { auth := some auth, epoch := ep } }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  rw [authenticatorPBAt_eq_exists_pinned A (pbA + 64#64) auth]
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono (v10_fsp_split_1632 (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (v10_protoPolynomialEncoderAt_relocate A pbA ((s0.sp - 2400#64) + 1392#64) (pbToProtoPolyEncoder encPb)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ga => SepWPp.exists_elim fun cap_pts => SepWPp.exists_elim fun ptr_pts =>
    SepWPp.exists_elim fun cap_polys => SepWPp.exists_elim fun ptr_polys => SepWPp.exists_elim fun w56 =>
    SepWPp.exists_elim fun P_enc_heap => SepWPp.exists_elim fun v232 => SepWPp.exists_elim fun v228 =>
    SepWPp.exists_elim fun v224 => SepWPp.exists_elim fun v200 => SepWPp.exists_elim fun v184 => SepWPp.exists_elim fun v152 => ?_
  have hp16 := v10_pointsTo64_eq_loByte_hiBytes7 (pbA + 16#64) ptr_pts
  have ha17 : (pbA + 16#64) + 1#64 = pbA + 17#64 := by bv_omega
  rw [ha17] at hp16
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    ⌜cap_pts.toNat < 2 ^ 63 ∧
      ((((s0.sp - 2400#64) + 1392#64) ↦₆₄ cap_pts) ∗ ((((s0.sp - 2400#64) + 1392#64) + 8#64) ↦₆₄ ptr_pts) ∗
       ((((s0.sp - 2400#64) + 1392#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
       ((((s0.sp - 2400#64) + 1392#64) + 24#64) ↦₆₄ cap_polys) ∗ ((((s0.sp - 2400#64) + 1392#64) + 32#64) ↦₆₄ ptr_polys) ∗
       ((((s0.sp - 2400#64) + 1392#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗
       ((((s0.sp - 2400#64) + 1392#64) + 48#64) ↦₆₄ w56) ∗ P_enc_heap ⊢
        protoPolynomialEncoderAt A ((s0.sp - 2400#64) + 1392#64) (pbToProtoPolyEncoder encPb))⌝ ∗
    (((pbA + 16#64) ↦₆₄ ptr_pts) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_pts) ∗
      authenticatorPBPinnedAt A ga (pbA + 64#64) auth ∗ ((pbA + 112#64) ↦₆₄ ep) ∗
      (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗ (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗
      (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗ A.pool ∗
      (memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
       ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
       ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗
       ((pbA + 56#64) ↦₆₄ w56) ∗ P_enc_heap ∗ memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTableAt b))) by ac_rfl)) ?_
  refine SepWPp.pure_left fun ⟨hcap_pts_lt, hreloc_pb⟩ => ?_; rw [hp16]
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_pts) ∗
    ((pbA + 16#64) ↦₈ loByte ptr_pts) ∗ authenticatorPBPinnedAt A ga (pbA + 64#64) auth ∗
    ((pbA + 112#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗
    (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
    (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗ A.pool ∗
    (((pbA + 17#64) ↦ₛ hiBytes7 ptr_pts) ∗ memRegion (s0.sp - 2400#64) 152 ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗
     ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
     ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
     ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗
     ((pbA + 56#64) ↦₆₄ w56) ∗ P_enc_heap ∗ memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
  have h5728 := v10_ct2Sent_1632_to_5728 hA s0 s1 out pbA cap_pts ep v152 v184 v200 v232 (loByte ptr_pts) v224 ga auth
    (((pbA + 17#64) ↦ₛ hiBytes7 ptr_pts) ∗ memRegion (s0.sp - 2400#64) 152 ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗
     ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
     ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
     ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗
     ((pbA + 56#64) ↦₆₄ w56) ∗ P_enc_heap ∗ memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTableAt b)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine v10_sepWPp_bind h5728 ?_
  intro s2 P2 hpc2 hrun2 ⟨pa1, pa2, hl1_lt, hP2, hsp2, hx19_2, hx21_2, hx22_2, _, hx26_2, hx27_2, htr2⟩
  refine SepWPp.weaken_pre (Entails.trans hP2 (Entails.trans (Entails.of_eq (show _ =
    (((pbA + 16#64) ↦₈ loByte ptr_pts) ∗ ((pbA + 17#64) ↦ₛ hiBytes7 ptr_pts)) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_pts) ∗
     memRegion (pbA + 64#64) 56 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ A.pool ∗
     memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗
     ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
     ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
     ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗
     ((pbA + 56#64) ↦₆₄ w56) ∗ P_enc_heap ∗ memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTableAt b) by ac_rfl))
    (sepConj_mono (Entails.of_eq hp16.symm) (sepConj_mono_left (v10_fsp_240_split_5728 (s0.sp - 2400#64)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u1440 => SepWPp.exists_elim fun u1432 =>
    SepWPp.exists_elim fun u1424 => SepWPp.exists_elim fun u1417 =>
    SepWPp.exists_elim fun u1409 => SepWPp.exists_elim fun u1401 =>
    SepWPp.exists_elim fun b1400 => SepWPp.exists_elim fun u1392 => ?_
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
    (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗ ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
    ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
    ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
    ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗
    (((s0.sp - 2400#64) + 1392#64) ↦₆₄ u1392) ∗ (((s0.sp - 2400#64) + 1400#64) ↦₈ b1400) ∗
    (((s0.sp - 2400#64) + 1401#64) ↦₆₄ u1401) ∗ (((s0.sp - 2400#64) + 1409#64) ↦₆₄ u1409) ∗
    (((s0.sp - 2400#64) + 1417#64) ↦ₛ EncoderFromPb.loBytes7 u1417) ∗
    (((s0.sp - 2400#64) + 1424#64) ↦₆₄ u1424) ∗ (((s0.sp - 2400#64) + 1432#64) ↦₆₄ u1432) ∗ (((s0.sp - 2400#64) + 1440#64) ↦₆₄ u1440) ∗
    (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗ memRegion ((s0.sp - 2400#64) + 1448#64) 440 ∗
     memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
     stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_pts) ∗
     memRegion (pbA + 64#64) 56 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ A.pool ∗
     memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗
     P_enc_heap ∗ memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
  have hcopy := v10_ct2Sent_copy_to_encoder_call_5728 s2
    (s0.sp - 2400#64) out pbA pa1 (BitVec.ofNat 64 auth.rootKey.length) (BitVec.ofNat 64 auth.macKey.length)
    cap_pts ptr_pts (BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length)
    cap_polys ptr_polys (BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) w56
    u1392 u1401 u1409 u1417 u1424 u1432 u1440 b1400
    (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗ memRegion ((s0.sp - 2400#64) + 1448#64) 440 ∗
     memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
     stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_pts) ∗
     memRegion (pbA + 64#64) 56 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ A.pool ∗
     memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗
     P_enc_heap ∗ memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTableAt b)
    hfsp_align hl1_lt hcap_pts_lt hpc2 hrun2 hsp2 hx19_2 hx21_2 hx22_2 hx26_2 hx27_2
  refine v10_sepWPp_seq_clean hcopy ?_
  intro s3 hpc3 hrun3 ⟨hsp3, hx0_3, hx1_3, hx19_3, hx21_3, hx22_3, hx26_3, hx27_3, _, hx30_3, htr3⟩
  have htr3_0 : TraceCalleeSaved s3 s0 := htr3.trans htr2
  have hpb224 := v10_pbA_some_some_entails_224 pbA cap_pts ptr_pts
    (BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) cap_polys ptr_polys
    (BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) w56
  have hf1400 : ((s0.sp - 2400#64) + 1392#64) + 8#64 = (s0.sp - 2400#64) + 1400#64 := by bv_omega
  have hf1408 : ((s0.sp - 2400#64) + 1392#64) + 16#64 = (s0.sp - 2400#64) + 1408#64 := by bv_omega
  have hf1416 : ((s0.sp - 2400#64) + 1392#64) + 24#64 = (s0.sp - 2400#64) + 1416#64 := by bv_omega
  have hf1424 : ((s0.sp - 2400#64) + 1392#64) + 32#64 = (s0.sp - 2400#64) + 1424#64 := by bv_omega
  have hf1432 : ((s0.sp - 2400#64) + 1392#64) + 40#64 = (s0.sp - 2400#64) + 1432#64 := by bv_omega
  have hf1440 : ((s0.sp - 2400#64) + 1392#64) + 48#64 = (s0.sp - 2400#64) + 1440#64 := by bv_omega
  rw [hf1400, hf1408, hf1416, hf1424, hf1432, hf1440] at hreloc_pb
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    (((s0.sp - 2400#64) + 1392#64) ↦₆₄ cap_pts ∗ ((s0.sp - 2400#64) + 1400#64) ↦₆₄ ptr_pts ∗
     ((s0.sp - 2400#64) + 1408#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length ∗
     ((s0.sp - 2400#64) + 1416#64) ↦₆₄ cap_polys ∗ ((s0.sp - 2400#64) + 1424#64) ↦₆₄ ptr_polys ∗
     ((s0.sp - 2400#64) + 1432#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length ∗
     ((s0.sp - 2400#64) + 1440#64) ↦₆₄ w56 ∗ P_enc_heap) ∗
    ((pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
     ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
     ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
     ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗
     ((pbA + 56#64) ↦₆₄ w56) ∗ memRegion (pbA + 64#64) 56 ∗ memRegion (pbA + 120#64) 104) ∗
    (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ A.pool ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗ memRegion ((s0.sp - 2400#64) + 1448#64) 440 ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗ (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
      (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
      vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
      vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
      memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
      memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b)) by ac_rfl))
    (Entails.trans (sepConj_mono hreloc_pb (sepConj_mono_left hpb224))
      (Entails.of_eq (show _ =
        (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
         protoPolynomialEncoderAt A ((s0.sp - 2400#64) + 1392#64) (pbToProtoPolyEncoder encPb) ∗
         A.pool ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗
        (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗ memRegion ((s0.sp - 2400#64) + 1448#64) 440 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗ (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
         vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
         vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
         memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
         memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl)))) ?_
  have hsp3_align : s3.spAligned = true := by unfold State.spAligned; rw [hsp3]; exact hfsp_align
  refine v10_sepWPp_call_ret_entails
    (x := { out := (s0.sp - 2400#64) + 1888#64, pbA := (s0.sp - 2400#64) + 1392#64, pb := pbToProtoPolyEncoder encPb })
    hEnc hpc3 hrun3 hsp3_align hx30_3
    (Entails.pure_right ⟨hx0_3, hx1_3, hpts⟩ (by dsimp only [polyEncoderSize]; rw [hsp3]; exact Entails.refl _))
    (fun sf => v10_onPanic_frame_entails htr3_0) (fun _ _ => rfl) ?_
  intro s4 hpc4 hrun4 hsp4_3 hcs34
  simp only [encoderFromPbSpec, protoPolynomialEncoderSize, sepConj_assoc]
  apply ProofLib.SepWP.pure_elim; intro htr4_3
  have hsp4 : s4.sp = s0.sp - 2400#64 := hsp4_3.trans hsp3
  have hx19_4 : s4.readReg64 .x19 = out := (hcs34.1).trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = pa1 := (hcs34.2.2.1).trans hx21_3
  have hx26_4 : s4.readReg64 .x26 = BitVec.ofNat 64 auth.macKey.length := (hcs34.2.2.2.2.2.2.2.1).trans hx26_3
  have htr4 : TraceCalleeSaved s4 s0 := ⟨htr4_3.trans htr3_0.1, hcs34.2.2.2.2.2.2.2.2.2.2.2.trans htr3_0.2⟩
  have hm1648 := v10_fsp_240_merge_1648 (s0.sp - 2400#64)
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 1448#64) 440) ∗
    resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (fromPbResult (pbToProtoPolyEncoder encPb)) ∗
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
     (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗ (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
     (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ A.pool ∗
     memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by rw [hsp3]; ac_rfl))
    (sepConj_mono_left hm1648)) ?_
  cases hres : fromPbResult (pbToProtoPolyEncoder encPb) with
  | error err =>
    rw [v10_states_from_pb_ct2Sampled_sending_some_err F encPb auth ep err hres]
    refine SepWP.weaken_pre (Entails.trans
      (sepConj_mono_right (sepConj_mono_left (v10_resultPolyEncoder_err_entails_tag_392 A (s0.sp - 2400#64) err)))
      (Entails.of_eq (show _ =
        (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
        (memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗ (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
         vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
         vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ A.pool ∗
         memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
         memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl))) ?_
    have h5820 := v10_ct2Sent_5808_to_5820_err s0 s4 out pa1 (BitVec.ofNat 64 auth.macKey.length)
      (memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗ (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ A.pool ∗
       memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
      hsp0_align hpc4 hrun4 hsp4 hx19_4 hx21_4 hx26_4 htr4
    refine EncoderFromPb.seq_clean h5820 ?_; intro s5 hpc5 hrun5 ⟨hsp5, hx19_5, hx21_5, hx26_5, htr5⟩
    have hf2064 := v10_fsp_5808_err_entails_2064 (s0.sp - 2400#64)
    have hd1 := v10_vecU8Payload_entails_vecCapPtrDealloc A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey
    have hd2 := v10_vecU8Payload_entails_vecCapPtrDealloc A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
       memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
      vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
      vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ A.pool ∗ memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
       memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl))
      (Entails.trans (sepConj_mono hf2064 (sepConj_mono hd1 (sepConj_mono_left hd2)))
        (Entails.of_eq (show _ =
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ vecCapPtrDealloc A (BitVec.ofNat 64 auth.rootKey.length) pa1 ∗
          vecCapPtrDealloc A (BitVec.ofNat 64 auth.macKey.length) pa2 ∗ A.pool ∗
          (memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
           memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
           memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
           (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
           memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl)))) ?_
    have h2084 := v10_states_from_pb_err_5820 hA s0 s5 out
      (BitVec.ofNat 64 auth.rootKey.length) pa1 (BitVec.ofNat 64 auth.macKey.length) pa2
      (memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
       memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
      hsp0_align hpc5 hrun5 hsp5 hx19_5 hx21_5 hx26_5 htr5
    refine EncoderFromPb.seq_clean h2084 ?_; intro s6 hpc6 hrun6 ⟨hsp6, hx19_6, hx21_6, htr6⟩
    have hfsp := v10_fsp_unsplit_1632 (s0.sp - 2400#64)
      ep pa2 (BitVec.ofNat 64 auth.rootKey.length) ga.macKey.ptr ((loByte ptr_pts).zeroExtend 32) v228
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
       memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       memRegion ((s0.sp - 2400#64) + 240#64) 2064) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl))
      (Entails.trans (sepConj_mono_left hfsp) (Entails.of_eq (show _ =
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)))) ?_
    have hx21_byte : (s6.readReg64 .x21).extractLsb' 0 8 = spqrErrorByte .stateDecode := by rw [hx21_6]; rfl
    have herr := v10_states_from_pb_err_2084 (A := A) (F := F) s0 s6 out .stateDecode
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
      hsp0_align hpc6 hrun6 hsp6 hx19_6 hx21_byte htr6
    refine SepWP.mono herr ?_; intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  | ok enc =>
    rw [v10_states_from_pb_ct2Sampled_sending_some_ok F encPb auth ep enc hres]; dsimp only [resultPolyEncoderFromPbAt]
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (v10_polyEncoderAt_relocate A ((s0.sp - 2400#64) + 1888#64) (out + 8#64) enc))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine ProofLib.SepWP.exists_left fun tag => ProofLib.SepWP.exists_left fun bs =>
      ProofLib.SepWP.exists_left fun hi32 => ProofLib.SepWP.exists_left fun P_heap => ?_
    have hm224 := v10_pointsTo32_pair_eq_pointsTo64 ((s0.sp - 2400#64) + 224#64) ((loByte ptr_pts).zeroExtend 32) v228
    have ha228 : ((s0.sp - 2400#64) + 224#64) + 4#64 = (s0.sp - 2400#64) + 228#64 := by bv_omega
    have ha2280 : ((s0.sp - 2400#64) + 1888#64) + 392#64 = (s0.sp - 2400#64) + 2280#64 := by bv_omega
    rw [ha228] at hm224; rw [v10_bs384_eq_encCells bs.val bs.property ((s0.sp - 2400#64) + 1888#64), ha2280]
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      ⌜(tag = 0#64 ∨ tag = 1#64) ∧
        (((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs.val) ∗
         (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢ polyEncoderAt A (out + 8#64) enc)⌝ ∗
      ((((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗ (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228)) ∗
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗
       ((memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
         memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
        (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗ v10_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
        (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗ P_heap ∗ vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
        vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool))) by ac_rfl))
      (sepConj_mono_right (sepConj_mono_left (Entails.of_eq hm224)))) ?_
    apply ProofLib.SepWP.pure_elim; rintro ⟨htag, hreloc_out⟩
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗
      ((memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
        memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ (v228 ++ (loByte ptr_pts).zeroExtend 32)) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗ v10_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
       (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ P_heap ∗ vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
       (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl)) ?_
    have h7904 := v10_ct2Sent_5808_to_7904_ok s0 s4 (s0.sp - 2400#64) tag htag
      ((memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
        memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ (v228 ++ (loByte ptr_pts).zeroExtend 32)) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗ v10_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
       (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ P_heap ∗ vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
       (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool))
      hfsp_align hpc4 hrun4 hsp4 htr4
    refine EncoderFromPb.seq_clean h7904 ?_; intro s5 hpc5 hrun5 ⟨hsp5, hx15_5, hx19_5, hx21_5, hx26_5, htr5⟩
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648) ∗
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ (v228 ++ (loByte ptr_pts).zeroExtend 32)) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
      (((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ v10_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
      (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
      statesFromPbSavedCells s0 ∗ P_heap ∗ vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
      vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
    have hret := v10_ct2Sent_7904_to_ret (F := F) hA s0 s5 (s0.sp - 2400#64) out tag ep
      pa1 (BitVec.ofNat 64 auth.rootKey.length) pa2 (BitVec.ofNat 64 auth.macKey.length)
      (v228 ++ (loByte ptr_pts).zeroExtend 32) ga.macKey.ptr
      bs.val bs.property hi32 enc P_heap hreloc_out auth.rootKey auth.macKey rfl rfl
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
      hsp0_align rfl hpc5 hrun5 hsp5 hx15_5 (hx19_5.trans hx19_4) (hx21_5.trans hx21_4) (hx26_5.trans hx26_4) htr5
    refine SepWP.mono hret ?_; intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-! ## 7. Top-Level Variant 10 Theorem (`states_from_pb_ct2Sampled_1632`) -/

theorem states_from_pb_ct2Sampled_1632
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hEnc : EncoderFromPbOkExt b A ext)
    (s0 s1 : State) (out pbA : BitVec 64) (s : V1State.Chunked.Ct2Sampled) (R : SepProp)
    (hpts : optEncoderPtsBound s.sendingCt2) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some (.ct2Sampled s)) ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct2Sampled s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have htr_eq : statesFromPbOnPanic s0 = statesFromPbOnPanic s1 := by
    funext sf; unfold statesFromPbOnPanic allocFailedIn; rw [htr1.1]
  rw [htr_eq]; apply v10_sepWPp_entails_to_satisfies; rw [← htr_eq]
  dsimp only [optProtoInnerStateAt, protoInnerStateAt]; cases s with | mk uc sendingCt2 =>
  cases uc with
  | none =>
    exact SepWPp.of_sepWP_ret (v10_ct2Sent_err_1632_uc_none_2304 (F := F) hA s0 s1 out pbA sendingCt2
      hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
  | some uc =>
    cases uc with | mk ep auth =>
    cases auth with
    | none =>
      exact SepWPp.of_sepWP_ret (v10_ct2Sent_err_1632_auth_none_2304 (F := F) hA s0 s1 out pbA ep sendingCt2
        hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
    | some auth =>
      dsimp only [protoChunkedCt2SampledAt, optProtoUnchunkedCt2SentAt, protoUnchunkedCt2SentAt, optProtoAuthenticatorAt]
      have ha64 : (pbA + 8#64) + 56#64 = pbA + 64#64 := by bv_omega
      have ha112 : (pbA + 64#64) + 48#64 = pbA + 112#64 := by bv_omega
      rw [ha64, ha112]; cases sendingCt2 with
      | none =>
        dsimp only [Option.map, optProtoPolynomialEncoderAt]
        have ha16 : (pbA + 8#64) + 8#64 = pbA + 16#64 := by bv_omega
        rw [ha16]; simp only [sepConj_assoc, v10_states_from_pb_ct2Sampled_sending_none]
        exact v10_ct2Sent_sending_none_some (F := F) hA s0 s1 out pbA ep auth
          hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
      | some encPb =>
        dsimp only [Option.map, optProtoPolynomialEncoderAt]; simp only [sepConj_assoc]
        exact v10_ct2Sent_sending_some_some (F := F) hA hEnc s0 s1 out pbA ep encPb auth hpts
          hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

end CryptoVerification.SpqrV1.States.FromPb

