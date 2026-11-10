/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueExt
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-! # `<spqr::v1::chunked::states::States>::from_pb`: Variant 0 (`KeysUnsampled`, `+156`) -/

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
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓] statesFromPb_fnOff
  stubOff_rust_no_alloc_shim stubOff_rust_alloc stubOff_rust_dealloc stubOff_memcpy stubOff_handle_error

/-! ## Variant 0 (`KeysUnsampled`, `+156`) Error Paths (`uc = none` and `auth = none`) -/

theorem pbA_keysUnsampled_uc_none_entails_224 (pbA : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 8#64) ↦₆₄ none2Cap) ∗
      memRegion (pbA + 16#64) 48 ∗ memRegion (pbA + 64#64) 160 ⊢
    memRegion pbA optProtoInnerStateSize := by
  exact collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| Entails.refl _

theorem pbA_keysUnsampled_auth_none_entails_224 (pbA ep : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗
      memRegion (pbA + 16#64) 40 ∗ ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ⊢
    memRegion pbA optProtoInnerStateSize := by
  exact collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _

/-- `KeysUnsampled` error path when `s.uc = none` (`+156 -> +2044 -> s0.x30`). -/
theorem states_from_pb_keysUnsampled_uc_none
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 156#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 8#64) ↦₆₄ none2Cap) ∗
        memRegion (pbA + 16#64) 48 ∗ memRegion (pbA + 64#64) 160 ∗
        statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := none }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2044#64)
    (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool))
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 156 12
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, none2Cap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hpb := pbA_keysUnsampled_uc_none_entails_224 pbA
      dsimp only [none2Cap] at hpb
      refine Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpb)))))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    have hep := states_from_pb_err_2044 (A := A) (F := F) s0 s2 out
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2
    refine SepWP.mono hep fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨Entails.trans hPf ?_, hsp_f, hcc_f, htr_f⟩
    change resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) ∗
        stackAt s0.sp statesFromPbStack ⊢
      resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗
        A.pool ∗ stackAt s0.sp statesFromPbStack
    exact Entails.of_eq (by ac_rfl)

/-- `KeysUnsampled` error path when `s.uc = some { auth := none, epoch := ep }` (`+156 -> +2044 -> s0.x30`). -/
theorem states_from_pb_keysUnsampled_auth_none
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA ep : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 156#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗
        memRegion (pbA + 16#64) 40 ∗ ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗
        statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := some { auth := none, epoch := ep } }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2044#64)
    (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool))
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 156 20
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hpb := pbA_keysUnsampled_auth_none_entails_224 pbA ep
      dsimp only [noneCap] at hpb
      refine Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpb)))))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    have hep := states_from_pb_err_2044 (A := A) (F := F) s0 s2 out
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2
    refine SepWP.mono hep fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨Entails.trans hPf ?_, hsp_f, hcc_f, htr_f⟩
    change resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) ∗
        stackAt s0.sp statesFromPbStack ⊢
      resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗
        A.pool ∗ stackAt s0.sp statesFromPbStack
    exact Entails.of_eq (by ac_rfl)

theorem pbA_keysUnsampled_some_entails_224 (pbA c1 p1 l1 c2 p2 l2 ep : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000000#64) ∗
      ((pbA + 8#64) ↦₆₄ c1) ∗ ((pbA + 16#64) ↦₆₄ p1) ∗ ((pbA + 24#64) ↦₆₄ l1) ∗
      ((pbA + 32#64) ↦₆₄ c2) ∗ ((pbA + 40#64) ↦₆₄ p2) ∗ ((pbA + 48#64) ↦₆₄ l2) ∗
      ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ⊢
      memRegion pbA optProtoInnerStateSize := by
  exact collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _

theorem authPBPinnedTailAt_8_eq (A : RustAlloc) (ga : AuthenticatorPBGhost) (a : BitVec 64)
    (auth : ProtoAuthenticator) :
    authPBPinnedTailAt A ga (a + 8#64) auth =
      ((a + 16#64) ↦₆₄ ga.rootKey.ptr) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
      vecU8At A (a + 32#64) ga.macKey.cap ga.macKey.ptr auth.macKey := by
  unfold authPBPinnedTailAt
  have h1 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have h2 : (a + 8#64) + 16#64 = a + 24#64 := by bv_omega
  have h3 : (a + 8#64) + 24#64 = a + 32#64 := by bv_omega
  rw [h1, h2, h3]

theorem authenticatorPBPinnedAt_8_eq_cap_tail (A : RustAlloc) (ga : AuthenticatorPBGhost)
    (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (a + 8#64) auth =
      ((a + 8#64) ↦₆₄ ga.rootKey.cap) ∗
      ((a + 16#64) ↦₆₄ ga.rootKey.ptr) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
      vecU8At A (a + 32#64) ga.macKey.cap ga.macKey.ptr auth.macKey := by
  rw [authenticatorPBPinnedAt_eq_cap_tail, authPBPinnedTailAt_8_eq]

theorem authenticatorPBPinnedAt_8_eq_full (A : RustAlloc) (ga : AuthenticatorPBGhost)
    (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (a + 8#64) auth =
      ((a + 8#64) ↦₆₄ ga.rootKey.cap) ∗
      ((a + 16#64) ↦₆₄ ga.rootKey.ptr) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((a + 32#64) ↦₆₄ ga.macKey.cap) ∗
      ((a + 40#64) ↦₆₄ ga.macKey.ptr) ∗ ((a + 48#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
      vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey := by
  rw [authenticatorPBPinnedAt_8_eq_cap_tail]
  unfold vecU8At vecHeader vecU8Payload
  have h1 : (a + 32#64) + 8#64 = a + 40#64 := by bv_omega
  have h2 : (a + 32#64) + 16#64 = a + 48#64 := by bv_omega
  rw [h1, h2]
  ac_rfl

@[simp]
theorem spqrAuthApi_from_pb (F : ShaCompress) :
    (spqrAuthApi F).from_pb = Authenticator.fromPb := rfl

theorem sepWPp_seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

theorem optProtoInnerStateAt_keysUnsampled_some_eq (A : RustAlloc) (pbA : BitVec 64)
    (auth : ProtoAuthenticator) (ep : BitVec 64) :
    optProtoInnerStateAt A pbA (some (.keysUnsampled { uc := some { auth := some auth, epoch := ep } })) =
      (pbA ↦₆₄ 0x8000000000000000#64) ∗
      optProtoAuthenticatorAt A (pbA + 8#64) (some auth) ∗
      ((pbA + 56#64) ↦₆₄ ep) ∗
      memRegion (pbA + 64#64) 160 := by
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedKeysUnsampledAt,
    optProtoUnchunkedKeysUnsampledAt, protoUnchunkedKeysUnsampledAt]
  have h56 : (pbA + 8#64) + 48#64 = pbA + 56#64 := by bv_omega
  rw [h56]; ac_rfl

@[simp]
theorem states_from_pb_keysUnsampled_uc_none_eq (F : ShaCompress) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.keysUnsampled { uc := none }) } =
      .error (.err .stateDecode) := rfl

@[simp]
theorem states_from_pb_keysUnsampled_auth_none_eq (F : ShaCompress) (ep : BitVec 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.keysUnsampled { uc := some { auth := none, epoch := ep } }) } =
      .error (.err .stateDecode) := rfl

@[simp]
theorem states_from_pb_keysUnsampled_some_eq (F : ShaCompress)
    (auth : ProtoAuthenticator) (ep : BitVec 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.keysUnsampled { uc := some { auth := some auth, epoch := ep } }) } =
      .ok (.keysUnsampled { uc := { auth := Authenticator.fromPb auth, epoch := ep } }) :=
  rfl

theorem authenticatorAt_8_pack (A : RustAlloc) (out ca1 pa1 ca2 pa2 : BitVec 64)
    (auth : Authenticator) :
    ((out + 8#64) ↦₆₄ ca1) ∗ ((out + 16#64) ↦₆₄ pa1) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((out + 32#64) ↦₆₄ ca2) ∗ ((out + 40#64) ↦₆₄ pa2) ∗
      ((out + 48#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      vecU8Payload A ca1 pa1 auth.rootKey ∗
      vecU8Payload A ca2 pa2 auth.macKey ⊢
    authenticatorAt A (out + 8#64) auth := by
  unfold authenticatorAt
  have h1 := vecU8_of_header_payload A (out + 8#64) ca1 pa1 auth.rootKey
  have h2 := vecU8_of_header_payload A (out + 32#64) ca2 pa2 auth.macKey
  have ha1 : (out + 8#64) + 8#64 = out + 16#64 := by bv_omega
  have ha2 : (out + 8#64) + 16#64 = out + 24#64 := by bv_omega
  have ha3 : (out + 8#64) + 24#64 = out + 32#64 := by bv_omega
  have hb1 : (out + 32#64) + 8#64 = out + 40#64 := by bv_omega
  have hb2 : (out + 32#64) + 16#64 = out + 48#64 := by bv_omega
  rw [ha1, ha2] at h1
  rw [hb1, hb2] at h2
  rw [ha3]
  refine Entails.trans (Entails.of_eq (show _ =
    (((out + 8#64) ↦₆₄ ca1) ∗ ((out + 16#64) ↦₆₄ pa1) ∗
     ((out + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     vecU8Payload A ca1 pa1 auth.rootKey) ∗
    (((out + 32#64) ↦₆₄ ca2) ∗ ((out + 40#64) ↦₆₄ pa2) ∗
     ((out + 48#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
     vecU8Payload A ca2 pa2 auth.macKey) by ac_rfl)) ?_
  exact sepConj_mono h1 h2

theorem memRegion_2304_split_152_208 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 152 ∗
      (∃∗ w152 : BitVec 64, ((fsp + 152#64) ↦₆₄ w152)) ∗
      memRegion (fsp + 160#64) 48 ∗
      (∃∗ w208 : BitVec 64, ((fsp + 208#64) ↦₆₄ w208)) ∗
      memRegion (fsp + 216#64) 2088 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem memRegion_152_8_48_entails_208 (fsp w152 : BitVec 64) :
    memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ memRegion (fsp + 160#64) 48 ⊢
      memRegion fsp 208 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

theorem memRegion_loBytes7_gap_at (a o1 o2 : BitVec 64) (k : Nat)
    (ho : o1 + 7#64 = o2 := by rfl)
    (hk : 8 + k ≤ 2 ^ 64 := by decide) :
    ProofLib.memRegion (a + o1) (7 + (1 + k)) ⊢
      (∃∗ u0 : BitVec 64, ((a + o1) ↦ₛ EncoderFromPb.loBytes7 u0)) ∗
      ProofLib.memRegion (a + o2) (1 + k) := by
  have h1 : 7 + (1 + k) = 8 + k := by omega
  rw [h1, ProofLib.memRegion_split' (b := a + o1) (n := 8) (k := k)
    (b' := a + o1 + 8#64) rfl rfl hk,
    ProofLib.memRegion_eight (a + o1), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro u0
  rw [pointsTo64_split_7_1 (a + o1) u0, sepConj_assoc, sepExists_sepConj_left]
  refine Entails.sepExists_right u0 (sepConj_mono_right ?_)
  have ha7 : a + o1 + 7#64 = a + o2 := by rw [BitVec.add_assoc, ho]
  have ha8 : a + o1 + 8#64 = a + o2 + 1#64 := by rw [← ha7]; bv_omega
  rw [ha7, ha8, ProofLib.memRegion_split' (b := a + o2) (n := 1) (k := k)
    (b' := a + o2 + 1#64) rfl rfl (by omega)]
  exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)

theorem memRegion_entails_bs :
    ∀ (n : Nat) (a : BitVec 64), n ≤ 2 ^ 64 →
      ProofLib.memRegion a n ⊢
        ∃∗ bs : { l : List (BitVec 8) // l.length = n }, (a ↦ₛ bs.val)
  | 0, a, _ => by
    rw [ProofLib.memRegion_zero]
    refine Entails.sepExists_right ⟨[], rfl⟩ ?_
    rw [ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | n + 1, a, hn => by
    have hsplit : n + 1 = 1 + n := by omega
    rw [hsplit, ProofLib.memRegion_split a 1 n (by omega), ProofLib.memRegion_one a,
        sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro b0
    refine Entails.trans (sepConj_mono_right (memRegion_entails_bs n (a + 1#64) (by omega))) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ⟨bs, hlen⟩
    refine Entails.sepExists_right ⟨b0 :: bs, by simp [hlen]; omega⟩ ?_
    rw [ProofLib.pointsToBytes_cons]
    exact Entails.refl _

theorem memRegion_328_entails_bs (a : BitVec 64) :
    ProofLib.memRegion a 328 ⊢
      ∃∗ bs : { l : List (BitVec 8) // l.length = 328 }, (a ↦ₛ bs.val) :=
  memRegion_entails_bs 328 a (by decide)

theorem memRegion_208_entails_epilogue_lo (fsp : BitVec 64) :
    memRegion fsp 208 ⊢
      memRegion fsp 92 ∗ (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92)) ∗
      memRegion (fsp + 96#64) 8 ∗ (∃∗ w104 : BitVec 64, ((fsp + 104#64) ↦₆₄ w104)) ∗
      (∃∗ w112 : BitVec 64, ((fsp + 112#64) ↦₆₄ w112)) ∗ (∃∗ w120 : BitVec 64, ((fsp + 120#64) ↦₆₄ w120)) ∗
      memRegion (fsp + 128#64) 32 ∗ (∃∗ w160 : BitVec 64, ((fsp + 160#64) ↦₆₄ w160)) ∗
      memRegion (fsp + 168#64) 4 ∗ (∃∗ d172 : BitVec 32, ((fsp + 172#64) ↦₃₂ d172)) ∗
      memRegion (fsp + 176#64) 16 ∗ (∃∗ w192 : BitVec 64, ((fsp + 192#64) ↦₆₄ w192)) ∗
      memRegion (fsp + 200#64) 8 := by
  exact split_top <| split_step0 (Entails.refl _) <| split_step (mem32_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem32_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <| Entails.refl _

theorem memRegion_2088_entails_epilogue_hi (fsp : BitVec 64) :
    memRegion (fsp + 216#64) 2088 ⊢
      memRegion (fsp + 216#64) 8 ∗ (∃∗ w224 : BitVec 64, ((fsp + 224#64) ↦₆₄ w224)) ∗
      (∃∗ w232 : BitVec 64, ((fsp + 232#64) ↦₆₄ w232)) ∗
      (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
      memRegion (fsp + 568#64) 8 ∗ (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗
      ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗ memRegion (fsp + 599#64) 9) ∗
      (∃∗ q608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ q608)) ∗ (∃∗ q624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ q624)) ∗
      (∃∗ q640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ q640)) ∗ (∃∗ q656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ q656)) ∗
      (∃∗ q672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ q672)) ∗ (∃∗ q688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ q688)) ∗
      (∃∗ q704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ q704)) ∗ (∃∗ q720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ q720)) ∗
      (∃∗ q736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ q736)) ∗ (∃∗ q752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ q752)) ∗
      (∃∗ q768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ q768)) ∗ (∃∗ q784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ q784)) ∗
      (∃∗ q800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ q800)) ∗ (∃∗ q816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ q816)) ∗
      (∃∗ w832 : BitVec 64, ((fsp + 832#64) ↦₆₄ w832)) ∗ memRegion (fsp + 840#64) 8 ∗
      (∃∗ q848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ q848)) ∗
      ((∃∗ w864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864)) ∗ memRegion (fsp + 871#64) 9) ∗
      (∃∗ w880 : BitVec 64, ((fsp + 880#64) ↦₆₄ w880)) ∗
      ((∃∗ w888 : BitVec 64, ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888)) ∗ memRegion (fsp + 895#64) 993) ∗
      (∃∗ q1888 : BitVec 128, ((fsp + 1888#64) ↦₁₂₈ q1888)) ∗
      (∃∗ q1904 : BitVec 128, ((fsp + 1904#64) ↦₁₂₈ q1904)) ∗
      (∃∗ w1920 : BitVec 64, ((fsp + 1920#64) ↦₆₄ w1920)) ∗ memRegion (fsp + 1928#64) 376 := by
  exact split_top <| split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (memRegion_328_entails_bs _) <|
    split_step (Entails.refl _) <| split_step (mem128_entails _) <|
    split_step (memRegion_loBytes7_gap_at fsp 592#64 599#64 8) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem128_entails _) <| split_step (memRegion_loBytes7_gap_at fsp 864#64 871#64 8) <|
    split_step (mem64_entails _) <| split_step (memRegion_loBytes7_gap_at fsp 888#64 895#64 992) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem64_entails _) <| Entails.refl _

theorem states_from_pb_epilogue_8176_keysUnsampled
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext) (s0 s : State) (out pa1 : BitVec 64) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8176#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion (s0.sp - 2400#64) 208 ∗ ((s0.sp - 2400#64 + 208#64) ↦₆₄ pa1) ∗
       memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (out ↦₆₄ s.readReg64 .x8) ∗ ((out + 8#64) ↦₆₄ s.readReg64 .x15) ∗
          ((out + 16#64) ↦₆₄ pa1) ∗ ((out + 24#64) ↦₆₄ s.readReg64 .x20) ∗
          ((out + 32#64) ↦₆₄ s.readReg64 .x13) ∗ ((out + 40#64) ↦₆₄ s.readReg64 .x25) ∗
          ((out + 48#64) ↦₆₄ s.readReg64 .x30) ∗ ((out + 56#64) ↦₆₄ s.readReg64 .x9) ∗
          memRegion (out + 64#64) 864 ∗ stackAt s0.sp statesFromPbStack ∗ Frame) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (memRegion_208_entails_epilogue_lo (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_left (memRegion_2088_entails_epilogue_hi (s0.sp - 2400#64))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun w1920 => ProofLib.SepWP.exists_left fun q1904 =>
    ProofLib.SepWP.exists_left fun q1888 => ProofLib.SepWP.exists_left fun w888 =>
    ProofLib.SepWP.exists_left fun w880 => ProofLib.SepWP.exists_left fun w864 =>
    ProofLib.SepWP.exists_left fun q848 => ProofLib.SepWP.exists_left fun w832 =>
    ProofLib.SepWP.exists_left fun q816 => ProofLib.SepWP.exists_left fun q800 =>
    ProofLib.SepWP.exists_left fun q784 => ProofLib.SepWP.exists_left fun q768 =>
    ProofLib.SepWP.exists_left fun q752 => ProofLib.SepWP.exists_left fun q736 =>
    ProofLib.SepWP.exists_left fun q720 => ProofLib.SepWP.exists_left fun q704 =>
    ProofLib.SepWP.exists_left fun q688 => ProofLib.SepWP.exists_left fun q672 =>
    ProofLib.SepWP.exists_left fun q656 => ProofLib.SepWP.exists_left fun q640 =>
    ProofLib.SepWP.exists_left fun q624 => ProofLib.SepWP.exists_left fun q608 =>
    ProofLib.SepWP.exists_left fun w592 => ProofLib.SepWP.exists_left fun q576 =>
    ProofLib.SepWP.exists_left fun bs240 => ProofLib.SepWP.exists_left fun w232 =>
    ProofLib.SepWP.exists_left fun w224 => ProofLib.SepWP.exists_left fun w192 =>
    ProofLib.SepWP.exists_left fun d172 => ProofLib.SepWP.exists_left fun w160 =>
    ProofLib.SepWP.exists_left fun w120 => ProofLib.SepWP.exists_left fun w112 =>
    ProofLib.SepWP.exists_left fun w104 => ProofLib.SepWP.exists_left fun d92 => ?_
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
    epilogueStackSlots (s0.sp - 2400#64) d92 d172 w104 w112 w120 w160 w192 pa1 w224 w232 bs240.val
      q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
      w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
    epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame by
      unfold epilogueStackSlots epilogueStackGaps; ac_rfl)) ?_
  refine SepWP.mono (states_from_pb_epilogue_8176_sfa hA s0 s out
    d92 d172 w104 w112 w120 w160 w192 pa1 w224 w232 bs240.val bs240.property
    q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    w832 q848 w864 w880 w888 q1888 q1904 w1920 Frame halign hpc hrun hsp hx19 hx23 htr) ?_
  intro sm Pm _ _ ⟨hPm, hsp_m, hcc_m, htr_m⟩
  refine ⟨Entails.trans hPm (Entails.trans (sepConj_mono_left (epilogueOutFull_entails_64_864 out
    (s.readReg64 .x8) (s.readReg64 .x15) pa1 (s.readReg64 .x20)
    (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
    (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
    ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
    (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
    (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
    (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
    w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
    (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
    (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
    (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
    (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
    w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
    bs240.val bs240.property q1888 q1904 w1920)) (Entails.of_eq (by ac_rfl))), hsp_m, hcc_m, htr_m⟩

theorem pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

theorem vecU8Payload_of_nil (A : RustAlloc) :
    emp ⊢ vecU8Payload A (BitVec.ofNat 64 ([] : List (BitVec 8)).length) 1#64 [] := by
  unfold vecU8Payload
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.le_refl, true_and, ↓reduceIte]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.refl _)

theorem vecU8Payload_pos_unpack (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8Payload A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
      (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8Payload
  apply Entails.pure_left; intro ⟨hle, hlt, hptr⟩
  have hcap : cap ≠ 0#64 := cap_ne_zero_of_pos hpos hle
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hptr, hcap⟩ (Entails.refl _)

theorem vecU8Payload_pos_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hcap : cap ≠ 0#64) :
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
    vecCapPtrDealloc A cap ptr := by
  refine Entails.trans ?_ (vecU8Payload_entails_dealloc A cap ptr bs)
  unfold vecU8Payload
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

theorem vecU8Payload_extract_len_lt63 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Payload A cap ptr bs ⊢ ⌜bs.length < 2 ^ 63⌝ ∗ vecU8Payload A cap ptr bs := by
  unfold vecU8Payload
  apply Entails.pure_left; intro ⟨hle, hlt, hne⟩
  exact Entails.pure_right (Nat.lt_of_le_of_lt hle hlt)
    (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

/-- `KeysUnsampled` entry unpack (`+156 -> +200`):
    loads `ga.rootKey`, `ga.macKey`, and `ep` from `pbA`, stores `ep` at `[fsp + 152]`,
    and collapses `pbA` into `memRegion pbA optProtoInnerStateSize`. -/
theorem states_from_pb_keysUnsampled_step0_156_200
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out pbA ep w152 : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator) (Frame : SepProp)
    (hcap0 : ga.rootKey.cap.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 156#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 200#64) s
      ((pbA ↦₆₄ 0x8000000000000000#64) ∗ authenticatorPBPinnedAt A ga (pbA + 8#64) auth ∗
       ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 152#64) ↦₆₄ ep) ∗
          vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
          vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗
          memRegion pbA optProtoInnerStateSize ∗ Frame) ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x22 = ga.rootKey.cap ∧ s1.readReg64 .x24 = ga.rootKey.ptr ∧
        s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
        s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s1 s) := by
  have hcmn2 : (ga.rootKey.cap + 2#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_two_beq_zero_false hcap0)
  have hcmn1 : (ga.rootKey.cap + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hcap0)
  rw [authenticatorPBPinnedAt_8_eq_full]
  states_from_pb_fetches_range b (Rust.withPanics ext) 156 44
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches; wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hpb := pbA_keysUnsampled_some_entails_224 pbA
      ga.rootKey.cap ga.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
      ga.macKey.cap ga.macKey.ptr (BitVec.ofNat 64 auth.macKey.length) ep
    refine Entails.trans (Entails.of_eq (show _ =
      ((pbA ↦₆₄ 0x8000000000000000#64) ∗
       ((pbA + 8#64) ↦₆₄ ga.rootKey.cap) ∗ ((pbA + 16#64) ↦₆₄ ga.rootKey.ptr) ∗
       ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       ((pbA + 32#64) ↦₆₄ ga.macKey.cap) ∗ ((pbA + 40#64) ↦₆₄ ga.macKey.ptr) ∗
       ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
       ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160) ∗
      ((fsp + 152#64) ↦₆₄ ep) ∗ vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
      vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ Frame by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))
  · wp_done

set_option maxHeartbeats 800000 in
theorem states_from_pb_keysUnsampled_step1_200_5476
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext) (s0 s : State) (target_pc fsp out w208 : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 200#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx22 : s.readReg64 .x22 = ga.rootKey.cap) (hx24 : s.readReg64 .x24 = ga.rootKey.ptr)
    (hx20 : s.readReg64 .x20 = ga.macKey.cap) (hx21 : s.readReg64 .x21 = ga.macKey.ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length) (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa1 : BitVec 64) (s1 : State),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5476#64 →
      s1.status = .Running →
      (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
       s1.readReg64 .x22 = ga.rootKey.cap ∧ s1.readReg64 .x24 = ga.rootKey.ptr ∧
       s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
       s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
       s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
       s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s1 s0) →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc s1
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗
         vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
         vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗ A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
       vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗ A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hr_cases : auth.rootKey = [] ∨ 0 < auth.rootKey.length := by cases auth.rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · refine sepWPp_seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5476#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ 1#64) ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
        vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) 1#64 auth.rootKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x22 = ga.rootKey.cap ∧ s1.readReg64 .x24 = ga.rootKey.ptr ∧
        s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
        s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s1 s0)
      ?_ (hnext 1#64)
    clear hnext; rw [hr_nil] at hx26 ⊢
    states_from_pb_fetches_range b (Rust.withPanics ext) 200 4
    states_from_pb_fetches_range b (Rust.withPanics ext) 5468 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, List.length_nil, BitVec.ofNat_eq_ofNat] at hpc hx26 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A ga.rootKey.cap ga.rootKey.ptr []
      have hn := vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A ga.rootKey.cap ga.rootKey.ptr [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ 1#64) ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecU8Payload_pos_unpack A ga.rootKey.cap ga.rootKey.ptr auth.rootKey hr_pos)))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
          (⌜auth.rootKey.length ≤ ga.rootKey.cap.toNat ∧ ga.rootKey.cap.toNat < 2 ^ 63 ∧
            ga.rootKey.ptr ≠ 0#64 ∧ ga.rootKey.cap ≠ 0#64⌝ ∗
           (A.live ga.rootKey.ptr ga.rootKey.cap.toNat 1 ∗ (ga.rootKey.ptr ↦ₛ auth.rootKey) ∗
            memRegion (ga.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (ga.rootKey.cap.toNat - auth.rootKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.rootKey.length ≤ ga.rootKey.cap.toNat ∧ ga.rootKey.cap.toNat < 2 ^ 63 ∧
          ga.rootKey.ptr ≠ 0#64 ∧ ga.rootKey.cap ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
         A.live ga.rootKey.ptr ga.rootKey.cap.toNat 1 ∗ (ga.rootKey.ptr ↦ₛ auth.rootKey) ∗
         memRegion (ga.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (ga.rootKey.cap.toNat - auth.rootKey.length) ∗
         A.pool ∗ Frame) by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hr_le, hr_cap, hptr0, hcap0_ne⟩ => ?_
    have hr_lt63 : auth.rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 auth.rootKey.length == 0#64) = false := ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hr_lay3 : auth.rootKey.length + 1 ≤ 2 ^ 63 := hr_lt63
    have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [stackAt_encoderFromPb_split_allocHook fsp]; wp_simp_pre [sepConj_assoc]
    have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
    have hshim := hA.shim_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
    have halloc := hA.alloc_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
    have hmc := hA.session_memcpy_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy")); simp only [sessionMemcpySpec] at hmc
    have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
      (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))) (by rw [hfn, stubOff_handle_error])
    states_from_pb_fetches_range b (Rust.withPanics ext) 200 48
    states_from_pb_fetches_range b (Rust.withPanics ext) 11584 12
    dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hshim halloc hmc hpanic hpc hnext ⊢
    clear hfn hA
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 220#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.rootKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      refine sepWPp_seq_clean (mid := entry + 5476#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗
          vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
          vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) (sf_1.readReg64 Reg.x0) auth.rootKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
          s1.readReg64 .x22 = ga.rootKey.cap ∧ s1.readReg64 .x24 = ga.rootKey.ptr ∧
          s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
          s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
          s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
          s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s1 s0)
        ?_ (hnext (sf_1.readReg64 Reg.x0))
      clear hnext; wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp]
        have hd := vecU8Payload_pos_dealloc A ga.rootKey.cap ga.rootKey.ptr auth.rootKey hr_le hr_cap hptr0 hcap0_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.rootKey hr_pos hr_lt63 hoom0
        have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
        rw [hsp_sf1]
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live ga.rootKey.ptr ga.rootKey.cap.toNat 1 ∗ (ga.rootKey.ptr ↦ₛ auth.rootKey) ∗
           memRegion (ga.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (ga.rootKey.cap.toNat - auth.rootKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.rootKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.rootKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
          ((fsp + 208#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

set_option maxHeartbeats 800000 in
theorem states_from_pb_keysUnsampled_step2_5476_5600
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext) (s0 s : State) (target_pc fsp out : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5476#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx22 : s.readReg64 .x22 = ga.rootKey.cap) (hx24 : s.readReg64 .x24 = ga.rootKey.ptr)
    (hx20 : s.readReg64 .x20 = ga.macKey.cap) (hx21 : s.readReg64 .x21 = ga.macKey.ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length) (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (s2 : State),
      s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5600#64 →
      s2.status = .Running →
      (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
       s2.readReg64 .x22 = ga.rootKey.cap ∧ s2.readReg64 .x24 = ga.rootKey.ptr ∧
       s2.readReg64 .x20 = ga.macKey.cap ∧ s2.readReg64 .x21 = ga.macKey.ptr ∧
       s2.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
       s2.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
       s2.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s2 s0) →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc s2
        (stackAt fsp encoderFromPbStack ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗
         vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s2.readReg64 .x25) auth.macKey ∗
         A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (stackAt fsp encoderFromPbStack ∗ vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hm_cases : auth.macKey = [] ∨ 0 < auth.macKey.length := by cases auth.macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · refine sepWPp_seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5600#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗
        vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) 1#64 auth.macKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s2 => s2.readReg64 .x25 = 1#64 ∧
        (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
         s2.readReg64 .x22 = ga.rootKey.cap ∧ s2.readReg64 .x24 = ga.rootKey.ptr ∧
         s2.readReg64 .x20 = ga.macKey.cap ∧ s2.readReg64 .x21 = ga.macKey.ptr ∧
         s2.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
         s2.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
         s2.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s2 s0))
      ?_ (fun s2 hpc2 hrun2 ⟨hx25, hregs⟩ => by rw [← hx25]; exact hnext s2 hpc2 hrun2 hregs)
    clear hnext; rw [hm_nil] at hx13 hx27 ⊢
    states_from_pb_fetches_range b (Rust.withPanics ext) 5476 4
    states_from_pb_fetches_range b (Rust.withPanics ext) 5596 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, List.length_nil, BitVec.ofNat_eq_ofNat] at hpc hx13 hx27 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A ga.macKey.cap ga.macKey.ptr []
      have hn := vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A ga.macKey.cap ga.macKey.ptr [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · refine SepWPp.weaken_pre (sepConj_mono_right
      (sepConj_mono_left (vecU8Payload_pos_unpack A ga.macKey.cap ga.macKey.ptr auth.macKey hm_pos))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗
          (⌜auth.macKey.length ≤ ga.macKey.cap.toNat ∧ ga.macKey.cap.toNat < 2 ^ 63 ∧
            ga.macKey.ptr ≠ 0#64 ∧ ga.macKey.cap ≠ 0#64⌝ ∗
           (A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ (ga.macKey.ptr ↦ₛ auth.macKey) ∗
            memRegion (ga.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (ga.macKey.cap.toNat - auth.macKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.macKey.length ≤ ga.macKey.cap.toNat ∧ ga.macKey.cap.toNat < 2 ^ 63 ∧
          ga.macKey.ptr ≠ 0#64 ∧ ga.macKey.cap ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗
         A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ (ga.macKey.ptr ↦ₛ auth.macKey) ∗
         memRegion (ga.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (ga.macKey.cap.toNat - auth.macKey.length) ∗
         A.pool ∗ Frame) by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hm_le, hm_cap, hptr1, hcap1_ne⟩ => ?_
    have hm_lt63 : auth.macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : auth.macKey.length < 2 ^ 64 := by omega
    have hm_toNat : (BitVec.ofNat 64 auth.macKey.length).toNat = auth.macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hm_ne0 : (BitVec.ofNat 64 auth.macKey.length == 0#64) = false := ofNat_beq_zero_false hm_pos hm_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hm_lay3 : auth.macKey.length + 1 ≤ 2 ^ 63 := hm_lt63
    have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [stackAt_encoderFromPb_split_allocHook fsp]; wp_simp_pre [sepConj_assoc]
    have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
    have hshim := hA.shim_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
    have halloc := hA.alloc_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
    have hmc := hA.session_memcpy_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy")); simp only [sessionMemcpySpec] at hmc
    have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
      (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))) (by rw [hfn, stubOff_handle_error])
    states_from_pb_fetches_range b (Rust.withPanics ext) 5476 60
    states_from_pb_fetches_range b (Rust.withPanics ext) 11584 12
    dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hshim halloc hmc hpanic hpc hnext ⊢
    clear hfn hA
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 5504#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.macKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      refine sepWPp_seq_clean (mid := entry + 5600#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗
          vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (sf_1.readReg64 Reg.x0) auth.macKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s2 => s2.readReg64 .x25 = sf_1.readReg64 Reg.x0 ∧
          (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
           s2.readReg64 .x22 = ga.rootKey.cap ∧ s2.readReg64 .x24 = ga.rootKey.ptr ∧
           s2.readReg64 .x20 = ga.macKey.cap ∧ s2.readReg64 .x21 = ga.macKey.ptr ∧
           s2.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
           s2.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
           s2.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s2 s0))
        ?_ (fun s2 hpc2 hrun2 ⟨hx25, hregs⟩ => by rw [← hx25]; exact hnext s2 hpc2 hrun2 hregs)
      clear hnext; wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp]
        have hd := vecU8Payload_pos_dealloc A ga.macKey.cap ga.macKey.ptr auth.macKey hm_le hm_cap hptr1 hcap1_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.macKey hm_pos hm_lt63 hoom1
        have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
        rw [hsp_sf1]
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ (ga.macKey.ptr ↦ₛ auth.macKey) ∗
           memRegion (ga.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (ga.macKey.cap.toNat - auth.macKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.macKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.macKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

set_option maxHeartbeats 800000 in
theorem states_from_pb_keysUnsampled_step3_5600_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext) (s0 s : State) (fsp out pbA ep pa1 : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator) (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (halign : (s0.sp &&& 15#64 == 0#64) = true) (hfsp : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5600#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx22 : s.readReg64 .x22 = ga.rootKey.cap) (hx24 : s.readReg64 .x24 = ga.rootKey.ptr)
    (hx20 : s.readReg64 .x20 = ga.macKey.cap) (hx21 : s.readReg64 .x21 = ga.macKey.ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ ep) ∗ memRegion (fsp + 160#64) 48 ∗
       ((fsp + 208#64) ↦₆₄ pa1) ∗ memRegion (fsp + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
       vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
       vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗
       vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := some { auth := some auth, epoch := ep } }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp ▸ sp_sub_2400_align s0.sp halign
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff stubOff_rust_dealloc (by decide)) hA.dealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
  have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
  have hcmn_false : (BitVec.ofNat 64 auth.rootKey.length + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false (by rw [hr_toNat]; exact hr_lt63))
  rw [stackAt_encoderFromPb_split_allocHook fsp]
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5624#64)
    (P_mid := memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
      memRegion out chunkedStatesSize ∗ memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ ep) ∗
      memRegion (fsp + 160#64) 48 ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗ memRegion (fsp + 216#64) 2088 ∗
      statesFromPbSavedCells s0 ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗
      vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
      vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
      memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
      s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
      s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
      s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
      s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s1 s0) ?_ ?_
  · clear hfsp; states_from_pb_fetches_range b (Rust.withPanics ext) 5600 24
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_cases hc1 : (ga.rootKey.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply; wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by rw [hsp]; ac_rfl)) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx23_1, hx20_1, hx21_1, hx25_1, hx26_1, hx13_1, hx27_1, htr1⟩
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5648#64)
      (P_mid := memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
        memRegion out chunkedStatesSize ∗ memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ ep) ∗
        memRegion (fsp + 160#64) 48 ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗ memRegion (fsp + 216#64) 2088 ∗
        statesFromPbSavedCells s0 ∗ vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
        vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
        s2.readReg64 .x25 = s.readReg64 .x25 ∧ s2.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s2 s0) ?_ ?_
    · clear hfsp; states_from_pb_fetches_range b (Rust.withPanics ext) 5624 24
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      by_cases hc2 : (ga.macKey.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply; wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by rw [hsp1]; ac_rfl)) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx25_2, hx26_2, hx13_2, htr2⟩
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8176#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
          memRegion fsp 208 ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗ memRegion (fsp + 216#64) 2088 ∗
          statesFromPbSavedCells s0 ∗
          (vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
           vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool))
        (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = out ∧ s3.readReg64 .x23 = fsp + 848#64 ∧
          s3.readReg64 .x8 = 2#64 ∧ s3.readReg64 .x15 = BitVec.ofNat 64 auth.rootKey.length ∧
          s3.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
          s3.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
          s3.readReg64 .x25 = s.readReg64 .x25 ∧ s3.readReg64 .x30 = BitVec.ofNat 64 auth.macKey.length ∧
          s3.readReg64 .x9 = ep ∧ TraceCalleeSaved s3 s0) ?_ ?_
      · clear hfsp; states_from_pb_fetches_range b (Rust.withPanics ext) 5648 32
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches; wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · rw [stackAt_encoderFromPb_split_allocHook fsp]
          have h208 := memRegion_152_8_48_entails_208 fsp ep
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ ep) ∗ memRegion (fsp + 160#64) 48) ∗
            memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
            memRegion out chunkedStatesSize ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗
            memRegion (fsp + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
            vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
            vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left h208) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx23_3, hx8_3, hx15_3, hx20_3, hx13_3, hx25_3, hx30_3, hx9_3, htr3⟩
        subst hfsp
        have hep := states_from_pb_epilogue_8176_keysUnsampled hA s0 s3 out pa1
          (vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
           vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
          halign hpc3 hrun3 hsp3 hx19_3 hx23_3 htr3
        rw [hx8_3, hx15_3, hx20_3, hx13_3, hx25_3, hx30_3, hx9_3] at hep
        refine SepWP.mono hep fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
          ⟨Entails.trans hPf ?_, hsp_f, hcc_f, htr_f⟩
        rw [states_from_pb_keysUnsampled_some_eq]
        dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedKeysUnsampledAt,
          unchunkedKeysUnsampledAt, Authenticator.fromPb]
        have hauth := authenticatorAt_8_pack A out
          (BitVec.ofNat 64 auth.rootKey.length) pa1
          (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25)
          { rootKey := auth.rootKey, macKey := auth.macKey }
        dsimp only at hauth
        have h56 : (out + 8#64) + 48#64 = out + 56#64 := by bv_omega
        rw [h56]
        refine Entails.trans (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ ((out + 16#64) ↦₆₄ pa1) ∗
           ((out + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ ((out + 32#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
           ((out + 40#64) ↦₆₄ s.readReg64 .x25) ∗ ((out + 48#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
           vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
           vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey) ∗
          (out ↦₆₄ 2#64) ∗ ((out + 56#64) ↦₆₄ ep) ∗ memRegion (out + 64#64) 864 ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hauth) (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 800000 in
theorem states_from_pb_keysUnsampled_some
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext) (s0 s1 : State) (out pbA ep : BitVec 64)
    (auth : ProtoAuthenticator) (R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 156#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000000#64) ∗ optProtoAuthenticatorAt A (pbA + 8#64) (some auth) ∗
        ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗
        statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := some { auth := some auth, epoch := ep } }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  rw [show optProtoAuthenticatorAt A (pbA + 8#64) (some auth) =
    ∃∗ ga : AuthenticatorPBGhost, authenticatorPBPinnedAt A ga (pbA + 8#64) auth from
    authenticatorPBAt_eq_exists_pinned A (pbA + 8#64) auth]
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (memRegion_2304_split_152_208 (s0.sp - 2400#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ga => SepWPp.exists_elim fun w208 => SepWPp.exists_elim fun w152 => ?_
  have hcap_ext : authenticatorPBPinnedAt A ga (pbA + 8#64) auth ⊢
      ⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗ authenticatorPBPinnedAt A ga (pbA + 8#64) auth := by
    rw [authenticatorPBPinnedAt_8_eq_cap_tail]
    have h1 : vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ⊢
        ⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗ vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey := by
      unfold vecU8Payload; apply Entails.pure_left; intro ⟨hle, hlt, hne⟩
      exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))
    exact Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h1))))
      (Entails.of_eq (by ac_rfl))
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 152 ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000000#64) ∗
        authenticatorPBPinnedAt A ga (pbA + 8#64) auth ∗
        ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗ statesFromPbJumpTableAt b ∗ A.pool =
      authenticatorPBPinnedAt A ga (pbA + 8#64) auth ∗
      ((pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗
       ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
       (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
        memRegion (s0.sp - 2400#64) 152 ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
        statesFromPbSavedCells s0 ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl))
    (Entails.trans (sepConj_mono_left hcap_ext) (Entails.of_eq (show _ =
      ⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗
      ((pbA ↦₆₄ 0x8000000000000000#64) ∗ authenticatorPBPinnedAt A ga (pbA + 8#64) auth ∗
       ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
       (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
        memRegion (s0.sp - 2400#64) 152 ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
        statesFromPbSavedCells s0 ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl)))) ?_
  refine SepWPp.pure_elim fun hcap0 => ?_
  refine sepWPp_seq_clean
    (states_from_pb_keysUnsampled_step0_156_200 s1 (s0.sp - 2400#64) out pbA ep w152 ga auth
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion (s0.sp - 2400#64) 152 ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
       ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
       statesFromPbSavedCells s0 ∗ statesFromPbJumpTableAt b ∗ A.pool)
      hcap0 hfsp_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx22_2, hx24_2, hx20_2, hx21_2, hx26_2, hx13_2, hx27_2, htr2⟩
  have htr2 := htr2.trans htr1
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (vecU8Payload_extract_len_lt63 A ga.rootKey.cap ga.rootKey.ptr auth.rootKey))) ?_
  rw [show ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗
        (⌜auth.rootKey.length < 2 ^ 63⌝ ∗ vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey) ∗
        vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ memRegion pbA optProtoInnerStateSize ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
         memRegion (s0.sp - 2400#64) 152 ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
         ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
         statesFromPbSavedCells s0 ∗ statesFromPbJumpTableAt b ∗ A.pool) =
      ⌜auth.rootKey.length < 2 ^ 63⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗
       vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗ A.pool ∗
       (vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗
        memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 152 ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)) by ac_rfl]
  refine SepWPp.pure_elim fun hr_lt63 => ?_
  refine states_from_pb_keysUnsampled_step1_200_5476 hA s0 s2 (s0.readReg64 .x30)
    (s0.sp - 2400#64) out w208 ga auth
    (vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗
     memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 152 ∗
     ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
     memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) R _
    hfsp_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx22_2 hx24_2 hx20_2 hx21_2 hx26_2 hx13_2 hx27_2 htr2 ?_
  intro pa1 s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx23_3, hx22_3, hx24_3, hx20_3, hx21_3, hx26_3, hx13_3, hx27_3, htr3⟩
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ A.pool ∗
    (memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 152 ∗
     ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
     ((s0.sp - 2400#64 + 208#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
     statesFromPbSavedCells s0 ∗ vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
     vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
  refine states_from_pb_keysUnsampled_step2_5476_5600 hA s0 s3 (s0.readReg64 .x30)
    (s0.sp - 2400#64) out ga auth
    (memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 152 ∗
     ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
     ((s0.sp - 2400#64 + 208#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
     statesFromPbSavedCells s0 ∗ vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
     vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) R _
    hfsp_align hpc3 hrun3 hsp3 hx19_3 hx23_3 hx22_3 hx24_3 hx20_3 hx21_3 hx26_3 hx13_3 hx27_3 htr3 ?_
  intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx23_4, hx22_4, hx24_4, hx20_4, hx21_4, hx26_4, hx13_4, hx27_4, htr4⟩
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
    memRegion (s0.sp - 2400#64) 152 ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗
    memRegion (s0.sp - 2400#64 + 160#64) 48 ∗ ((s0.sp - 2400#64 + 208#64) ↦₆₄ pa1) ∗
    memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
    vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗
    vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
    vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s4.readReg64 .x25) auth.macKey ∗
    memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool by ac_rfl)) ?_
  exact SepWPp.of_sepWP_ret (states_from_pb_keysUnsampled_step3_5600_ret hA s0 s4
    (s0.sp - 2400#64) out pbA ep pa1 ga auth hr_lt63 hsp0_align rfl
    hpc4 hrun4 hsp4 hx19_4 hx23_4 hx22_4 hx24_4 hx20_4 hx21_4 hx26_4 hx13_4 hx27_4 htr4)

theorem states_from_pb_keysUnsampled_156_sfa
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext) (s0 s1 : State) (out pbA : BitVec 64)
    (s : V1State.Chunked.KeysUnsampled) (R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 156#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    StatesFromPbKeysUnsampled156Goal A F b ext s0 s1 out pbA s R := by
  cases s with | mk uc =>
  cases uc with
  | none =>
    dsimp only [StatesFromPbKeysUnsampled156Goal, optProtoInnerStateAt, protoInnerStateAt, protoChunkedKeysUnsampledAt, optProtoUnchunkedKeysUnsampledAt]
    have h16 : (pbA + 8#64) + 8#64 = pbA + 16#64 := by bv_omega
    rw [h16]; simp only [sepConj_assoc]
    exact SepWPp.of_sepWP_ret (states_from_pb_keysUnsampled_uc_none s0 s1 out pbA hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
  | some uc =>
    cases uc with | mk ep auth =>
    cases auth with
    | none =>
      dsimp only [StatesFromPbKeysUnsampled156Goal, optProtoInnerStateAt, protoInnerStateAt, protoChunkedKeysUnsampledAt,
        optProtoUnchunkedKeysUnsampledAt, protoUnchunkedKeysUnsampledAt, optProtoAuthenticatorAt]
      have h16 : (pbA + 8#64) + 8#64 = pbA + 16#64 := by bv_omega
      have h56 : (pbA + 8#64) + 48#64 = pbA + 56#64 := by bv_omega
      rw [h16, h56]; simp only [sepConj_assoc]
      exact SepWPp.of_sepWP_ret (states_from_pb_keysUnsampled_auth_none s0 s1 out pbA ep hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
    | some auth =>
      dsimp only [StatesFromPbKeysUnsampled156Goal]
      rw [optProtoInnerStateAt_keysUnsampled_some_eq]; simp only [sepConj_assoc]
      exact states_from_pb_keysUnsampled_some hA s0 s1 out pbA ep auth R hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1

theorem states_from_pb_keysUnsampled_156 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) (s0 s1 : State) (out pbA : BitVec 64)
    (s : V1State.Chunked.KeysUnsampled) (R : SepProp) (ha : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 156#64) (hr : s1.status = .Running)
    (hsp : s1.sp = s0.sp - 2400#64) (hx19 : s1.readReg64 .x19 = out) (hx23 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27 : s1.readReg64 .x27 = pbA) (htr : TraceCalleeSaved s1 s0) : StatesFromPbKeysUnsampled156Goal A F b ext s0 s1 out pbA s R :=
  states_from_pb_keysUnsampled_156_sfa (.of_allocContracts hA) s0 s1 out pbA s R ha hpc hr hsp hx19 hx23 hx27 htr

end CryptoVerification.SpqrV1.States.FromPb
