/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Phase 2d Common Infrastructure (`0x6d6dc .. 0x6e660`): `V1State` Encoding Helpers

Defines exact-capacity callee specifications (`etvPolyEncoderExactSpecOf`, `etvPolyDecoderExactSpecOf`,
`etvEkSentCt1ReceivedEncodeSpecOf`, `etvCt1SentEncodeSpecOf`), relative callee address equations,
`SepWPp.call_cs` wrappers at `s.sp = sp - 144#64`, and the unpacked 22-byte `.rodata` jump-table
representation at `b + 0xa1480#64`.
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

@[simp, arm64_norm] theorem noneCap2_add_two_beq_zero :
    (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := by decide

@[simp, arm64_norm] theorem noneCap2_add_two_bne_zero :
    (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := by decide

@[simp, arm64_norm] theorem noneCap_add_two_beq_zero :
    (0xffffffffffffffff#64 + 2#64 == 0#64) = false := by decide

@[simp, arm64_norm] theorem noneCap_add_two_bne_zero :
    (0xffffffffffffffff#64 + 2#64 != 0#64) = true := by decide

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Stack Split & Symbol Name Helpers for `V1State` Callees -/

abbrev etvPolyEncoder2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"

abbrev etvPolyDecoder2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#2]"

abbrev etvEkSentCt1ReceivedEncode2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#2]"

abbrev etvCt1SentEncode2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]"

theorem stackAt_callee_eq_chunkedEncodedLen {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (128 + resStack) ∗
        stackAt sp1 chunkedEncodedLenStack := by
  have h48 : chunkedEncodedLenStack = 48 := rfl
  have h := ProofLib.stackAt_split_bottom sp1 chunkedEncodedLenStack (128 + resStack)
    (by rw [h48]; omega)
  have heq : chunkedEncodedLenStack + (128 + resStack) = encodeToVecCalleeStackOf resStack := by
    rw [h48]; dsimp [encodeToVecCalleeStackOf]; omega
  simpa only [heq] using h

/-! ## 2. Callee Address Equations for `V1State` Phase (`0x6d6dc .. 0x6e660`) -/

theorem encodeToVec_v1StateEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709530600#64 =
      (spqrProgAtExt b ext).fnAddr v1StateEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x62a00]
  bv_omega

theorem encodeToVec_polyEncoderEncode2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442756#64 =
      (spqrProgAtExt b ext).fnAddr etvPolyEncoder2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x4d2dc]
  bv_omega

theorem encodeToVec_polyDecoderEncode2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442356#64 =
      (spqrProgAtExt b ext).fnAddr etvPolyDecoder2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x4d14c]
  bv_omega

theorem encodeToVec_ekSentCt1ReceivedEncode2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709443724#64 =
      (spqrProgAtExt b ext).fnAddr etvEkSentCt1ReceivedEncode2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x4d6a4]
  bv_omega

theorem encodeToVec_ct1SentEncode2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709444388#64 =
      (spqrProgAtExt b ext).fnAddr etvCt1SentEncode2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x4d93c]
  bv_omega

theorem encodeToVec_keysUnsampledEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709524916#64 =
      (spqrProgAtExt b ext).fnAddr keysUnsampledEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x613cc]
  bv_omega

theorem encodeToVec_headerSentEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709535892#64 =
      (spqrProgAtExt b ext).fnAddr headerSentEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x63eac]
  bv_omega

theorem encodeToVec_chunkedHeaderSentEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709539168#64 =
      (spqrProgAtExt b ext).fnAddr chunkedHeaderSentEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x64b78]
  bv_omega

theorem encodeToVec_ekSentEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709539708#64 =
      (spqrProgAtExt b ext).fnAddr ekSentEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x64d94]
  bv_omega

theorem encodeToVec_ekSentCt1ReceivedEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709549660#64 =
      (spqrProgAtExt b ext).fnAddr ekSentCt1ReceivedEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x67474]
  bv_omega

theorem encodeToVec_ct1SentEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709534512#64 =
      (spqrProgAtExt b ext).fnAddr ct1SentEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x63948]
  bv_omega

theorem encodeToVec_noHeaderReceivedEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709550932#64 =
      (spqrProgAtExt b ext).fnAddr noHeaderReceivedEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x6796c]
  bv_omega

theorem encodeToVec_headerReceivedEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709529772#64 =
      (spqrProgAtExt b ext).fnAddr headerReceivedEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x626c4]
  bv_omega

theorem encodeToVec_chunkedCt1SampledEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709534032#64 =
      (spqrProgAtExt b ext).fnAddr chunkedCt1SampledEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x63768]
  bv_omega

theorem encodeToVec_ct1SentEkReceivedEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709515116#64 =
      (spqrProgAtExt b ext).fnAddr ct1SentEkReceivedEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x5ed84]
  bv_omega

theorem encodeToVec_ct2SentEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709516504#64 =
      (spqrProgAtExt b ext).fnAddr ct2SentEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x5f2f0]
  bv_omega

theorem encodeToVec_polyDecoderEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709536996#64 =
      (spqrProgAtExt b ext).fnAddr ProtoRepr.polynomialDecoderEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x642fc]
  bv_omega

theorem encodeToVec_polyEncoderEncodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709525468#64 =
      (spqrProgAtExt b ext).fnAddr ProtoRepr.polynomialEncoderEncodedLenLocal2Name := by
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff,
    libsignalSessionCode_fnOff_0x615f4]
  bv_omega

/-! ## 3. Callee `SepWPp.call_cs` Wrappers at `s.sp = sp - 144#64` -/

theorem step_etv_v1State_encLen_call {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hv1Len : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))))
    (v1A sp ret_pc : BitVec 64) (g : V1StatePBGhost) (v1 : V1State)
    (hfit : v1StatePBEncodedLen v1 < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v1A)
    (hinv0 : StepInv s0 s)
    (hP : P = (v1StatePBPinnedAt A g v1A v1 ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen v1) →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((v1StatePBPinnedAt A g v1A v1 ∗
          ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  let F_rem := memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (96 + resStack)
  refine SepWPp.call_cs (x := ⟨v1A, g, v1⟩) (F := F_rem ∗ F)
    hv1Len hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_callee_eq_v1StateEncodedLen (by omega) (sp - 144#64)] at hm
    simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact False.elim hm.1
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, v1StateEncodedLenRoPinnedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm (hinv0.trans hinv_call))
    rw [stackAt_callee_eq_v1StateEncodedLen (by omega) (sp - 144#64)]
    exact Entails.of_eq (by dsimp [F_rem]; ac_rfl)

/-- Generic 16-byte stack `encoded_len` specification shape (`unchunkedEncodedLenStack = polyEncodedLenStack = 16`). -/
def leafEncLen16Spec {G M : Type} (reprAt : G → BitVec 64 → M → SepProp)
    (encLen : M → Nat) : Spec (PinnedEncLenGhost G M) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ encLen x.m < 2 ^ 64⌝ ∗
      reprAt x.g x.a x.m ∗ stackAt s.sp unchunkedEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      reprAt x.g x.a x.m ∗ stackAt s0.sp unchunkedEncodedLenStack

theorem step_etv_leaf_encLen16_call {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {G M : Type} (b : BitVec 64) (ext : String → Option (State → State))
    (reprAt : G → BitVec 64 → M → SepProp) (encLen : M → Nat)
    {call_pc : BitVec 64} {s0 s : State}
    (hcallee : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (leafEncLen16Spec reprAt encLen)))
    (msgA sp ret_pc : BitVec 64) (g : G) (m : M)
    (hfit : encLen m < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA)
    (hinv0 : StepInv s0 s)
    (hP : P = (reprAt g msgA m ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encLen m) →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((reprAt g msgA m ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  let F_rem := memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (160 + resStack)
  refine SepWPp.call_cs (x := ⟨msgA, g, m⟩) (F := F_rem ∗ F)
    hcallee hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_callee_eq_unchunkedEncodedLen (by omega) (sp - 144#64)] at hm
    simp only [withStepInv, leafEncLen16Spec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, leafEncLen16Spec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact False.elim hm.1
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, leafEncLen16Spec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm (hinv0.trans hinv_call))
    rw [stackAt_callee_eq_unchunkedEncodedLen (by omega) (sp - 144#64)]
    exact Entails.of_eq (by dsimp [F_rem]; ac_rfl)

/-- Generic 48-byte stack `encoded_len` specification shape (`chunkedEncodedLenStack = 48`). -/
def leafEncLen48Spec {G M : Type} (reprAt : G → BitVec 64 → M → SepProp)
    (encLen : M → Nat) : Spec (PinnedEncLenGhost G M) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ encLen x.m < 2 ^ 64⌝ ∗
      reprAt x.g x.a x.m ∗ stackAt s.sp chunkedEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      reprAt x.g x.a x.m ∗ stackAt s0.sp chunkedEncodedLenStack

theorem step_etv_chunked_encLen48_call {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {G M : Type} (b : BitVec 64) (ext : String → Option (State → State))
    (reprAt : G → BitVec 64 → M → SepProp) (encLen : M → Nat)
    {call_pc : BitVec 64} {s0 s : State}
    (hcallee : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (leafEncLen48Spec reprAt encLen)))
    (msgA sp ret_pc : BitVec 64) (g : G) (m : M)
    (hfit : encLen m < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA)
    (hinv0 : StepInv s0 s)
    (hP : P = (reprAt g msgA m ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encLen m) →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((reprAt g msgA m ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  let F_rem := memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (128 + resStack)
  refine SepWPp.call_cs (x := ⟨msgA, g, m⟩) (F := F_rem ∗ F)
    hcallee hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_callee_eq_chunkedEncodedLen (by omega) (sp - 144#64)] at hm
    simp only [withStepInv, leafEncLen48Spec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, leafEncLen48Spec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact False.elim hm.1
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, leafEncLen48Spec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm (hinv0.trans hinv_call))
    rw [stackAt_callee_eq_chunkedEncodedLen (by omega) (sp - 144#64)]
    exact Entails.of_eq (by dsimp [F_rem]; ac_rfl)

structure EtvPolyEncoderGhost where
  encA : BitVec 64
  g : PolynomialEncoderPBGhost
  enc : PolynomialEncoder
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Exact-capacity specification for `encode<PolynomialEncoder> [local#2]` (`0x526d4`). -/
def etvPolyEncoderExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EtvPolyEncoderGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 x.enc).length ≤ x.cap.toNat⌝ ∗
      ProtoRepr.polynomialEncoderPBPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ProtoRepr.polynomialEncoderPBPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 x.enc) ∗
      A.pool ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

structure EtvPolyDecoderGhost where
  tag : BitVec 32
  decA : BitVec 64
  g : PolynomialDecoderPBGhost
  dec : PolynomialDecoder
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Exact-capacity specification for `encode<PolynomialDecoder> [local#2]` (`0x52544`). -/
def etvPolyDecoderExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EtvPolyDecoderGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw x.tag x.dec).length ≤ x.cap.toNat⌝ ∗
      ProtoRepr.polynomialDecoderPBPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ProtoRepr.polynomialDecoderPBPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw x.tag x.dec) ∗
      A.pool ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

structure EtvUnchunkedMsgEncodeGhost (G M : Type) where
  msgA : BitVec 64
  g : G
  m : M
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

def etvEkSentCt1ReceivedEncodeSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec (EtvUnchunkedMsgEncodeGhost Unchunked4PBGhost V1State.Unchunked.EkSentCt1Received) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length +
        (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m).length ≤ x.cap.toNat ∨
       x.bs.length +
        (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m).length + 10 < 2 ^ 62)⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A x.g x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length +
            (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A x.v cap' ptr'
          (x.bs ++ Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m)) ∗
      A.pool ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

def etvCt1SentEncodeSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec (EtvUnchunkedMsgEncodeGhost Unchunked5PBGhost V1State.Unchunked.Ct1Sent) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length +
        (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m).length ≤ x.cap.toNat ∨
       x.bs.length +
        (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m).length + 10 < 2 ^ 62)⌝ ∗
      ct1SentPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentPBPinnedAt A x.g x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length +
            (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A x.v cap' ptr'
          (x.bs ++ Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m)) ∗
      A.pool ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

theorem step_etv_encode_polyEncoder_call {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hpe : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (encA v cap ptr sp ret_pc : BitVec 64)
    (g : PolynomialEncoderPBGhost) (enc : PolynomialEncoder) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = encA)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (ProtoRepr.polynomialEncoderPBPinnedAt A g encA enc ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((ProtoRepr.polynomialEncoderPBPinnedAt A g encA enc ∗
          vecU8At A v cap ptr (bs ++ Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs
    (x := { encA := encA, g := g, enc := enc, v := v, cap := cap, ptr := ptr, bs := bs })
    (F := F) hpe hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvPolyEncoderExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, etvPolyEncoderExactSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvPolyEncoderExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem step_etv_encode_polyDecoder_call {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hpd : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (tag : BitVec 32) (decA v cap ptr sp ret_pc : BitVec 64)
    (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw tag dec).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = decA)
    (hx2 : s.readReg64 .x2 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (ProtoRepr.polynomialDecoderPBPinnedAt A g decA dec ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((ProtoRepr.polynomialDecoderPBPinnedAt A g decA dec ∗
          vecU8At A v cap ptr (bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw tag dec) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs
    (x := { tag := tag, decA := decA, g := g, dec := dec, v := v, cap := cap, ptr := ptr, bs := bs })
    (F := F) hpd hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvPolyDecoderExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hx1, hx2, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, etvPolyDecoderExactSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvPolyDecoderExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem step_etv_encode_ekSentCt1Received_call {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hek : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (msgA v cap ptr sp ret_pc : BitVec 64)
    (g : Unchunked4PBGhost) (m : V1State.Unchunked.EkSentCt1Received) (bs : List (BitVec 8))
    (hfit : bs.length +
      (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
          vecU8At A v cap ptr
            (bs ++ Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs
    (x := { msgA := msgA, g := g, m := m, v := v, cap := cap, ptr := ptr, bs := bs })
    (F := F) hek hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvEkSentCt1ReceivedEncodeSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, Or.inl hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, etvEkSentCt1ReceivedEncodeSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvEkSentCt1ReceivedEncodeSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.weaken_pre
      (P' := ⌜cap.toNat ≤ cap'.toNat ∧
        (bs.length + (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m).length ≤ cap.toNat →
          cap' = cap ∧ ptr' = ptr)⌝ ∗
        ((ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
          vecU8At A v cap' ptr'
            (bs ++ Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨_, hpres⟩ => ?_
    obtain ⟨rfl, rfl⟩ := hpres hfit
    exact hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call)

theorem step_etv_encode_ct1Sent_call {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hct1 : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (msgA v cap ptr sp ret_pc : BitVec 64)
    (g : Unchunked5PBGhost) (m : V1State.Unchunked.Ct1Sent) (bs : List (BitVec 8))
    (hfit : bs.length +
      (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (ct1SentPBPinnedAt A g msgA m ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((ct1SentPBPinnedAt A g msgA m ∗
          vecU8At A v cap ptr
            (bs ++ Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs
    (x := { msgA := msgA, g := g, m := m, v := v, cap := cap, ptr := ptr, bs := bs })
    (F := F) hct1 hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvCt1SentEncodeSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, Or.inl hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, etvCt1SentEncodeSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvCt1SentEncodeSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.weaken_pre
      (P' := ⌜cap.toNat ≤ cap'.toNat ∧
        (bs.length + (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m).length ≤ cap.toNat →
          cap' = cap ∧ ptr' = ptr)⌝ ∗
        ((ct1SentPBPinnedAt A g msgA m ∗
          vecU8At A v cap' ptr'
            (bs ++ Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨_, hpres⟩ => ?_
    obtain ⟨rfl, rfl⟩ := hpres hfit
    exact hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call)

/-! ## 4. `.rodata` Jump Table at `b + 0xa1480#64` and Option Cap Bound Wrappers -/

/-- Unpacked 22-byte (`11 × u16`) `.rodata` jump table at `roBase` (`b + 0xa1480#64`) as 22 `↦₈ᵣ` atoms. -/
def encodeToVecJumpTableBytes8At (roBase : BitVec 64) : SepProp :=
  (roBase ↦₈ᵣ 0x00#8) ∗ ((roBase + 1#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 2#64) ↦₈ᵣ 0xd5#8) ∗ ((roBase + 3#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 4#64) ↦₈ᵣ 0x46#8) ∗ ((roBase + 5#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 6#64) ↦₈ᵣ 0x9c#8) ∗ ((roBase + 7#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 8#64) ↦₈ᵣ 0x14#8) ∗ ((roBase + 9#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 10#64) ↦₈ᵣ 0xee#8) ∗ ((roBase + 11#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 12#64) ↦₈ᵣ 0xfd#8) ∗ ((roBase + 13#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 14#64) ↦₈ᵣ 0xb5#8) ∗ ((roBase + 15#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 16#64) ↦₈ᵣ 0x25#8) ∗ ((roBase + 17#64) ↦₈ᵣ 0x01#8) ∗
  ((roBase + 18#64) ↦₈ᵣ 0x2d#8) ∗ ((roBase + 19#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 20#64) ↦₈ᵣ 0x16#8) ∗ ((roBase + 21#64) ↦₈ᵣ 0x01#8)

theorem encodeToVecJumpTableBytes_eq8 (roBase : BitVec 64) :
    (roBase ↦ᵣ encodeToVecJumpTableBytes) = encodeToVecJumpTableBytes8At roBase := by
  unfold encodeToVecJumpTableBytes encodeToVecJumpTableBytes8At
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

end CryptoVerification.SpqrV1.Prost.EncodeToVec
