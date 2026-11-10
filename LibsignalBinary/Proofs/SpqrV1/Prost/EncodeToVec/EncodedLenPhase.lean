/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import ProofLib.SepLogic.WPp

/-!
# `PqRatchetState::encode_to_vec`: `encoded_len` Phase (`0x6d010..0x6d214`)

Verifies Phase 1 (`+0..+516`) of `PqRatchetState::encode_to_vec`, combining the prologue and
`Option<VersionNegotiation>`, `Option<Chain>`, and `Option<pq_ratchet_state::Inner>` encoded-length
computations to produce `x23 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)`.
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
  (ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_u32VarintField_nonzero bv_bytesField_nonempty
   bv_add_ofNat_comm bv_add_ofNat_eq adds_no_overflow_of_eq cmp_ls_false_of_lt)

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
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-- Panic postcondition `⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap`. -/
def encodeToVecOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Step 1b: `Option<Chain>::encoded_len` (`+380/+428 .. +436`, `0x6d18c/0x6d1bc .. 0x6d1c4`) -/

theorem step_encodeToVec_chain_len {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s1 : State}
    (hChainLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr chainEncodedLenLocal2Name)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (sret a sp v0 v1 v2 v3 v4 v5 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s1.pc = (if st.chain.isSome then entry + 380#64 else entry + 428#64))
    (hrun : s1.status = .Running) (hsp : s1.sp = sp - 144#64) (htr : s1.trace = s0.trace)
    (hx8_none : st.chain = none → s1.readReg64 .x8 = 0#64)
    (hx19 : s1.readReg64 .x19 = optChainCap g.chain st.chain) (hx20 : s1.readReg64 .x20 = a)
    (hx21 : s1.readReg64 .x21 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation))
    (hx22 : s1.readReg64 .x22 = a + 48#64)
    (hx25 : s1.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation)
    (hx27 : s1.readReg64 .x27 = sret) (hfp : s1.readReg64 .fp = sp - 96#64)
    (hinv1 : StepInv s0 s1)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
      encodeToVecSavedRegs sp s0) ∗ F)
    (hnext : ∀ s2 : State,
      s2.pc = entry + 436#64 → s2.status = .Running → s2.sp = sp - 144#64 →
      s2.trace = s0.trace → s2.readReg64 .x19 = optChainCap g.chain st.chain →
      s2.readReg64 .x20 = a → s2.readReg64 .x22 = a + 48#64 →
      s2.readReg64 .x23 =
        BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
          optChainPBFieldEncodedLen st.chain) →
      s2.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation →
      s2.readReg64 .x27 = sret → s2.readReg64 .fp = sp - 96#64 → StepInv s0 s2 →
      SepWPp (spqrProgAtExt b ext) ret s2
        ((pqRatchetStatePBPinnedAt A g a st ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
          encodeToVecSavedRegs sp s0) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s1 P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 380 436
  have hbl := encodeToVec_chainEncodedLen_fnAddr_eq b ext hfn
  examples_hide_fetches; subst hP
  cases hch : st.chain with
  | none =>
    rw [hch] at hpc
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    have hx8 := hx8_none hch
    have ⟨hadd1, hadd2⟩ := EncodedLen.adds_no_overflow_of_eq (a := 0)
      (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)
      (c := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen none)
      (by dsimp [optChainPBFieldEncodedLen])
      (by unfold pqRatchetStatePBEncodedLen at hlen; dsimp [optChainPBFieldEncodedLen]; omega)
    apply SepWPp.of_sepWP_cs (mid := entry + 436#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by rw [hch]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv1.trans hinv)
  | some ch =>
    rw [hch] at hpc
    simp only [Option.isSome_some, ↓reduceIte] at hpc
    have ⟨hfit, hopt_lt, hvar_lt⟩ := chainPBEncodedLen_lt_of_state hch hlen
    have hls := EncodedLen.cmp_ls_false_of_lt hvar_lt hopt_lt
    have hopt_ch := bv_optChain_some_eq ch
    have ⟨hadd1, hadd2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optChainPBFieldEncodedLen (some ch))
      (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)
      (c := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen (some ch))
      rfl
      (by unfold pqRatchetStatePBEncodedLen at hlen; rw [hch] at hlen; omega)
    apply SepWPp.of_sepWP_cs (mid := (spqrProgAtExt b ext).fnAddr chainEncodedLenLocal2Name)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_bl
    refine SepWPp.call_cs (x := ChainEncodedLenPinnedGhost.mk (a + 0x30#64) g.chain ch)
      (F := optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
        optPqRatchetInnerPBPinnedAt A g.inner (a + 0x80#64) st.inner ∗
        memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (80 + resStack) ∗
        encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
        encodeToVecSavedRegs sp s0 ∗ F)
      hChainLen (by simp only [arm64_norm, hbl]) (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]
          exact halign)
      (ret_pc := entry + 388#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
    · intro R' hm
      rw [pqRatchetStatePBPinnedAt, hch, optChainPBPinnedAt,
        stackAt_callee_eq_chainEncodedLen (by omega) (sp - 144#64)] at hm
      simp only [arm64_norm] at hm
      simp only [withStepInv, chainEncodedLenPinnedSpec, arm64_norm, hsp,
        sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hinv1.trans hinv_bl, hfit⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
    · intro sf code R' _ hm
      exact allowPanic_not_exited hm
    · intro sf _ hm
      simp only [withStepInv, chainEncodedLenPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    · intro sm hpcm hrunm hspm hcsm hinv_call
      simp only [arm64_norm, hsp] at hspm
      dsimp only [withStepInv, chainEncodedLenPinnedSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
      simp only [arm64_norm, htr] at htrm
      have hx19m : sm.readReg64 .x19 = optChainCap g.chain st.chain :=
        hcsm.1.trans (by simpa only [arm64_norm] using hx19)
      have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simpa only [arm64_norm] using hx20)
      have hx21m : sm.readReg64 .x21 =
          BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation) :=
        hcsm.2.2.1.trans (by simpa only [arm64_norm] using hx21)
      have hx22m : sm.readReg64 .x22 = a + 48#64 := hcsm.2.2.2.1.trans (by simpa only [arm64_norm] using hx22)
      have hx25m : sm.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation :=
        hcsm.2.2.2.2.2.2.1.trans (by simpa only [arm64_norm] using hx25)
      have hx27m : sm.readReg64 .x27 = sret :=
        hcsm.2.2.2.2.2.2.2.2.1.trans (by simpa only [arm64_norm] using hx27)
      have hfpm : sm.readReg64 .fp = sp - 96#64 :=
        hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simpa only [arm64_norm] using hfp)
      apply SepWPp.of_sepWP_cs (mid := entry + 436#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_post
      refine SepWPp.weaken_pre ?_
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hch]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (((hinv1.trans hinv_bl).trans hinv_call).trans hinv_post))
      rw [pqRatchetStatePBPinnedAt, hch, optChainPBPinnedAt,
        stackAt_callee_eq_chainEncodedLen (by omega) (sp - 144#64)]
      simp only [arm64_norm, hsp]
      exact Entails.of_eq (by ac_rfl)

/-! ## Step 1c: `Option<pq_ratchet_state::Inner>::encoded_len` (`+436 .. +516`, `0x6d1c4 .. 0x6d214`) -/

theorem step_encodeToVec_inner_len {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s2 : State}
    (hV1StateLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr v1StateEncodedLenLocal2Name)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))))
    (sret a sp v0 v1 v2 v3 v4 v5 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s2.pc = entry + 436#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp - 144#64) (htr : s2.trace = s0.trace)
    (hx19 : s2.readReg64 .x19 = optChainCap g.chain st.chain) (hx20 : s2.readReg64 .x20 = a)
    (hx22 : s2.readReg64 .x22 = a + 48#64)
    (hx23 : s2.readReg64 .x23 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen st.chain))
    (hx25 : s2.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation)
    (hx27 : s2.readReg64 .x27 = sret) (hfp : s2.readReg64 .fp = sp - 96#64)
    (hinv2 : StepInv s0 s2)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
      encodeToVecSavedRegs sp s0) ∗ F)
    (hnext : ∀ s3 : State,
      s3.pc = entry + 516#64 → s3.status = .Running → s3.sp = sp - 144#64 →
      s3.trace = s0.trace → s3.readReg64 .x19 = optChainCap g.chain st.chain →
      s3.readReg64 .x20 = a → s3.readReg64 .x21 = a + 128#64 →
      s3.readReg64 .x22 = a + 48#64 →
      s3.readReg64 .x23 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      s3.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation →
      s3.readReg64 .x27 = sret → s3.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner →
      s3.readReg64 .fp = sp - 96#64 → StepInv s0 s3 →
      SepWPp (spqrProgAtExt b ext) ret s3
        ((pqRatchetStatePBPinnedAt A g a st ∗
          ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
          encodeToVecSavedRegs sp s0) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s2 P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 436 516
  have hbl := encodeToVec_v1StateEncodedLen_fnAddr_eq b ext hfn
  examples_hide_fetches; subst hP
  refine sepWPp_extract_pure
    ((optPqRatchetInnerCap g.inner st.inner + 3#64 == 0#64) = !st.inner.isSome ∧
     (optPqRatchetInnerCap g.inner st.inner + 3#64 != 0#64) = st.inner.isSome)
    (fun R' hm => ?_) (fun hin_cap => ?_)
  · apply optPqRatchetInnerPBPinnedAt_cap_bounds (A := A) (p := a + 0x80#64)
      (R := optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
        optChainPBPinnedAt A g.chain (a + 0x30#64) st.chain ∗
        ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
        encodeToVecSavedRegs sp s0 ∗ F ∗ R')
    rw [pqRatchetStatePBPinnedAt] at hm
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq]
    cases hin : st.inner with
    | none =>
      rw [hin] at hin_cap
      simp only [Option.isSome_none, Bool.not_false] at hin_cap
      have ⟨hadd1, hadd2⟩ := EncodedLen.adds_no_overflow_of_eq (a := 0)
        (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
          optChainPBFieldEncodedLen st.chain)
        (c := pqRatchetStatePBEncodedLen st)
        (by unfold pqRatchetStatePBEncodedLen; rw [hin]; dsimp [optPqRatchetInnerPBFieldEncodedLen])
        (by omega)
      apply SepWPp.of_sepWP_cs (mid := entry + 516#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre ?_
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hin, *]) (by simp only [arm64_norm, *])
          (hinv2.trans hinv))
      rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq, hin]
      exact Entails.of_eq (by ac_rfl)
    | some innerVal =>
      cases innerVal with
      | v1 v1s =>
        rw [hin] at hin_cap
        simp only [Option.isSome_some, Bool.not_true] at hin_cap
        have ⟨hfit, hopt_lt, hvar_lt⟩ := v1StatePBEncodedLen_lt_of_state hin hlen
        have hls := EncodedLen.cmp_ls_false_of_lt hvar_lt hopt_lt
        have hopt_in := bv_optInner_some_eq v1s
        have ⟨hadd1, hadd2⟩ := EncodedLen.adds_no_overflow_of_eq
          (a := optPqRatchetInnerPBFieldEncodedLen (some (.v1 v1s)))
          (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
            optChainPBFieldEncodedLen st.chain)
          (c := pqRatchetStatePBEncodedLen st)
          (by unfold pqRatchetStatePBEncodedLen; rw [hin])
          (by omega)
        apply SepWPp.of_sepWP_cs (mid := (spqrProgAtExt b ext).fnAddr v1StateEncodedLenLocal2Name)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_bl
        refine SepWPp.call_cs (x := PinnedEncLenGhost.mk (a + 0x80#64) g.inner v1s)
          (F := optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
            optChainPBPinnedAt A g.chain (a + 0x30#64) st.chain ∗
            memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (96 + resStack) ∗
            encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
            encodeToVecSavedRegs sp s0 ∗ F)
          hV1StateLen (by simp only [arm64_norm, hbl]) (by simp only [arm64_norm, *])
          (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]
              exact halign)
          (ret_pc := entry + 468#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
        · intro R' hm
          rw [← optPqRatchetInnerPBPinnedAt_eq A g.inner (a + 0x80#64) (some (.v1 v1s)),
            optPqRatchetInnerPBPinnedAt,
            stackAt_callee_eq_v1StateEncodedLen (by omega) (sp - 144#64)] at hm
          simp only [arm64_norm] at hm
          simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, arm64_norm, hsp,
            sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hinv2.trans hinv_bl, hfit⟩, ?_⟩
          exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
        · intro sf code R' _ hm
          exact allowPanic_not_exited hm
        · intro sf _ hm
          simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
          exact hm.1.elim
        · intro sm hpcm hrunm hspm hcsm hinv_call
          simp only [arm64_norm, hsp] at hspm
          dsimp only [withStepInv, v1StateEncodedLenRoPinnedSpec]
          rw [sepConj_assoc]
          refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
          simp only [arm64_norm, htr] at htrm
          have hx19m : sm.readReg64 .x19 = optChainCap g.chain st.chain :=
            hcsm.1.trans (by simpa only [arm64_norm] using hx19)
          have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simpa only [arm64_norm] using hx20)
          have hx21m : sm.readReg64 .x21 = a + 128#64 :=
            hcsm.2.2.1.trans (by simp only [arm64_norm])
          have hx22m : sm.readReg64 .x22 = a + 48#64 := hcsm.2.2.2.1.trans (by simpa only [arm64_norm] using hx22)
          have hx23m : sm.readReg64 .x23 =
              BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
                optChainPBFieldEncodedLen st.chain) :=
            hcsm.2.2.2.2.1.trans (by simpa only [arm64_norm] using hx23)
          have hx25m : sm.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation :=
            hcsm.2.2.2.2.2.2.1.trans (by simpa only [arm64_norm] using hx25)
          have hx27m : sm.readReg64 .x27 = sret :=
            hcsm.2.2.2.2.2.2.2.2.1.trans (by simpa only [arm64_norm] using hx27)
          have hx28m : sm.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner := by
            rw [hin]; exact hcsm.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])
          have hfpm : sm.readReg64 .fp = sp - 96#64 :=
            hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simpa only [arm64_norm] using hfp)
          apply SepWPp.of_sepWP_cs (mid := entry + 516#64); wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_post
          refine SepWPp.weaken_pre ?_
            (hnext _
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (((hinv2.trans hinv_bl).trans hinv_call).trans hinv_post))
          rw [pqRatchetStatePBPinnedAt, hin, optPqRatchetInnerPBPinnedAt,
            stackAt_callee_eq_v1StateEncodedLen (by omega) (sp - 144#64)]
          simp only [arm64_norm, hsp]
          exact Entails.of_eq (by ac_rfl)

/-! ## Master Phase 1 Theorem (`0x6d010 .. 0x6d214`, `+0 .. +516`) -/

/-- Full Phase 1 stepping theorem (`0x6d010 .. 0x6d214`): executes the prologue and total
`encoded_len` computation for `PqRatchetState::encode_to_vec`, reaching `+516` (`0x6d214`) with
`x23 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)`. -/
theorem step_encodeToVec_phase1 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 : State}
    (hChainLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr chainEncodedLenLocal2Name)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hV1StateLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr v1StateEncodedLenLocal2Name)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))))
    (sret a sp : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running) (hsp : s0.sp = sp)
    (hx0 : s0.readReg64 .x0 = sret) (hx1 : s0.readReg64 .x1 = a)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt sp (encodeToVecStackOf resStack)) ∗ F)
    (hnext : ∀ (s3 : State) (v0 v1 v2 v3 v4 v5 : BitVec 64),
      s3.pc = entry + 516#64 → s3.status = .Running → s3.sp = sp - 144#64 →
      s3.trace = s0.trace → s3.readReg64 .x19 = optChainCap g.chain st.chain →
      s3.readReg64 .x20 = a → s3.readReg64 .x21 = a + 128#64 →
      s3.readReg64 .x22 = a + 48#64 →
      s3.readReg64 .x23 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      s3.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation →
      s3.readReg64 .x27 = sret → s3.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner →
      s3.readReg64 .fp = sp - 96#64 → StepInv s0 s3 →
      SepWPp (spqrProgAtExt b ext) ret s3
        ((pqRatchetStatePBPinnedAt A g a st ∗
          ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
          encodeToVecSavedRegs sp s0) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s0 P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  refine step_encodeToVec_prologue_and_vn hres b A ext hfn sret a sp g st hlen halign
    hpc hrun hsp hx0 hx1 (F := ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗ F) (by ac_rfl) ?_
  intro s1 v0 v1 v2 v3 v4 v5 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx25_1 hx27_1 hfp1 hinv1
  refine step_encodeToVec_chain_len hres b A ext hfn hChainLen sret a sp v0 v1 v2 v3 v4 v5 g st hlen halign
    hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx25_1 hx27_1 hfp1 hinv1
    (F := ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗ F) rfl ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx22_2 hx23_2 hx25_2 hx27_2 hfp2 hinv2
  refine step_encodeToVec_inner_len hres b A ext hfn hV1StateLen sret a sp v0 v1 v2 v3 v4 v5 g st hlen halign
    hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx22_2 hx23_2 hx25_2 hx27_2 hfp2 hinv2
    (F := F) (by ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx25_3 hx27_3 hx28_3 hfp3 hinv3
  exact hnext s3 v0 v1 v2 v3 v4 v5 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx25_3 hx27_3 hx28_3 hfp3 hinv3

end CryptoVerification.SpqrV1.Prost.EncodeToVec
