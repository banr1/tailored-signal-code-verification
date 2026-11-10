/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import ProofLib.SepLogic.WPp

/-!
# `V1State::encoded_len` Two-Field Variant Branches Part A (`k = 4, 9, 3, 1`)

Symbolic-execution stepping lemmas for the first four two-field variants (`uc` at `a + 8`, `poly`
at `a + off2`) of `spqr::proto::pq_ratchet::V1State::encoded_len`:
- `k = 4`: `.ekSentCt1Received` (`+100..+232`, `+1304..+1328`)
- `k = 9`: `.ct1Acknowledged` (`+236..+368`, `+1344..+1368`)
- `k = 3`: `.ct1Received` (`+384..+516`, `+1384..+1408`)
- `k = 1`: `.keysSampled` (`+576..+708`, `+1424..+1448`)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open EncodedLen

local notation "tripleRatchetProgAtExt" => CryptoVerification.LibsignalTripleRatchet.contractProg

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

@[local simp, local arm64_norm]
theorem add_48_sub_40 (a : BitVec 64) :
    a + 48#64 + -40#64 = a + 8#64 := by bv_bits

@[local simp, local arm64_norm]
theorem add_48_add_neg40 (a : BitVec 64) :
    a + 48#64 + 0xffffffffffffffd8#64 = a + 8#64 := by bv_bits

@[local simp, local arm64_norm]
theorem add_64_sub_56 (a : BitVec 64) :
    a + 64#64 + -56#64 = a + 8#64 := by bv_bits

@[local simp, local arm64_norm]
theorem add_64_add_neg56 (a : BitVec 64) :
    a + 64#64 + 0xffffffffffffffc8#64 = a + 8#64 := by bv_bits

/-! ## 1. Branch `k = 4` (`.ekSentCt1Received`, `+100..+232` and `+1304..+1328`) -/

/-- Field-2 (`receivingCt2 = some p`) continuation at `+188` for `.ekSentCt1Received`. -/
theorem step_v1State_ekSentCt1Received_f2_some (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hbl2 : CallPinnedEncLenAtF Φ prog entry 188
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (g : Unchunked4PBGhost × PolynomialDecoderPBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.EkSentCt1Received) (p : PolynomialDecoder)
    (hp : v.receivingCt2 = some p)
    (hfit : v1StatePBEncodedLen ⟨some (.ekSentCt1Received v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 188#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a + 112#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen v.uc))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 112#64) v.receivingCt2 ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ekSentCt1Received v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range hfn 192 236
  v1State_fetches_range hfn 1324 1332
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hp_fit : polynomialDecoderPBEncodedLen p < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp,
      optPolynomialDecoderPBFieldEncodedLen] at hfit; omega
  have htot_fit : optPolynomialDecoderPBFieldEncodedLen (some p) < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp] at hfit; omega
  have hsum_fit : v1StateInnerPayloadEncodedLen (.ekSentCt1Received v) < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen] at hfit; omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
  have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 112#64) v.receivingCt2 ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
    ((polynomialDecoderPBPinnedAt A g.2 (a + 112#64) p ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗
      (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗ F)) := by
    simp only [hp, optPolynomialDecoderPBPinnedAt]; ac_rfl
  apply SepWPpF.congr_pre hP_bl
  refine hbl2 (s0.readReg64 .lr) g.2 (a + 112#64) (sp - 32#64) p s _ Q Qp
    hpc hrun hsp hsp_sub_align hx0 hp_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  have hf2_eq := bv_optMsgField_some (inner := polynomialDecoderPBEncodedLen p)
    (tot := optPolynomialDecoderPBFieldEncodedLen (some p)) rfl
  have hvlen_lt : varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen p)) <
      optPolynomialDecoderPBFieldEncodedLen (some p) := by
    simp only [optPolynomialDecoderPBFieldEncodedLen]; omega
  have ⟨hule_f, hule_f_rev, hult_f, hsub_f, hbeq_f⟩ := cmp_ls_false_of_lt hvlen_lt htot_fit
  have hult_f_fwd := ult_of_lt_of_fit hvlen_lt htot_fit
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ :=
    adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen (some p))
      (b := optEkSentCt1ReceivedPBFieldEncodedLen v.uc)
      (c := v1StateInnerPayloadEncodedLen (.ekSentCt1Received v))
      (by simp only [v1StateInnerPayloadEncodedLen, hp])
      hsum_fit
  apply SepWPpF.of_sepWP (mid := entry + 1580#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  refine step_v1State_tail_1580 Φ prog entry hfn sp (.ekSentCt1Received v) hfit
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
    (by simp [arm64_norm, hf2_eq, hx0_1, h19_1, hx19, hadd_sum])
    ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
     by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
     by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
     by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
     by simp [arm64_norm, h28_1, h28]⟩
    rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
      hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 4` (`.ekSentCt1Received`, `+100`): steps from `entry + 100#64` to `s0.readReg64 .lr`. -/
theorem step_v1State_ekSentCt1Received (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF Φ prog entry 124
      (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAtF Φ prog entry 188
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (g : Unchunked4PBGhost × PolynomialDecoderPBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.EkSentCt1Received)
    (hfit : v1StatePBEncodedLen ⟨some (.ekSentCt1Received v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap1 : (optEkSentCt1ReceivedCap g.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
             (optEkSentCt1ReceivedCap g.1 v.uc + 1#64 != 0#64) = v.uc.isSome)
    (hcap2 : (optPolyDecCap g.2 v.receivingCt2 + 1#64 == 0#64) = !v.receivingCt2.isSome ∧
             (optPolyDecCap g.2 v.receivingCt2 + 1#64 != 0#64) = v.receivingCt2.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 112#64) v.receivingCt2 ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ekSentCt1Received v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range hfn 100 124
  v1State_fetches_range hfn 128 188
  v1State_fetches_range hfn 1304 1332
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  rcases hcap1 with ⟨hcap1_beq, hcap1_bne⟩
  rcases hcap2 with ⟨hcap2_beq, hcap2_bne⟩
  subst hP
  cases huc : v.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap1_beq hcap1_bne
    cases hp : v.receivingCt2 with
    | none =>
      simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
      rw [optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 112#64) none]
      apply SepWPpF.of_sepWP (mid := entry + 1580#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        ← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 112#64) none, ← huc, ← hp]
      refine step_v1State_tail_1580 Φ prog entry hfn sp (.ekSentCt1Received v) hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
        (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hp,
          optEkSentCt1ReceivedPBFieldEncodedLen, optPolynomialDecoderPBFieldEncodedLen])
        ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
         by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
         by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
    | some p =>
      simp only [hp, Option.isSome_some, Bool.not_true] at hcap2_beq hcap2_bne
      rw [optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 112#64) (some p)]
      apply SepWPpF.of_sepWP (mid := entry + 188#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        ← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 112#64) (some p), ← huc, ← hp]
      refine step_v1State_ekSentCt1Received_f2_some Φ prog A entry hfn hbl2 g a sp v p hp hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
        (by simp [arm64_norm, hx0])
        (by simp [arm64_norm, huc, optEkSentCt1ReceivedPBFieldEncodedLen])
        ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
         by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
         by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap1_beq hcap1_bne
    have hu_fit : ekSentCt1ReceivedPBEncodedLen u < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc,
        optEkSentCt1ReceivedPBFieldEncodedLen] at hfit; omega
    have htot1_fit : optEkSentCt1ReceivedPBFieldEncodedLen (some u) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc] at hfit; omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
    rw [optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 8#64) (some u)]
    apply SepWPpF.of_sepWP (mid := entry + 124#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 8#64) (some u), ← huc]
    have hP_bl1 : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
        optPolynomialDecoderPBPinnedAt A g.2 (a + 112#64) v.receivingCt2 ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((ekSentCt1ReceivedPBPinnedAt A g.1 (a + 8#64) u ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 112#64) v.receivingCt2 ∗ F)) := by
      simp only [huc, optEkSentCt1ReceivedPBPinnedAt]; ac_rfl
    apply SepWPpF.congr_pre hP_bl1
    refine hbl1 (s0.readReg64 .lr) g.1 (a + 8#64) (sp - 32#64) u _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hu_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPpF.congr_pre hP_bl1.symm
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
    have hf1_eq := bv_optMsgField_some (inner := ekSentCt1ReceivedPBEncodedLen u)
      (tot := optEkSentCt1ReceivedPBFieldEncodedLen (some u)) rfl
    have hvlen1_lt : varintLen (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u)) <
        optEkSentCt1ReceivedPBFieldEncodedLen (some u) := by
      simp only [optEkSentCt1ReceivedPBFieldEncodedLen]; omega
    have ⟨hule_f1, hule_f1_rev, hult_f1, hsub_f1, hbeq_f1⟩ := cmp_ls_false_of_lt hvlen1_lt htot1_fit
    have hult_f1_fwd := ult_of_lt_of_fit hvlen1_lt htot1_fit
    cases hp : v.receivingCt2 with
    | none =>
      simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 112#64) none]
      apply SepWPpF.of_sepWP (mid := entry + 1580#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 112#64) none, ← hp]
      refine step_v1State_tail_1580 Φ prog entry hfn sp (.ekSentCt1Received v) hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hp,
          optPolynomialDecoderPBFieldEncodedLen, hf1_eq, hx0_1])
        ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
         by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
         by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
         by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
         by simp [arm64_norm, h28_1, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf
    | some p =>
      simp only [hp, Option.isSome_some, Bool.not_true] at hcap2_beq hcap2_bne
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 112#64) (some p)]
      apply SepWPpF.of_sepWP (mid := entry + 188#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 112#64) (some p), ← hp]
      refine step_v1State_ekSentCt1Received_f2_some Φ prog A entry hfn hbl2 g a sp v p hp hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, h19_1, hx0])
        (by simp [arm64_norm, huc, hf1_eq, hx0_1])
        ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
         by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
         by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
         by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
         by simp [arm64_norm, h28_1, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-! ## 2. Branch `k = 9` (`.ct1Acknowledged`, `+236..+368` and `+1344..+1368`) -/

/-- Field-2 (`receivingEk = some p`) continuation at `+324` for `.ct1Acknowledged`. -/
theorem step_v1State_ct1Acknowledged_f2_some (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hbl2 : CallPinnedEncLenAtF Φ prog entry 324
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (g : Unchunked5PBGhost × PolynomialDecoderPBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.Ct1Acknowledged) (p : PolynomialDecoder)
    (hp : v.receivingEk = some p)
    (hfit : v1StatePBEncodedLen ⟨some (.ct1Acknowledged v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 324#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a + 136#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen v.uc))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optCt1SentPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 136#64) v.receivingEk ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ct1Acknowledged v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range hfn 328 372
  v1State_fetches_range hfn 1364 1372
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hp_fit : polynomialDecoderPBEncodedLen p < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp,
      optPolynomialDecoderPBFieldEncodedLen] at hfit; omega
  have htot_fit : optPolynomialDecoderPBFieldEncodedLen (some p) < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp] at hfit; omega
  have hsum_fit : v1StateInnerPayloadEncodedLen (.ct1Acknowledged v) < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen] at hfit; omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
  have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optCt1SentPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 136#64) v.receivingEk ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
    ((polynomialDecoderPBPinnedAt A g.2 (a + 136#64) p ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗
      (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optCt1SentPBPinnedAt A g.1 (a + 8#64) v.uc ∗ F)) := by
    simp only [hp, optPolynomialDecoderPBPinnedAt]; ac_rfl
  apply SepWPpF.congr_pre hP_bl
  refine hbl2 (s0.readReg64 .lr) g.2 (a + 136#64) (sp - 32#64) p s _ Q Qp
    hpc hrun hsp hsp_sub_align hx0 hp_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  have hf2_eq := bv_optMsgField_some (inner := polynomialDecoderPBEncodedLen p)
    (tot := optPolynomialDecoderPBFieldEncodedLen (some p)) rfl
  have hvlen_lt : varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen p)) <
      optPolynomialDecoderPBFieldEncodedLen (some p) := by
    simp only [optPolynomialDecoderPBFieldEncodedLen]; omega
  have ⟨hule_f, hule_f_rev, hult_f, hsub_f, hbeq_f⟩ := cmp_ls_false_of_lt hvlen_lt htot_fit
  have hult_f_fwd := ult_of_lt_of_fit hvlen_lt htot_fit
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ :=
    adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen (some p))
      (b := optCt1SentPBFieldEncodedLen v.uc)
      (c := v1StateInnerPayloadEncodedLen (.ct1Acknowledged v))
      (by simp only [v1StateInnerPayloadEncodedLen, hp])
      hsum_fit
  apply SepWPpF.of_sepWP (mid := entry + 1580#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  refine step_v1State_tail_1580 Φ prog entry hfn sp (.ct1Acknowledged v) hfit
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
    (by simp [arm64_norm, hf2_eq, hx0_1, h19_1, hx19, hadd_sum])
    ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
     by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
     by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
     by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
     by simp [arm64_norm, h28_1, h28]⟩
    rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
      hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 9` (`.ct1Acknowledged`, `+236`): steps from `entry + 236#64` to `s0.readReg64 .lr`. -/
theorem step_v1State_ct1Acknowledged (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF Φ prog entry 260
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAtF Φ prog entry 324
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (g : Unchunked5PBGhost × PolynomialDecoderPBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.Ct1Acknowledged)
    (hfit : v1StatePBEncodedLen ⟨some (.ct1Acknowledged v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 236#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap1 : (optCt1SentCap g.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
             (optCt1SentCap g.1 v.uc + 1#64 != 0#64) = v.uc.isSome)
    (hcap2 : (optPolyDecCap g.2 v.receivingEk + 1#64 == 0#64) = !v.receivingEk.isSome ∧
             (optPolyDecCap g.2 v.receivingEk + 1#64 != 0#64) = v.receivingEk.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optCt1SentPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 136#64) v.receivingEk ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ct1Acknowledged v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range hfn 236 260
  v1State_fetches_range hfn 264 324
  v1State_fetches_range hfn 1344 1372
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  rcases hcap1 with ⟨hcap1_beq, hcap1_bne⟩
  rcases hcap2 with ⟨hcap2_beq, hcap2_bne⟩
  subst hP
  cases huc : v.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap1_beq hcap1_bne
    cases hp : v.receivingEk with
    | none =>
      simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
      rw [optCt1SentPBPinnedAt_eq A g.1 (a + 8#64) none,
        optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 136#64) none]
      apply SepWPpF.of_sepWP (mid := entry + 1580#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optCt1SentPBPinnedAt_eq A g.1 (a + 8#64) none,
        ← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 136#64) none, ← huc, ← hp]
      refine step_v1State_tail_1580 Φ prog entry hfn sp (.ct1Acknowledged v) hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
        (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hp,
          optCt1SentPBFieldEncodedLen, optPolynomialDecoderPBFieldEncodedLen])
        ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
         by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
         by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
    | some p =>
      simp only [hp, Option.isSome_some, Bool.not_true] at hcap2_beq hcap2_bne
      rw [optCt1SentPBPinnedAt_eq A g.1 (a + 8#64) none,
        optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 136#64) (some p)]
      apply SepWPpF.of_sepWP (mid := entry + 324#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optCt1SentPBPinnedAt_eq A g.1 (a + 8#64) none,
        ← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 136#64) (some p), ← huc, ← hp]
      refine step_v1State_ct1Acknowledged_f2_some Φ prog A entry hfn hbl2 g a sp v p hp hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
        (by simp [arm64_norm, hx0])
        (by simp [arm64_norm, huc, optCt1SentPBFieldEncodedLen])
        ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
         by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
         by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap1_beq hcap1_bne
    have hu_fit : ct1SentPBEncodedLen u < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc,
        optCt1SentPBFieldEncodedLen] at hfit; omega
    have htot1_fit : optCt1SentPBFieldEncodedLen (some u) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc] at hfit; omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
    rw [optCt1SentPBPinnedAt_eq A g.1 (a + 8#64) (some u)]
    apply SepWPpF.of_sepWP (mid := entry + 260#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optCt1SentPBPinnedAt_eq A g.1 (a + 8#64) (some u), ← huc]
    have hP_bl1 : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optCt1SentPBPinnedAt A g.1 (a + 8#64) v.uc ∗
        optPolynomialDecoderPBPinnedAt A g.2 (a + 136#64) v.receivingEk ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((ct1SentPBPinnedAt A g.1 (a + 8#64) u ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 136#64) v.receivingEk ∗ F)) := by
      simp only [huc, optCt1SentPBPinnedAt]; ac_rfl
    apply SepWPpF.congr_pre hP_bl1
    refine hbl1 (s0.readReg64 .lr) g.1 (a + 8#64) (sp - 32#64) u _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hu_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPpF.congr_pre hP_bl1.symm
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
    have hf1_eq := bv_optMsgField_some (inner := ct1SentPBEncodedLen u)
      (tot := optCt1SentPBFieldEncodedLen (some u)) rfl
    have hvlen1_lt : varintLen (BitVec.ofNat 64 (ct1SentPBEncodedLen u)) <
        optCt1SentPBFieldEncodedLen (some u) := by
      simp only [optCt1SentPBFieldEncodedLen]; omega
    have ⟨hule_f1, hule_f1_rev, hult_f1, hsub_f1, hbeq_f1⟩ := cmp_ls_false_of_lt hvlen1_lt htot1_fit
    have hult_f1_fwd := ult_of_lt_of_fit hvlen1_lt htot1_fit
    cases hp : v.receivingEk with
    | none =>
      simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 136#64) none]
      apply SepWPpF.of_sepWP (mid := entry + 1580#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 136#64) none, ← hp]
      refine step_v1State_tail_1580 Φ prog entry hfn sp (.ct1Acknowledged v) hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hp,
          optPolynomialDecoderPBFieldEncodedLen, hf1_eq, hx0_1])
        ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
         by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
         by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
         by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
         by simp [arm64_norm, h28_1, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf
    | some p =>
      simp only [hp, Option.isSome_some, Bool.not_true] at hcap2_beq hcap2_bne
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 136#64) (some p)]
      apply SepWPpF.of_sepWP (mid := entry + 324#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 136#64) (some p), ← hp]
      refine step_v1State_ct1Acknowledged_f2_some Φ prog A entry hfn hbl2 g a sp v p hp hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, h19_1, hx0])
        (by simp [arm64_norm, huc, hf1_eq, hx0_1])
        ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
         by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
         by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
         by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
         by simp [arm64_norm, h28_1, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-! ## 3. Branch `k = 3` (`.ct1Received`, `+384..+516` and `+1384..+1408`) -/

/-- Field-2 (`sendingEk = some p`) continuation at `+472` for `.ct1Received`. -/
theorem step_v1State_ct1Received_f2_some (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hbl2 : CallPinnedEncLenAtF Φ prog entry 472
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (g : Unchunked4PBGhost × PolynomialEncoderPBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.Ct1Received) (p : PolynomialEncoder)
    (hp : v.sendingEk = some p)
    (hfit : v1StatePBEncodedLen ⟨some (.ct1Received v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 472#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a + 112#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen v.uc))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 112#64) v.sendingEk ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ct1Received v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range hfn 476 520
  v1State_fetches_range hfn 1404 1412
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hp_fit : polynomialEncoderPBEncodedLen p < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp,
      optPolynomialEncoderPBFieldEncodedLen] at hfit; omega
  have htot_fit : optPolynomialEncoderPBFieldEncodedLen (some p) < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp] at hfit; omega
  have hsum_fit : v1StateInnerPayloadEncodedLen (.ct1Received v) < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen] at hfit; omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
  have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 112#64) v.sendingEk ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
    ((polynomialEncoderPBPinnedAt A g.2 (a + 112#64) p ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗
      (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗ F)) := by
    simp only [hp, optPolynomialEncoderPBPinnedAt]; ac_rfl
  apply SepWPpF.congr_pre hP_bl
  refine hbl2 (s0.readReg64 .lr) g.2 (a + 112#64) (sp - 32#64) p s _ Q Qp
    hpc hrun hsp hsp_sub_align hx0 hp_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  have hf2_eq := bv_optMsgField_some (inner := polynomialEncoderPBEncodedLen p)
    (tot := optPolynomialEncoderPBFieldEncodedLen (some p)) rfl
  have hvlen_lt : varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen p)) <
      optPolynomialEncoderPBFieldEncodedLen (some p) := by
    simp only [optPolynomialEncoderPBFieldEncodedLen]; omega
  have ⟨hule_f, hule_f_rev, hult_f, hsub_f, hbeq_f⟩ := cmp_ls_false_of_lt hvlen_lt htot_fit
  have hult_f_fwd := ult_of_lt_of_fit hvlen_lt htot_fit
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ :=
    adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen (some p))
      (b := optEkSentCt1ReceivedPBFieldEncodedLen v.uc)
      (c := v1StateInnerPayloadEncodedLen (.ct1Received v))
      (by simp only [v1StateInnerPayloadEncodedLen, hp])
      hsum_fit
  apply SepWPpF.of_sepWP (mid := entry + 1580#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  refine step_v1State_tail_1580 Φ prog entry hfn sp (.ct1Received v) hfit
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
    (by simp [arm64_norm, hf2_eq, hx0_1, h19_1, hx19, hadd_sum])
    ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
     by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
     by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
     by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
     by simp [arm64_norm, h28_1, h28]⟩
    rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
      hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 3` (`.ct1Received`, `+384`): steps from `entry + 384#64` to `s0.readReg64 .lr`. -/
theorem step_v1State_ct1Received (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF Φ prog entry 408
      (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAtF Φ prog entry 472
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (g : Unchunked4PBGhost × PolynomialEncoderPBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.Ct1Received)
    (hfit : v1StatePBEncodedLen ⟨some (.ct1Received v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap1 : (optEkSentCt1ReceivedCap g.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
             (optEkSentCt1ReceivedCap g.1 v.uc + 1#64 != 0#64) = v.uc.isSome)
    (hcap2 : (optPolyEncCap g.2 v.sendingEk + 1#64 == 0#64) = !v.sendingEk.isSome ∧
             (optPolyEncCap g.2 v.sendingEk + 1#64 != 0#64) = v.sendingEk.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 112#64) v.sendingEk ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ct1Received v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range hfn 384 408
  v1State_fetches_range hfn 412 472
  v1State_fetches_range hfn 1384 1412
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  rcases hcap1 with ⟨hcap1_beq, hcap1_bne⟩
  rcases hcap2 with ⟨hcap2_beq, hcap2_bne⟩
  subst hP
  cases huc : v.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap1_beq hcap1_bne
    cases hp : v.sendingEk with
    | none =>
      simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
      rw [optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) none]
      apply SepWPpF.of_sepWP (mid := entry + 1580#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        ← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) none, ← huc, ← hp]
      refine step_v1State_tail_1580 Φ prog entry hfn sp (.ct1Received v) hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
        (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hp,
          optEkSentCt1ReceivedPBFieldEncodedLen, optPolynomialEncoderPBFieldEncodedLen])
        ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
         by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
         by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
    | some p =>
      simp only [hp, Option.isSome_some, Bool.not_true] at hcap2_beq hcap2_bne
      rw [optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) (some p)]
      apply SepWPpF.of_sepWP (mid := entry + 472#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        ← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) (some p), ← huc, ← hp]
      refine step_v1State_ct1Received_f2_some Φ prog A entry hfn hbl2 g a sp v p hp hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
        (by simp [arm64_norm, hx0])
        (by simp [arm64_norm, huc, optEkSentCt1ReceivedPBFieldEncodedLen])
        ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
         by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
         by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap1_beq hcap1_bne
    have hu_fit : ekSentCt1ReceivedPBEncodedLen u < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc,
        optEkSentCt1ReceivedPBFieldEncodedLen] at hfit; omega
    have htot1_fit : optEkSentCt1ReceivedPBFieldEncodedLen (some u) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc] at hfit; omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
    rw [optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 8#64) (some u)]
    apply SepWPpF.of_sepWP (mid := entry + 408#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optEkSentCt1ReceivedPBPinnedAt_eq A g.1 (a + 8#64) (some u), ← huc]
    have hP_bl1 : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optEkSentCt1ReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
        optPolynomialEncoderPBPinnedAt A g.2 (a + 112#64) v.sendingEk ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((ekSentCt1ReceivedPBPinnedAt A g.1 (a + 8#64) u ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
          optPolynomialEncoderPBPinnedAt A g.2 (a + 112#64) v.sendingEk ∗ F)) := by
      simp only [huc, optEkSentCt1ReceivedPBPinnedAt]; ac_rfl
    apply SepWPpF.congr_pre hP_bl1
    refine hbl1 (s0.readReg64 .lr) g.1 (a + 8#64) (sp - 32#64) u _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hu_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPpF.congr_pre hP_bl1.symm
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
    have hf1_eq := bv_optMsgField_some (inner := ekSentCt1ReceivedPBEncodedLen u)
      (tot := optEkSentCt1ReceivedPBFieldEncodedLen (some u)) rfl
    have hvlen1_lt : varintLen (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u)) <
        optEkSentCt1ReceivedPBFieldEncodedLen (some u) := by
      simp only [optEkSentCt1ReceivedPBFieldEncodedLen]; omega
    have ⟨hule_f1, hule_f1_rev, hult_f1, hsub_f1, hbeq_f1⟩ := cmp_ls_false_of_lt hvlen1_lt htot1_fit
    have hult_f1_fwd := ult_of_lt_of_fit hvlen1_lt htot1_fit
    cases hp : v.sendingEk with
    | none =>
      simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
      rw [optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) none]
      apply SepWPpF.of_sepWP (mid := entry + 1580#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) none, ← hp]
      refine step_v1State_tail_1580 Φ prog entry hfn sp (.ct1Received v) hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hp,
          optPolynomialEncoderPBFieldEncodedLen, hf1_eq, hx0_1])
        ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
         by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
         by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
         by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
         by simp [arm64_norm, h28_1, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf
    | some p =>
      simp only [hp, Option.isSome_some, Bool.not_true] at hcap2_beq hcap2_bne
      rw [optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) (some p)]
      apply SepWPpF.of_sepWP (mid := entry + 472#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) (some p), ← hp]
      refine step_v1State_ct1Received_f2_some Φ prog A entry hfn hbl2 g a sp v p hp hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, h19_1, hx0])
        (by simp [arm64_norm, huc, hf1_eq, hx0_1])
        ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
         by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
         by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
         by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
         by simp [arm64_norm, h28_1, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-! ## 4. Branch `k = 1` (`.keysSampled`, `+576..+708` and `+1424..+1448`) -/

/-- Field-2 (`sendingHdr = some p`) continuation at `+664` for `.keysSampled`. -/
theorem step_v1State_keysSampled_f2_some (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hbl2 : CallPinnedEncLenAtF Φ prog entry 664
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (g : Unchunked4PBGhost × PolynomialEncoderPBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.KeysSampled) (p : PolynomialEncoder)
    (hp : v.sendingHdr = some p)
    (hfit : v1StatePBEncodedLen ⟨some (.keysSampled v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 664#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a + 112#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 (optHeaderSentPBFieldEncodedLen v.uc))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optHeaderSentPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 112#64) v.sendingHdr ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.keysSampled v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range hfn 668 712
  v1State_fetches_range hfn 1444 1452
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hp_fit : polynomialEncoderPBEncodedLen p < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp,
      optPolynomialEncoderPBFieldEncodedLen] at hfit; omega
  have htot_fit : optPolynomialEncoderPBFieldEncodedLen (some p) < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp] at hfit; omega
  have hsum_fit : v1StateInnerPayloadEncodedLen (.keysSampled v) < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen] at hfit; omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
  have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optHeaderSentPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 112#64) v.sendingHdr ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
    ((polynomialEncoderPBPinnedAt A g.2 (a + 112#64) p ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗
      (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optHeaderSentPBPinnedAt A g.1 (a + 8#64) v.uc ∗ F)) := by
    simp only [hp, optPolynomialEncoderPBPinnedAt]; ac_rfl
  apply SepWPpF.congr_pre hP_bl
  refine hbl2 (s0.readReg64 .lr) g.2 (a + 112#64) (sp - 32#64) p s _ Q Qp
    hpc hrun hsp hsp_sub_align hx0 hp_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  have hf2_eq := bv_optMsgField_some (inner := polynomialEncoderPBEncodedLen p)
    (tot := optPolynomialEncoderPBFieldEncodedLen (some p)) rfl
  have hvlen_lt : varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen p)) <
      optPolynomialEncoderPBFieldEncodedLen (some p) := by
    simp only [optPolynomialEncoderPBFieldEncodedLen]; omega
  have ⟨hule_f, hule_f_rev, hult_f, hsub_f, hbeq_f⟩ := cmp_ls_false_of_lt hvlen_lt htot_fit
  have hult_f_fwd := ult_of_lt_of_fit hvlen_lt htot_fit
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ :=
    adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen (some p))
      (b := optHeaderSentPBFieldEncodedLen v.uc)
      (c := v1StateInnerPayloadEncodedLen (.keysSampled v))
      (by simp only [v1StateInnerPayloadEncodedLen, hp])
      hsum_fit
  apply SepWPpF.of_sepWP (mid := entry + 1580#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  refine step_v1State_tail_1580 Φ prog entry hfn sp (.keysSampled v) hfit
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
    (by simp [arm64_norm, hf2_eq, hx0_1, h19_1, hx19, hadd_sum])
    ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
     by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
     by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
     by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
     by simp [arm64_norm, h28_1, h28]⟩
    rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
      hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 1` (`.keysSampled`, `+576`): steps from `entry + 576#64` to `s0.readReg64 .lr`. -/
theorem step_v1State_keysSampled (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF Φ prog entry 600
      (headerSentPBPinnedAt A) headerSentPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAtF Φ prog entry 664
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (g : Unchunked4PBGhost × PolynomialEncoderPBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.KeysSampled)
    (hfit : v1StatePBEncodedLen ⟨some (.keysSampled v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 576#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap1 : (optHeaderSentCap g.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
             (optHeaderSentCap g.1 v.uc + 1#64 != 0#64) = v.uc.isSome)
    (hcap2 : (optPolyEncCap g.2 v.sendingHdr + 1#64 == 0#64) = !v.sendingHdr.isSome ∧
             (optPolyEncCap g.2 v.sendingHdr + 1#64 != 0#64) = v.sendingHdr.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optHeaderSentPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 112#64) v.sendingHdr ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.keysSampled v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range hfn 576 600
  v1State_fetches_range hfn 604 664
  v1State_fetches_range hfn 1424 1452
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  rcases hcap1 with ⟨hcap1_beq, hcap1_bne⟩
  rcases hcap2 with ⟨hcap2_beq, hcap2_bne⟩
  subst hP
  cases huc : v.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap1_beq hcap1_bne
    cases hp : v.sendingHdr with
    | none =>
      simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
      rw [optHeaderSentPBPinnedAt_eq A g.1 (a + 8#64) none,
        optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) none]
      apply SepWPpF.of_sepWP (mid := entry + 1580#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optHeaderSentPBPinnedAt_eq A g.1 (a + 8#64) none,
        ← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) none, ← huc, ← hp]
      refine step_v1State_tail_1580 Φ prog entry hfn sp (.keysSampled v) hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
        (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hp,
          optHeaderSentPBFieldEncodedLen, optPolynomialEncoderPBFieldEncodedLen])
        ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
         by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
         by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
    | some p =>
      simp only [hp, Option.isSome_some, Bool.not_true] at hcap2_beq hcap2_bne
      rw [optHeaderSentPBPinnedAt_eq A g.1 (a + 8#64) none,
        optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) (some p)]
      apply SepWPpF.of_sepWP (mid := entry + 664#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optHeaderSentPBPinnedAt_eq A g.1 (a + 8#64) none,
        ← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) (some p), ← huc, ← hp]
      refine step_v1State_keysSampled_f2_some Φ prog A entry hfn hbl2 g a sp v p hp hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
        (by simp [arm64_norm, hx0])
        (by simp [arm64_norm, huc, optHeaderSentPBFieldEncodedLen])
        ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
         by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
         by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap1_beq hcap1_bne
    have hu_fit : headerSentPBEncodedLen u < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc,
        optHeaderSentPBFieldEncodedLen] at hfit; omega
    have htot1_fit : optHeaderSentPBFieldEncodedLen (some u) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc] at hfit; omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
    rw [optHeaderSentPBPinnedAt_eq A g.1 (a + 8#64) (some u)]
    apply SepWPpF.of_sepWP (mid := entry + 600#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optHeaderSentPBPinnedAt_eq A g.1 (a + 8#64) (some u), ← huc]
    have hP_bl1 : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optHeaderSentPBPinnedAt A g.1 (a + 8#64) v.uc ∗
        optPolynomialEncoderPBPinnedAt A g.2 (a + 112#64) v.sendingHdr ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((headerSentPBPinnedAt A g.1 (a + 8#64) u ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
          optPolynomialEncoderPBPinnedAt A g.2 (a + 112#64) v.sendingHdr ∗ F)) := by
      simp only [huc, optHeaderSentPBPinnedAt]; ac_rfl
    apply SepWPpF.congr_pre hP_bl1
    refine hbl1 (s0.readReg64 .lr) g.1 (a + 8#64) (sp - 32#64) u _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hu_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPpF.congr_pre hP_bl1.symm
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
    have hf1_eq := bv_optMsgField_some (inner := headerSentPBEncodedLen u)
      (tot := optHeaderSentPBFieldEncodedLen (some u)) rfl
    have hvlen1_lt : varintLen (BitVec.ofNat 64 (headerSentPBEncodedLen u)) <
        optHeaderSentPBFieldEncodedLen (some u) := by
      simp only [optHeaderSentPBFieldEncodedLen]; omega
    have ⟨hule_f1, hule_f1_rev, hult_f1, hsub_f1, hbeq_f1⟩ := cmp_ls_false_of_lt hvlen1_lt htot1_fit
    have hult_f1_fwd := ult_of_lt_of_fit hvlen1_lt htot1_fit
    cases hp : v.sendingHdr with
    | none =>
      simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
      rw [optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) none]
      apply SepWPpF.of_sepWP (mid := entry + 1580#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) none, ← hp]
      refine step_v1State_tail_1580 Φ prog entry hfn sp (.keysSampled v) hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hp,
          optPolynomialEncoderPBFieldEncodedLen, hf1_eq, hx0_1])
        ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
         by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
         by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
         by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
         by simp [arm64_norm, h28_1, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf
    | some p =>
      simp only [hp, Option.isSome_some, Bool.not_true] at hcap2_beq hcap2_bne
      rw [optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) (some p)]
      apply SepWPpF.of_sepWP (mid := entry + 664#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 112#64) (some p), ← hp]
      refine step_v1State_keysSampled_f2_some Φ prog A entry hfn hbl2 g a sp v p hp hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, h19_1, hx0])
        (by simp [arm64_norm, huc, hf1_eq, hx0_1])
        ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
         by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
         by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
         by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
         by simp [arm64_norm, h28_1, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

end CryptoVerification.SpqrV1.ProtoRepr
