/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateBranches
import ProofLib.SepLogic.WPp

/-!
# CLI `V1State::encoded_len` Two-Field Variant Branches (Part B: `k = 6, 8, 5, 10`)

Proves `SepWPp` branch lemmas for `.headerReceived` (`k = 6`), `.ekReceivedCt1Sampled` (`k = 8`),
`.noHeaderReceived` (`k = 5`), and `.ct2Sampled` (`k = 10`) in `V1State::encoded_len` on the CLI
image.
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
  add_48_sub_40 add_48_add_neg40 add_64_sub_56 add_64_add_neg56

/-! ## 5. Branch `k = 6` (`.headerReceived`, `+732..+864` and `+1464..+1488`) -/

/-- Field-2 (`receivingEk = some p`) continuation at `+820` for `.headerReceived`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_headerReceived_f2_some (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hbl2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 820
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (g : Unchunked3PBGhost × PolynomialDecoderPBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.HeaderReceived) (p : PolynomialDecoder)
    (hp : v.receivingEk = some p)
    (hfit : v1StatePBEncodedLen ⟨some (.headerReceived v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a + 88#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 (optHeaderReceivedPBFieldEncodedLen v.uc))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optHeaderReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 88#64) v.receivingEk ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.headerReceived v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 824 868
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1484 1492
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hp_fit : polynomialDecoderPBEncodedLen p < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp,
      optPolynomialDecoderPBFieldEncodedLen] at hfit; omega
  have htot_fit : optPolynomialDecoderPBFieldEncodedLen (some p) < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp] at hfit; omega
  have hsum_fit : v1StateInnerPayloadEncodedLen (.headerReceived v) < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen] at hfit; omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
  have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optHeaderReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 88#64) v.receivingEk ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
    ((polynomialDecoderPBPinnedAt A g.2 (a + 88#64) p ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗
      (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optHeaderReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗ F)) := by
    simp only [hp, optPolynomialDecoderPBPinnedAt]; ac_rfl
  apply SepWPp.congr_pre hP_bl
  refine hbl2 (s0.readReg64 .lr) g.2 (a + 88#64) (sp - 32#64) p s _ Q Qp
    hpc hrun hsp hsp_sub_align hx0 hp_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPp.congr_pre hP_bl.symm
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
      (b := optHeaderReceivedPBFieldEncodedLen v.uc)
      (c := v1StateInnerPayloadEncodedLen (.headerReceived v))
      (by simp only [v1StateInnerPayloadEncodedLen, hp])
      hsum_fit
  apply SepWPp.of_sepWP (mid := entry + 1580#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 b abs entry hfn sp (.headerReceived v) hfit
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
    (by simp [arm64_norm, hf2_eq, hx0_1, h19_1, hx19, hadd_sum])
    ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
     by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
     by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
     by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
     by simp [arm64_norm, h28_1, h28]⟩
    rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
      hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 6` (`.headerReceived`, `+732`): steps from `entry + 732#64` to `s0.readReg64 .lr`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_headerReceived (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hbl1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 756
      (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 820
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (g : Unchunked3PBGhost × PolynomialDecoderPBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.HeaderReceived)
    (hfit : v1StatePBEncodedLen ⟨some (.headerReceived v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 732#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap1 : (optHeaderReceivedCap g.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
             (optHeaderReceivedCap g.1 v.uc + 1#64 != 0#64) = v.uc.isSome)
    (hcap2 : (optPolyDecCap g.2 v.receivingEk + 1#64 == 0#64) = !v.receivingEk.isSome ∧
             (optPolyDecCap g.2 v.receivingEk + 1#64 != 0#64) = v.receivingEk.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optHeaderReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.2 (a + 88#64) v.receivingEk ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.headerReceived v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 732 756
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 760 820
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1464 1492
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
      rw [optHeaderReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 88#64) none]
      apply SepWPp.of_sepWP (mid := entry + 1580#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optHeaderReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        ← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 88#64) none, ← huc, ← hp]
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 b abs entry hfn sp (.headerReceived v) hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
        (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hp,
          optHeaderReceivedPBFieldEncodedLen, optPolynomialDecoderPBFieldEncodedLen])
        ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
         by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
         by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
    | some p =>
      simp only [hp, Option.isSome_some, Bool.not_true] at hcap2_beq hcap2_bne
      rw [optHeaderReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 88#64) (some p)]
      apply SepWPp.of_sepWP (mid := entry + 820#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optHeaderReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        ← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 88#64) (some p), ← huc, ← hp]
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_headerReceived_f2_some b A abs entry hfn hbl2 g a sp v p hp hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
        (by simp [arm64_norm, hx0])
        (by simp [arm64_norm, huc, optHeaderReceivedPBFieldEncodedLen])
        ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
         by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
         by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap1_beq hcap1_bne
    have hu_fit : headerReceivedPBEncodedLen u < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc,
        optHeaderReceivedPBFieldEncodedLen] at hfit; omega
    have htot1_fit : optHeaderReceivedPBFieldEncodedLen (some u) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc] at hfit; omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
    rw [optHeaderReceivedPBPinnedAt_eq A g.1 (a + 8#64) (some u)]
    apply SepWPp.of_sepWP (mid := entry + 756#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optHeaderReceivedPBPinnedAt_eq A g.1 (a + 8#64) (some u), ← huc]
    have hP_bl1 : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optHeaderReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
        optPolynomialDecoderPBPinnedAt A g.2 (a + 88#64) v.receivingEk ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((headerReceivedPBPinnedAt A g.1 (a + 8#64) u ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
          optPolynomialDecoderPBPinnedAt A g.2 (a + 88#64) v.receivingEk ∗ F)) := by
      simp only [huc, optHeaderReceivedPBPinnedAt]; ac_rfl
    apply SepWPp.congr_pre hP_bl1
    refine hbl1 (s0.readReg64 .lr) g.1 (a + 8#64) (sp - 32#64) u _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hu_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPp.congr_pre hP_bl1.symm
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
    have hf1_eq := bv_optMsgField_some (inner := headerReceivedPBEncodedLen u)
      (tot := optHeaderReceivedPBFieldEncodedLen (some u)) rfl
    have hvlen1_lt : varintLen (BitVec.ofNat 64 (headerReceivedPBEncodedLen u)) <
        optHeaderReceivedPBFieldEncodedLen (some u) := by
      simp only [optHeaderReceivedPBFieldEncodedLen]; omega
    have ⟨hule_f1, hule_f1_rev, hult_f1, hsub_f1, hbeq_f1⟩ := cmp_ls_false_of_lt hvlen1_lt htot1_fit
    have hult_f1_fwd := ult_of_lt_of_fit hvlen1_lt htot1_fit
    cases hp : v.receivingEk with
    | none =>
      simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 88#64) none]
      apply SepWPp.of_sepWP (mid := entry + 1580#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 88#64) none, ← hp]
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 b abs entry hfn sp (.headerReceived v) hfit
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
      rw [optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 88#64) (some p)]
      apply SepWPp.of_sepWP (mid := entry + 820#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optPolynomialDecoderPBPinnedAt_eq A g.2 (a + 88#64) (some p), ← hp]
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_headerReceived_f2_some b A abs entry hfn hbl2 g a sp v p hp hfit
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

/-! ## 6. Branch `k = 8` (`.ekReceivedCt1Sampled`, `+888..+1020` and `+1504..+1528`) -/

/-- Field-2 (`sendingCt1 = some p`) continuation at `+976` for `.ekReceivedCt1Sampled`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ekReceivedCt1Sampled_f2_some (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hbl2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 976
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (g : Unchunked5PBGhost × PolynomialEncoderPBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.EkReceivedCt1Sampled) (p : PolynomialEncoder)
    (hp : v.sendingCt1 = some p)
    (hfit : v1StatePBEncodedLen ⟨some (.ekReceivedCt1Sampled v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 976#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a + 136#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 (optCt1SentEkReceivedPBFieldEncodedLen v.uc))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optCt1SentEkReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 136#64) v.sendingCt1 ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ekReceivedCt1Sampled v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 980 1024
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1524 1532
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hp_fit : polynomialEncoderPBEncodedLen p < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp,
      optPolynomialEncoderPBFieldEncodedLen] at hfit; omega
  have htot_fit : optPolynomialEncoderPBFieldEncodedLen (some p) < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp] at hfit; omega
  have hsum_fit : v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled v) < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen] at hfit; omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
  have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optCt1SentEkReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 136#64) v.sendingCt1 ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
    ((polynomialEncoderPBPinnedAt A g.2 (a + 136#64) p ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗
      (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optCt1SentEkReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗ F)) := by
    simp only [hp, optPolynomialEncoderPBPinnedAt]; ac_rfl
  apply SepWPp.congr_pre hP_bl
  refine hbl2 (s0.readReg64 .lr) g.2 (a + 136#64) (sp - 32#64) p s _ Q Qp
    hpc hrun hsp hsp_sub_align hx0 hp_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPp.congr_pre hP_bl.symm
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
      (b := optCt1SentEkReceivedPBFieldEncodedLen v.uc)
      (c := v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled v))
      (by simp only [v1StateInnerPayloadEncodedLen, hp])
      hsum_fit
  apply SepWPp.of_sepWP (mid := entry + 1580#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 b abs entry hfn sp (.ekReceivedCt1Sampled v) hfit
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
    (by simp [arm64_norm, hf2_eq, hx0_1, h19_1, hx19, hadd_sum])
    ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
     by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
     by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
     by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
     by simp [arm64_norm, h28_1, h28]⟩
    rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
      hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 8` (`.ekReceivedCt1Sampled`, `+888`): steps from `entry + 888#64` to `s0.readReg64 .lr`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ekReceivedCt1Sampled (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hbl1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 912
      (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 976
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (g : Unchunked5PBGhost × PolynomialEncoderPBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.EkReceivedCt1Sampled)
    (hfit : v1StatePBEncodedLen ⟨some (.ekReceivedCt1Sampled v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 888#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap1 : (optCt1SentEkReceivedCap g.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
             (optCt1SentEkReceivedCap g.1 v.uc + 1#64 != 0#64) = v.uc.isSome)
    (hcap2 : (optPolyEncCap g.2 v.sendingCt1 + 1#64 == 0#64) = !v.sendingCt1.isSome ∧
             (optPolyEncCap g.2 v.sendingCt1 + 1#64 != 0#64) = v.sendingCt1.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optCt1SentEkReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.2 (a + 136#64) v.sendingCt1 ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ekReceivedCt1Sampled v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 888 912
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 916 976
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1504 1532
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  rcases hcap1 with ⟨hcap1_beq, hcap1_bne⟩
  rcases hcap2 with ⟨hcap2_beq, hcap2_bne⟩
  subst hP
  cases huc : v.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap1_beq hcap1_bne
    cases hp : v.sendingCt1 with
    | none =>
      simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
      rw [optCt1SentEkReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 136#64) none]
      apply SepWPp.of_sepWP (mid := entry + 1580#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optCt1SentEkReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        ← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 136#64) none, ← huc, ← hp]
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 b abs entry hfn sp (.ekReceivedCt1Sampled v) hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
        (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hp,
          optCt1SentEkReceivedPBFieldEncodedLen, optPolynomialEncoderPBFieldEncodedLen])
        ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
         by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
         by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
    | some p =>
      simp only [hp, Option.isSome_some, Bool.not_true] at hcap2_beq hcap2_bne
      rw [optCt1SentEkReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 136#64) (some p)]
      apply SepWPp.of_sepWP (mid := entry + 976#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optCt1SentEkReceivedPBPinnedAt_eq A g.1 (a + 8#64) none,
        ← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 136#64) (some p), ← huc, ← hp]
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ekReceivedCt1Sampled_f2_some b A abs entry hfn hbl2 g a sp v p hp hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
        (by simp [arm64_norm, hx0])
        (by simp [arm64_norm, huc, optCt1SentEkReceivedPBFieldEncodedLen])
        ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
         by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
         by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
        rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
          hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap1_beq hcap1_bne
    have hu_fit : ct1SentEkReceivedPBEncodedLen u < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc,
        optCt1SentEkReceivedPBFieldEncodedLen] at hfit; omega
    have htot1_fit : optCt1SentEkReceivedPBFieldEncodedLen (some u) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc] at hfit; omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
    rw [optCt1SentEkReceivedPBPinnedAt_eq A g.1 (a + 8#64) (some u)]
    apply SepWPp.of_sepWP (mid := entry + 912#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optCt1SentEkReceivedPBPinnedAt_eq A g.1 (a + 8#64) (some u), ← huc]
    have hP_bl1 : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optCt1SentEkReceivedPBPinnedAt A g.1 (a + 8#64) v.uc ∗
        optPolynomialEncoderPBPinnedAt A g.2 (a + 136#64) v.sendingCt1 ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((ct1SentEkReceivedPBPinnedAt A g.1 (a + 8#64) u ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
          optPolynomialEncoderPBPinnedAt A g.2 (a + 136#64) v.sendingCt1 ∗ F)) := by
      simp only [huc, optCt1SentEkReceivedPBPinnedAt]; ac_rfl
    apply SepWPp.congr_pre hP_bl1
    refine hbl1 (s0.readReg64 .lr) g.1 (a + 8#64) (sp - 32#64) u _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hu_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPp.congr_pre hP_bl1.symm
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
    have hf1_eq := bv_optMsgField_some (inner := ct1SentEkReceivedPBEncodedLen u)
      (tot := optCt1SentEkReceivedPBFieldEncodedLen (some u)) rfl
    have hvlen1_lt : varintLen (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u)) <
        optCt1SentEkReceivedPBFieldEncodedLen (some u) := by
      simp only [optCt1SentEkReceivedPBFieldEncodedLen]; omega
    have ⟨hule_f1, hule_f1_rev, hult_f1, hsub_f1, hbeq_f1⟩ := cmp_ls_false_of_lt hvlen1_lt htot1_fit
    have hult_f1_fwd := ult_of_lt_of_fit hvlen1_lt htot1_fit
    cases hp : v.sendingCt1 with
    | none =>
      simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
      rw [optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 136#64) none]
      apply SepWPp.of_sepWP (mid := entry + 1580#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 136#64) none, ← hp]
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 b abs entry hfn sp (.ekReceivedCt1Sampled v) hfit
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
      rw [optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 136#64) (some p)]
      apply SepWPp.of_sepWP (mid := entry + 976#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← optPolynomialEncoderPBPinnedAt_eq A g.2 (a + 136#64) (some p), ← hp]
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ekReceivedCt1Sampled_f2_some b A abs entry hfn hbl2 g a sp v p hp hfit
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

/-! ## 7. Branch `k = 5` (`.noHeaderReceived`, `+712..+728`, `+1072..+1184`, `+1544..+1552`) -/

/-- Merged continuation at `+1128` for `.noHeaderReceived` (`X0 = a + 48#64`, `X19 = uc_len`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_noHeaderReceived_f2 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hbl2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1140
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (g : PolynomialDecoderPBGhost × Unchunked2PBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.NoHeaderReceived)
    (hfit : v1StatePBEncodedLen ⟨some (.noHeaderReceived v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 1128#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a + 48#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 (optNoHeaderReceivedPBFieldEncodedLen v.uc))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap2 : (optPolyDecCap g.1 v.receivingHdr + 1#64 == 0#64) = !v.receivingHdr.isSome ∧
             (optPolyDecCap g.1 v.receivingHdr + 1#64 != 0#64) = v.receivingHdr.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optPolynomialDecoderPBPinnedAt A g.1 (a + 8#64) v.receivingHdr ∗
      optNoHeaderReceivedPBPinnedAt A g.2 (a + 48#64) v.uc ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.noHeaderReceived v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1128 1140
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1144 1188
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1544 1556
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  rcases hcap2 with ⟨hcap2_beq, hcap2_bne⟩
  subst hP
  cases hp : v.receivingHdr with
  | none =>
    simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
    rw [optPolynomialDecoderPBPinnedAt_eq A g.1 (a + 8#64) none]
    apply SepWPp.of_sepWP (mid := entry + 1580#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optPolynomialDecoderPBPinnedAt_eq A g.1 (a + 8#64) none, ← hp]
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 b abs entry hfn sp (.noHeaderReceived v) hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
      (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, hp,
        optPolynomialDecoderPBFieldEncodedLen, hx19])
      ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
       by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
      rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some p =>
    simp only [hp, Option.isSome_some, Bool.not_true] at hcap2_beq hcap2_bne
    have hp_fit : polynomialDecoderPBEncodedLen p < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp,
        optPolynomialDecoderPBFieldEncodedLen] at hfit; omega
    have htot_fit : optPolynomialDecoderPBFieldEncodedLen (some p) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp] at hfit; omega
    have hsum_fit : v1StateInnerPayloadEncodedLen (.noHeaderReceived v) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen] at hfit; omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
    rw [optPolynomialDecoderPBPinnedAt_eq A g.1 (a + 8#64) (some p)]
    apply SepWPp.of_sepWP (mid := entry + 1140#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optPolynomialDecoderPBPinnedAt_eq A g.1 (a + 8#64) (some p), ← hp]
    have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optPolynomialDecoderPBPinnedAt A g.1 (a + 8#64) v.receivingHdr ∗
        optNoHeaderReceivedPBPinnedAt A g.2 (a + 48#64) v.uc ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((polynomialDecoderPBPinnedAt A g.1 (a + 8#64) p ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
          optNoHeaderReceivedPBPinnedAt A g.2 (a + 48#64) v.uc ∗ F)) := by
      simp only [hp, optPolynomialDecoderPBPinnedAt]; ac_rfl
    apply SepWPp.congr_pre hP_bl
    refine hbl2 (s0.readReg64 .lr) g.1 (a + 8#64) (sp - 32#64) p _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hp_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPp.congr_pre hP_bl.symm
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
        (b := optNoHeaderReceivedPBFieldEncodedLen v.uc)
        (c := v1StateInnerPayloadEncodedLen (.noHeaderReceived v))
        (by simp only [v1StateInnerPayloadEncodedLen, hp])
        hsum_fit
    apply SepWPp.of_sepWP (mid := entry + 1580#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 b abs entry hfn sp (.noHeaderReceived v) hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
      (by simp [arm64_norm, hf2_eq, hx0_1, h19_1, hx19, hadd_sum])
      ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
       by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
       by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
       by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
       by simp [arm64_norm, h28_1, h28]⟩
      rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 5` (`.noHeaderReceived`, `+712`): steps from `entry + 712#64` to `s0.readReg64 .lr`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_noHeaderReceived (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hbl1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1076
      (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1140
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (g : PolynomialDecoderPBGhost × Unchunked2PBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.NoHeaderReceived)
    (hfit : v1StatePBEncodedLen ⟨some (.noHeaderReceived v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 712#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap1 : (optNoHeaderReceivedCap g.2 v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
             (optNoHeaderReceivedCap g.2 v.uc + 2#64 != 0#64) = v.uc.isSome)
    (hcap2 : (optPolyDecCap g.1 v.receivingHdr + 1#64 == 0#64) = !v.receivingHdr.isSome ∧
             (optPolyDecCap g.1 v.receivingHdr + 1#64 != 0#64) = v.receivingHdr.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optPolynomialDecoderPBPinnedAt A g.1 (a + 8#64) v.receivingHdr ∗
      optNoHeaderReceivedPBPinnedAt A g.2 (a + 48#64) v.uc ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.noHeaderReceived v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 712 732
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1072 1076
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1080 1128
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  rcases hcap1 with ⟨hcap1_beq, hcap1_bne⟩
  subst hP
  cases huc : v.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap1_beq hcap1_bne
    rw [optNoHeaderReceivedPBPinnedAt_eq A g.2 (a + 48#64) none]
    apply SepWPp.of_sepWP (mid := entry + 1128#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optNoHeaderReceivedPBPinnedAt_eq A g.2 (a + 48#64) none, ← huc]
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_noHeaderReceived_f2 b A abs entry hfn hbl2 g a sp v hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
      (by simp [arm64_norm, hx0])
      (by simp [arm64_norm, huc, optNoHeaderReceivedPBFieldEncodedLen])
      ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
       by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
      hcap2 rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap1_beq hcap1_bne
    have hu_fit : noHeaderReceivedPBEncodedLen u < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc,
        optNoHeaderReceivedPBFieldEncodedLen] at hfit; omega
    have htot1_fit : optNoHeaderReceivedPBFieldEncodedLen (some u) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc] at hfit; omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
    rw [optNoHeaderReceivedPBPinnedAt_eq A g.2 (a + 48#64) (some u)]
    apply SepWPp.of_sepWP (mid := entry + 1076#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optNoHeaderReceivedPBPinnedAt_eq A g.2 (a + 48#64) (some u), ← huc]
    have hP_bl1 : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optPolynomialDecoderPBPinnedAt A g.1 (a + 8#64) v.receivingHdr ∗
        optNoHeaderReceivedPBPinnedAt A g.2 (a + 48#64) v.uc ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((noHeaderReceivedPBPinnedAt A g.2 (a + 48#64) u ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
          optPolynomialDecoderPBPinnedAt A g.1 (a + 8#64) v.receivingHdr ∗ F)) := by
      simp only [huc, optNoHeaderReceivedPBPinnedAt]; ac_rfl
    apply SepWPp.congr_pre hP_bl1
    refine hbl1 (s0.readReg64 .lr) g.2 (a + 48#64) (sp - 32#64) u _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hu_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPp.congr_pre hP_bl1.symm
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
    have hf1_eq := bv_optMsgField_some (inner := noHeaderReceivedPBEncodedLen u)
      (tot := optNoHeaderReceivedPBFieldEncodedLen (some u)) rfl
    have hvlen1_lt : varintLen (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u)) <
        optNoHeaderReceivedPBFieldEncodedLen (some u) := by
      simp only [optNoHeaderReceivedPBFieldEncodedLen]; omega
    have ⟨hule_f1, hule_f1_rev, hult_f1, hsub_f1, hbeq_f1⟩ := cmp_ls_false_of_lt hvlen1_lt htot1_fit
    have hult_f1_fwd := ult_of_lt_of_fit hvlen1_lt htot1_fit
    apply SepWPp.of_sepWP (mid := entry + 1128#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_noHeaderReceived_f2 b A abs entry hfn hbl2 g a sp v hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
      (by simp [arm64_norm, h19_1, hx0])
      (by simp [arm64_norm, huc, hf1_eq, hx0_1])
      ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
       by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
       by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
       by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
       by simp [arm64_norm, h28_1, h28]⟩
      hcap2 rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-! ## 8. Branch `k = 10` (`.ct2Sampled`, `+868..+884`, `+1188..+1300`, `+1568..+1576`) -/

/-- Merged continuation at `+1244` for `.ct2Sampled` (`X0 = a + 64#64`, `X19 = uc_len`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ct2Sampled_f2 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hbl2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1256
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (g : PolynomialEncoderPBGhost × Unchunked2PBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.Ct2Sampled)
    (hfit : v1StatePBEncodedLen ⟨some (.ct2Sampled v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 1244#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a + 64#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 (optCt2SentPBFieldEncodedLen v.uc))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap2 : (optPolyEncCap g.1 v.sendingCt2 + 1#64 == 0#64) = !v.sendingCt2.isSome ∧
             (optPolyEncCap g.1 v.sendingCt2 + 1#64 != 0#64) = v.sendingCt2.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optPolynomialEncoderPBPinnedAt A g.1 (a + 8#64) v.sendingCt2 ∗
      optCt2SentPBPinnedAt A g.2 (a + 64#64) v.uc ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ct2Sampled v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1244 1256
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1260 1304
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1568 1580
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  rcases hcap2 with ⟨hcap2_beq, hcap2_bne⟩
  subst hP
  cases hp : v.sendingCt2 with
  | none =>
    simp only [hp, Option.isSome_none, Bool.not_false] at hcap2_beq hcap2_bne
    rw [optPolynomialEncoderPBPinnedAt_eq A g.1 (a + 8#64) none]
    apply SepWPp.of_sepWP (mid := entry + 1580#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optPolynomialEncoderPBPinnedAt_eq A g.1 (a + 8#64) none, ← hp]
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 b abs entry hfn sp (.ct2Sampled v) hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
      (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, hp,
        optPolynomialEncoderPBFieldEncodedLen, hx19])
      ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
       by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
      rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some p =>
    simp only [hp, Option.isSome_some, Bool.not_true] at hcap2_beq hcap2_bne
    have hp_fit : polynomialEncoderPBEncodedLen p < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp,
        optPolynomialEncoderPBFieldEncodedLen] at hfit; omega
    have htot_fit : optPolynomialEncoderPBFieldEncodedLen (some p) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, hp] at hfit; omega
    have hsum_fit : v1StateInnerPayloadEncodedLen (.ct2Sampled v) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen] at hfit; omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
    rw [optPolynomialEncoderPBPinnedAt_eq A g.1 (a + 8#64) (some p)]
    apply SepWPp.of_sepWP (mid := entry + 1256#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optPolynomialEncoderPBPinnedAt_eq A g.1 (a + 8#64) (some p), ← hp]
    have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optPolynomialEncoderPBPinnedAt A g.1 (a + 8#64) v.sendingCt2 ∗
        optCt2SentPBPinnedAt A g.2 (a + 64#64) v.uc ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((polynomialEncoderPBPinnedAt A g.1 (a + 8#64) p ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
          optCt2SentPBPinnedAt A g.2 (a + 64#64) v.uc ∗ F)) := by
      simp only [hp, optPolynomialEncoderPBPinnedAt]; ac_rfl
    apply SepWPp.congr_pre hP_bl
    refine hbl2 (s0.readReg64 .lr) g.1 (a + 8#64) (sp - 32#64) p _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hp_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPp.congr_pre hP_bl.symm
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
        (b := optCt2SentPBFieldEncodedLen v.uc)
        (c := v1StateInnerPayloadEncodedLen (.ct2Sampled v))
        (by simp only [v1StateInnerPayloadEncodedLen, hp])
        hsum_fit
    apply SepWPp.of_sepWP (mid := entry + 1580#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_tail_1580 b abs entry hfn sp (.ct2Sampled v) hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
      (by simp [arm64_norm, hf2_eq, hx0_1, h19_1, hx19, hadd_sum])
      ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
       by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
       by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
       by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
       by simp [arm64_norm, h28_1, h28]⟩
      rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 10` (`.ct2Sampled`, `+868`): steps from `entry + 868#64` to `s0.readReg64 .lr`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ct2Sampled (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hbl1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1192
      (ct2SentPBPinnedAt A) ct2SentPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1256
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (g : PolynomialEncoderPBGhost × Unchunked2PBGhost) (a sp : BitVec 64)
    (v : V1State.Chunked.Ct2Sampled)
    (hfit : v1StatePBEncodedLen ⟨some (.ct2Sampled v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 868#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap1 : (optCt2SentCap g.2 v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
             (optCt2SentCap g.2 v.uc + 2#64 != 0#64) = v.uc.isSome)
    (hcap2 : (optPolyEncCap g.1 v.sendingCt2 + 1#64 == 0#64) = !v.sendingCt2.isSome ∧
             (optPolyEncCap g.1 v.sendingCt2 + 1#64 != 0#64) = v.sendingCt2.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optPolynomialEncoderPBPinnedAt A g.1 (a + 8#64) v.sendingCt2 ∗
      optCt2SentPBPinnedAt A g.2 (a + 64#64) v.uc ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ct2Sampled v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 868 888
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1188 1192
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 1196 1244
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  rcases hcap1 with ⟨hcap1_beq, hcap1_bne⟩
  subst hP
  cases huc : v.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap1_beq hcap1_bne
    rw [optCt2SentPBPinnedAt_eq A g.2 (a + 64#64) none]
    apply SepWPp.of_sepWP (mid := entry + 1244#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optCt2SentPBPinnedAt_eq A g.2 (a + 64#64) none, ← huc]
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ct2Sampled_f2 b A abs entry hfn hbl2 g a sp v hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
      (by simp [arm64_norm, hx0])
      (by simp [arm64_norm, huc, optCt2SentPBFieldEncodedLen])
      ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
       by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
      hcap2 rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap1_beq hcap1_bne
    have hu_fit : ct2SentPBEncodedLen u < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc,
        optCt2SentPBFieldEncodedLen] at hfit; omega
    have htot1_fit : optCt2SentPBFieldEncodedLen (some u) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc] at hfit; omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by clear *- halign; bv_bits
    rw [optCt2SentPBPinnedAt_eq A g.2 (a + 64#64) (some u)]
    apply SepWPp.of_sepWP (mid := entry + 1192#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optCt2SentPBPinnedAt_eq A g.2 (a + 64#64) (some u), ← huc]
    have hP_bl1 : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optPolynomialEncoderPBPinnedAt A g.1 (a + 8#64) v.sendingCt2 ∗
        optCt2SentPBPinnedAt A g.2 (a + 64#64) v.uc ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((ct2SentPBPinnedAt A g.2 (a + 64#64) u ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
          optPolynomialEncoderPBPinnedAt A g.1 (a + 8#64) v.sendingCt2 ∗ F)) := by
      simp only [huc, optCt2SentPBPinnedAt]; ac_rfl
    apply SepWPp.congr_pre hP_bl1
    refine hbl1 (s0.readReg64 .lr) g.2 (a + 64#64) (sp - 32#64) u _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hu_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPp.congr_pre hP_bl1.symm
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
    have hf1_eq := bv_optMsgField_some (inner := ct2SentPBEncodedLen u)
      (tot := optCt2SentPBFieldEncodedLen (some u)) rfl
    have hvlen1_lt : varintLen (BitVec.ofNat 64 (ct2SentPBEncodedLen u)) <
        optCt2SentPBFieldEncodedLen (some u) := by
      simp only [optCt2SentPBFieldEncodedLen]; omega
    have ⟨hule_f1, hule_f1_rev, hult_f1, hsub_f1, hbeq_f1⟩ := cmp_ls_false_of_lt hvlen1_lt htot1_fit
    have hult_f1_fwd := ult_of_lt_of_fit hvlen1_lt htot1_fit
    apply SepWPp.of_sepWP (mid := entry + 1244#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ct2Sampled_f2 b A abs entry hfn hbl2 g a sp v hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
      (by simp [arm64_norm, h19_1, hx0])
      (by simp [arm64_norm, huc, hf1_eq, hx0_1])
      ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
       by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
       by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
       by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
       by simp [arm64_norm, h28_1, h28]⟩
      hcap2 rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

end CryptoVerification.SpqrV1.ProtoRepr
