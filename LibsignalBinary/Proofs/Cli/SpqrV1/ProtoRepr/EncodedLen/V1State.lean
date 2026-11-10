/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
public import LibsignalBinary.Proofs.CodeLayout
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSent
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPoly
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateBranches
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateBranchesB
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import ProofLib.SepLogic.WPp

/-!
# CLI `V1State::encoded_len` Top-Level Verification

Combines `.rodata` jump-table dispatch with the 11 variant branch proofs to establish top-level
`subroutine_ok` contracts for `<spqr::proto::pq_ratchet::V1State as
prost::message::Message>::encoded_len` on the CLI image.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux CryptoGames.LibsignalSession

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
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero

local notation "CalleeSaved20To28" => CryptoVerification.SpqrV1.ProtoRepr.V1CalleeSaved20To28

/-! ## 1. `.rodata` Jump-Table Decomposition and Option Cap Bound Wrappers -/

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.hasJumpTableAddr_local1 (b : BitVec 64) (abs : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64) :
    HasJumpTableAddr b abs
      ((tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLenLocal1Name)
      (b + bv% (ls_xref% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56) (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60))) := by
  refine ⟨_, _,
    libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics abs) (k := 56)
      (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") (by decide) (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56)),
    libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics abs) (k := 60)
      (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") (by decide) (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60)),
    ?_⟩
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]")]
  dsimp [Int64.toBitVec, Int64.ofBitVec]
  clear *- hb
  bv_kernel

/-- Steps the `none` path (`+0..+36`) from `entry` to `s0.readReg64 .lr`, returning `X0 = 0`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_none (b : BitVec 64)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (a sp v32 v24 v16 : BitVec 64)
    {s0 : State} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = a)
    (hmem : P = (((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ Rest ∗ (a ↦₆₄ noneCap2)))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s0 sf →
      Q sf (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ Rest ∗ (a ↦₆₄ noneCap2))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s0 P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 0 40
  subst hmem
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by rw [hsp]; exact halign
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_kernel
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by epochEncLen_cc_close)

/-- Steps the `some` prologue (`+0..+64`) up to the jump-table `ADR X10, #16` instruction,
    storing `X29, X30, X19` on the stack, computing the jump-table index in `X8`, and loading
    `roBase` into `X9`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_prologue_to_64 (b : BitVec 64)
    (abs : String → Option (State → State)) (entry roBase : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hjt : HasJumpTableAddr b abs entry roBase)
    (a sp w v32 v24 v16 : BitVec 64)
    {s0 : State} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = a)
    (hw_beq : (w + 2#64 == 0#64) = false)
    (hw_bne : (w + 2#64 != 0#64) = true)
    (hmem : P = (((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ Rest ∗ (a ↦₆₄ w)))
    (hnext : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = entry + 64#64 → s1.status = .Running → s1.sp = sp - 32#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = a →
      s1.readReg64 .x8 =
        (if BitVec.ult (w ^^^ 0x8000000000000000#64) 11#64
         then w ^^^ 0x8000000000000000#64 else 7#64) →
      s1.readReg64 .x9 = roBase →
      (s1.readReg64 .x19 = s0.readReg64 .x19 ∧ CalleeSaved20To28 s1 s0) →
      P1 = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ Rest ∗ (a ↦₆₄ w)) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s1 P1 Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s0 P Q Qp := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 0 56
  rcases hjt with ⟨pageOff, loOff, hf56, hf60, hro⟩
  subst hmem
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by rw [hsp]; exact halign
  have hsp_sub_align : (s0.sp - 32#64) &&& 15#64 = 0#64 := by
    rw [hsp]; clear *- halign; bv_kernel
  apply SepWPp.of_sepWP (mid := entry + 64#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hsp]) (by simp [arm64_norm])
    (by simp [arm64_norm, hx0])
    (by simp [arm64_norm])
    (by simp [arm64_norm, ← hro, ← BitVec.add_assoc])
    ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
     by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
     by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
     by simp [arm64_norm], by simp [arm64_norm]⟩
    rfl

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1State_entry_ro_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry roBase : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsV1StateEntry b abs entry)
    (hjt : HasJumpTableAddr b abs entry roBase)
    (hbl_ku : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1024
      (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen polyEncodedLenStack)
    (hbl_ks1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 600
      (headerSentPBPinnedAt A) headerSentPBEncodedLen polyEncodedLenStack)
    (hbl_ks2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 664
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl_hs : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 376
      (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen chunkedEncodedLenStack)
    (hbl_cr1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 408
      (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_cr2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 472
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl_escr1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 124
      (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_escr2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 188
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_nhr1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1076
      (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_nhr2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1140
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_hr1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 756
      (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_hr2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 820
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_cs : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 520
      (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen chunkedEncodedLenStack)
    (hbl_ercs1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 912
      (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_ercs2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 976
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl_ca1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 260
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (hbl_ca2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 324
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_c2s1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1192
      (ct2SentPBPinnedAt A) ct2SentPBEncodedLen polyEncodedLenStack)
    (hbl_c2s2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1256
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack) :
    subroutine_ok (tripleRatchetProgAtExt b abs) entry (v1StateEncodedLenRoPinnedSpec A roBase) := by
  v1State_fetches_range_cli b (Rust.withPanics abs) entry hfn 64 80
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, m⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [v1StateEncodedLenRoPinnedSpec, v1StateJumpTableBytes_eq,
    stackAt_v1StateEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v32, v24, v16, v8, ⟨hx0, hfit⟩, hpre⟩
  refine ⟨((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
      stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
      v1StateJumpTableBytesAt roBase ∗
      v1StatePBPinnedAt A g a m ∗ R, emp,
    by rw [sepConj_emp]; convert hpre using 1; ac_rfl, ?_⟩
  rcases m with ⟨inner⟩
  cases inner with
  | none =>
    have hP_eq (u32 u24 u16 : BitVec 64) :
        (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
          ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
          stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
          v1StateJumpTableBytesAt roBase ∗
          v1StatePBPinnedAt A g a ⟨none⟩ ∗ R) =
        (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
          ((s0.sp - 16#64) ↦₆₄ u16) ∗
          (((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt roBase ∗ memRegion (a + 8#64) 216 ∗ R) ∗
          (a ↦₆₄ noneCap2)) := by
      dsimp only [v1StatePBPinnedAt]; ac_rfl
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_none b abs entry hfn a s0.sp v32 v24 v16
      hpc0 hrun rfl halign hx0 (hP_eq v32 v24 v16) ?_
    intro sf hpcf hrunf hspf htrf hx0f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
    exact v1State_post_of_body A roBase a g ⟨none⟩ R s0 sf _ _ _ v8 hx0f htrf hm_f
  | some is =>
    cases is with
    | keysUnsampled v =>
      have hcap : (optKeysUnsampledCap g.a.gKeysUnsampled v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
          (optKeysUnsampledCap g.a.gKeysUnsampled v.uc + 2#64 != 0#64) = v.uc.isSome := by
        apply optKeysUnsampledPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000000#64) ∗
            memRegion (a + 64#64) 160 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt roBase ∗
            v1StatePBPinnedAt A g a ⟨some (.keysUnsampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optKeysUnsampledPBPinnedAt A g.a.gKeysUnsampled (a + 8#64) v.uc ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt roBase ∗ memRegion (a + 64#64) 160 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000000#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_prologue_to_64 b abs entry roBase hfn hjt
        a s0.sp 0x8000000000000000#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to entry 80 s1 0#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_keysUnsampled b A abs entry hfn hbl_ku g.a.gKeysUnsampled a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A roBase a g ⟨some (.keysUnsampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | keysSampled v =>
      have hcap1 : (optHeaderSentCap g.a.gKeysSampled.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optHeaderSentCap g.a.gKeysSampled.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optHeaderSentPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000001#64) ∗
            optPolynomialEncoderPBPinnedAt A g.a.gKeysSampled.2 (a + 112#64) v.sendingHdr ∗
            memRegion (a + 168#64) 56 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyEncCap g.a.gKeysSampled.2 v.sendingHdr + 1#64 == 0#64) = !v.sendingHdr.isSome ∧
          (optPolyEncCap g.a.gKeysSampled.2 v.sendingHdr + 1#64 != 0#64) = v.sendingHdr.isSome := by
        apply optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 112#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000001#64) ∗
            optHeaderSentPBPinnedAt A g.a.gKeysSampled.1 (a + 8#64) v.uc ∗
            memRegion (a + 168#64) 56 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt roBase ∗
            v1StatePBPinnedAt A g a ⟨some (.keysSampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optHeaderSentPBPinnedAt A g.a.gKeysSampled.1 (a + 8#64) v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.a.gKeysSampled.2 (a + 112#64) v.sendingHdr ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt roBase ∗ memRegion (a + 168#64) 56 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000001#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_prologue_to_64 b abs entry roBase hfn hjt
        a s0.sp 0x8000000000000001#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to entry 576 s1 1#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_keysSampled b A abs entry hfn hbl_ks1 hbl_ks2 g.a.gKeysSampled a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A roBase a g ⟨some (.keysSampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | headerSent v =>
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt roBase ∗
            v1StatePBPinnedAt A g a ⟨some (.headerSent v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (chunkedHeaderSentPBPinnedAt A g.a.gHeaderSent (a + 8#64) v ∗
              stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
              (v1StateJumpTableBytesAt roBase ∗ memRegion (a + 184#64) 40 ∗
                ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000002#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]; ac_rfl
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_prologue_to_64 b abs entry roBase hfn hjt
        a s0.sp 0x8000000000000002#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to entry 372 s1 2#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_headerSent b A abs entry hfn hbl_hs g.a.gHeaderSent a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A roBase a g ⟨some (.headerSent v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ct1Received v =>
      have hcap1 : (optEkSentCt1ReceivedCap g.a.gCt1Received.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optEkSentCt1ReceivedCap g.a.gCt1Received.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optEkSentCt1ReceivedPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000003#64) ∗
            optPolynomialEncoderPBPinnedAt A g.a.gCt1Received.2 (a + 112#64) v.sendingEk ∗
            memRegion (a + 168#64) 56 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyEncCap g.a.gCt1Received.2 v.sendingEk + 1#64 == 0#64) = !v.sendingEk.isSome ∧
          (optPolyEncCap g.a.gCt1Received.2 v.sendingEk + 1#64 != 0#64) = v.sendingEk.isSome := by
        apply optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 112#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000003#64) ∗
            optEkSentCt1ReceivedPBPinnedAt A g.a.gCt1Received.1 (a + 8#64) v.uc ∗
            memRegion (a + 168#64) 56 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt roBase ∗
            v1StatePBPinnedAt A g a ⟨some (.ct1Received v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optEkSentCt1ReceivedPBPinnedAt A g.a.gCt1Received.1 (a + 8#64) v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.a.gCt1Received.2 (a + 112#64) v.sendingEk ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt roBase ∗ memRegion (a + 168#64) 56 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000003#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_prologue_to_64 b abs entry roBase hfn hjt
        a s0.sp 0x8000000000000003#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to entry 384 s1 3#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ct1Received b A abs entry hfn hbl_cr1 hbl_cr2 g.a.gCt1Received a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A roBase a g ⟨some (.ct1Received v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ekSentCt1Received v =>
      have hcap1 : (optEkSentCt1ReceivedCap g.a.gEkSentCt1Received.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optEkSentCt1ReceivedCap g.a.gEkSentCt1Received.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optEkSentCt1ReceivedPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000004#64) ∗
            optPolynomialDecoderPBPinnedAt A g.a.gEkSentCt1Received.2 (a + 112#64) v.receivingCt2 ∗
            memRegion (a + 152#64) 72 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyDecCap g.a.gEkSentCt1Received.2 v.receivingCt2 + 1#64 == 0#64) = !v.receivingCt2.isSome ∧
          (optPolyDecCap g.a.gEkSentCt1Received.2 v.receivingCt2 + 1#64 != 0#64) = v.receivingCt2.isSome := by
        apply optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 112#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000004#64) ∗
            optEkSentCt1ReceivedPBPinnedAt A g.a.gEkSentCt1Received.1 (a + 8#64) v.uc ∗
            memRegion (a + 152#64) 72 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt roBase ∗
            v1StatePBPinnedAt A g a ⟨some (.ekSentCt1Received v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optEkSentCt1ReceivedPBPinnedAt A g.a.gEkSentCt1Received.1 (a + 8#64) v.uc ∗
              optPolynomialDecoderPBPinnedAt A g.a.gEkSentCt1Received.2 (a + 112#64) v.receivingCt2 ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt roBase ∗ memRegion (a + 152#64) 72 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000004#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_prologue_to_64 b abs entry roBase hfn hjt
        a s0.sp 0x8000000000000004#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to entry 100 s1 4#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ekSentCt1Received b A abs entry hfn hbl_escr1 hbl_escr2 g.a.gEkSentCt1Received a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A roBase a g ⟨some (.ekSentCt1Received v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | noHeaderReceived v =>
      have hcap1 : (optNoHeaderReceivedCap g.a.gNoHeaderReceived.2 v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
          (optNoHeaderReceivedCap g.a.gNoHeaderReceived.2 v.uc + 2#64 != 0#64) = v.uc.isSome := by
        apply optNoHeaderReceivedPBPinnedAt_cap_bounds (p := a + 48#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000005#64) ∗
            optPolynomialDecoderPBPinnedAt A g.a.gNoHeaderReceived.1 (a + 8#64) v.receivingHdr ∗
            memRegion (a + 104#64) 120 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyDecCap g.a.gNoHeaderReceived.1 v.receivingHdr + 1#64 == 0#64) = !v.receivingHdr.isSome ∧
          (optPolyDecCap g.a.gNoHeaderReceived.1 v.receivingHdr + 1#64 != 0#64) = v.receivingHdr.isSome := by
        apply optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000005#64) ∗
            optNoHeaderReceivedPBPinnedAt A g.a.gNoHeaderReceived.2 (a + 48#64) v.uc ∗
            memRegion (a + 104#64) 120 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt roBase ∗
            v1StatePBPinnedAt A g a ⟨some (.noHeaderReceived v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optPolynomialDecoderPBPinnedAt A g.a.gNoHeaderReceived.1 (a + 8#64) v.receivingHdr ∗
              optNoHeaderReceivedPBPinnedAt A g.a.gNoHeaderReceived.2 (a + 48#64) v.uc ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt roBase ∗ memRegion (a + 104#64) 120 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000005#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_prologue_to_64 b abs entry roBase hfn hjt
        a s0.sp 0x8000000000000005#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to entry 712 s1 5#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_noHeaderReceived b A abs entry hfn hbl_nhr1 hbl_nhr2 g.a.gNoHeaderReceived a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A roBase a g ⟨some (.noHeaderReceived v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | headerReceived v =>
      have hcap1 : (optHeaderReceivedCap g.b.gHeaderReceived.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optHeaderReceivedCap g.b.gHeaderReceived.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optHeaderReceivedPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000006#64) ∗
            optPolynomialDecoderPBPinnedAt A g.b.gHeaderReceived.2 (a + 88#64) v.receivingEk ∗
            memRegion (a + 128#64) 96 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyDecCap g.b.gHeaderReceived.2 v.receivingEk + 1#64 == 0#64) = !v.receivingEk.isSome ∧
          (optPolyDecCap g.b.gHeaderReceived.2 v.receivingEk + 1#64 != 0#64) = v.receivingEk.isSome := by
        apply optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 88#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000006#64) ∗
            optHeaderReceivedPBPinnedAt A g.b.gHeaderReceived.1 (a + 8#64) v.uc ∗
            memRegion (a + 128#64) 96 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt roBase ∗
            v1StatePBPinnedAt A g a ⟨some (.headerReceived v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optHeaderReceivedPBPinnedAt A g.b.gHeaderReceived.1 (a + 8#64) v.uc ∗
              optPolynomialDecoderPBPinnedAt A g.b.gHeaderReceived.2 (a + 88#64) v.receivingEk ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt roBase ∗ memRegion (a + 128#64) 96 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000006#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_prologue_to_64 b abs entry roBase hfn hjt
        a s0.sp 0x8000000000000006#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to entry 732 s1 6#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_headerReceived b A abs entry hfn hbl_hr1 hbl_hr2 g.b.gHeaderReceived a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A roBase a g ⟨some (.headerReceived v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ct1Sampled v =>
      have ⟨hw_beq, hw_bne, hw_ult⟩ :
          (optCt1SentCap g.b.gCt1Sampled.uc v.uc + 2#64 == 0#64) = false ∧
          (optCt1SentCap g.b.gCt1Sampled.uc v.uc + 2#64 != 0#64) = true ∧
          ((optCt1SentCap g.b.gCt1Sampled.uc v.uc ^^^ 0x8000000000000000#64).ult 11#64) = false := by
        apply optCt1SentRest_disc_bounds (p := a)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc) ∗
            optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (a + 128#64) v.sendingCt1 ∗
            optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (a + 184#64) v.receivingEk ∗
            ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
            ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt, chunkedCt1SampledPBPinnedAt] at hpre
        rw [optCt1SentPBPinnedAt_eq] at hpre
        convert hpre using 1; ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt roBase ∗
            v1StatePBPinnedAt A g a ⟨some (.ct1Sampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optCt1SentRest A g.b.gCt1Sampled.uc a v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (a + 128#64) v.sendingCt1 ∗
              optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (a + 184#64) v.receivingEk ∗
              stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
              (v1StateJumpTableBytesAt roBase ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt, chunkedCt1SampledPBPinnedAt]
        rw [optCt1SentPBPinnedAt_eq]; ac_rfl
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_prologue_to_64 b abs entry roBase hfn hjt
        a s0.sp (optCt1SentCap g.b.gCt1Sampled.uc v.uc) v32 v24 v16
        hpc0 hrun rfl halign hx0 hw_beq hw_bne (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to entry 520 s1 7#64 (by rw [hx8_1, hw_ult]; rfl)
      rw [fold_v1StateJumpTableBytesAt]
      have hP_cs :
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
            (optCt1SentRest A g.b.gCt1Sampled.uc a v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (a + 128#64) v.sendingCt1 ∗
              optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (a + 184#64) v.receivingEk ∗
              stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
              (v1StateJumpTableBytesAt roBase ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc)) =
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
            chunkedCt1SampledPBPinnedAt A g.b.gCt1Sampled a v ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            (v1StateJumpTableBytesAt roBase ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) := by
        dsimp only [chunkedCt1SampledPBPinnedAt]
        rw [optCt1SentPBPinnedAt_eq]; ac_rfl
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ct1Sampled b A abs entry hfn hbl_cs g.b.gCt1Sampled a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hP_cs ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A roBase a g ⟨some (.ct1Sampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ekReceivedCt1Sampled v =>
      have hcap1 : (optCt1SentEkReceivedCap g.b.gEkReceivedCt1Sampled.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optCt1SentEkReceivedCap g.b.gEkReceivedCt1Sampled.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optCt1SentEkReceivedPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000008#64) ∗
            optPolynomialEncoderPBPinnedAt A g.b.gEkReceivedCt1Sampled.2 (a + 136#64) v.sendingCt1 ∗
            memRegion (a + 192#64) 32 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyEncCap g.b.gEkReceivedCt1Sampled.2 v.sendingCt1 + 1#64 == 0#64) = !v.sendingCt1.isSome ∧
          (optPolyEncCap g.b.gEkReceivedCt1Sampled.2 v.sendingCt1 + 1#64 != 0#64) = v.sendingCt1.isSome := by
        apply optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 136#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000008#64) ∗
            optCt1SentEkReceivedPBPinnedAt A g.b.gEkReceivedCt1Sampled.1 (a + 8#64) v.uc ∗
            memRegion (a + 192#64) 32 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt roBase ∗
            v1StatePBPinnedAt A g a ⟨some (.ekReceivedCt1Sampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optCt1SentEkReceivedPBPinnedAt A g.b.gEkReceivedCt1Sampled.1 (a + 8#64) v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.b.gEkReceivedCt1Sampled.2 (a + 136#64) v.sendingCt1 ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt roBase ∗ memRegion (a + 192#64) 32 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000008#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_prologue_to_64 b abs entry roBase hfn hjt
        a s0.sp 0x8000000000000008#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to entry 888 s1 8#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ekReceivedCt1Sampled b A abs entry hfn hbl_ercs1 hbl_ercs2 g.b.gEkReceivedCt1Sampled a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A roBase a g ⟨some (.ekReceivedCt1Sampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ct1Acknowledged v =>
      have hcap1 : (optCt1SentCap g.b.gCt1Acknowledged.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optCt1SentCap g.b.gCt1Acknowledged.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optCt1SentPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000009#64) ∗
            optPolynomialDecoderPBPinnedAt A g.b.gCt1Acknowledged.2 (a + 136#64) v.receivingEk ∗
            memRegion (a + 176#64) 48 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyDecCap g.b.gCt1Acknowledged.2 v.receivingEk + 1#64 == 0#64) = !v.receivingEk.isSome ∧
          (optPolyDecCap g.b.gCt1Acknowledged.2 v.receivingEk + 1#64 != 0#64) = v.receivingEk.isSome := by
        apply optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 136#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x8000000000000009#64) ∗
            optCt1SentPBPinnedAt A g.b.gCt1Acknowledged.1 (a + 8#64) v.uc ∗
            memRegion (a + 176#64) 48 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt roBase ∗
            v1StatePBPinnedAt A g a ⟨some (.ct1Acknowledged v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optCt1SentPBPinnedAt A g.b.gCt1Acknowledged.1 (a + 8#64) v.uc ∗
              optPolynomialDecoderPBPinnedAt A g.b.gCt1Acknowledged.2 (a + 136#64) v.receivingEk ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt roBase ∗ memRegion (a + 176#64) 48 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000009#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_prologue_to_64 b abs entry roBase hfn hjt
        a s0.sp 0x8000000000000009#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to entry 236 s1 9#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ct1Acknowledged b A abs entry hfn hbl_ca1 hbl_ca2 g.b.gCt1Acknowledged a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A roBase a g ⟨some (.ct1Acknowledged v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ct2Sampled v =>
      have hcap1 : (optCt2SentCap g.b.gCt2Sampled.2 v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
          (optCt2SentCap g.b.gCt2Sampled.2 v.uc + 2#64 != 0#64) = v.uc.isSome := by
        apply optCt2SentPBPinnedAt_cap_bounds (p := a + 64#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x800000000000000a#64) ∗
            optPolynomialEncoderPBPinnedAt A g.b.gCt2Sampled.1 (a + 8#64) v.sendingCt2 ∗
            memRegion (a + 120#64) 104 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyEncCap g.b.gCt2Sampled.1 v.sendingCt2 + 1#64 == 0#64) = !v.sendingCt2.isSome ∧
          (optPolyEncCap g.b.gCt2Sampled.1 v.sendingCt2 + 1#64 != 0#64) = v.sendingCt2.isSome := by
        apply optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt roBase ∗ (a ↦₆₄ 0x800000000000000a#64) ∗
            optCt2SentPBPinnedAt A g.b.gCt2Sampled.2 (a + 64#64) v.uc ∗
            memRegion (a + 120#64) 104 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt roBase ∗
            v1StatePBPinnedAt A g a ⟨some (.ct2Sampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optPolynomialEncoderPBPinnedAt A g.b.gCt2Sampled.1 (a + 8#64) v.sendingCt2 ∗
              optCt2SentPBPinnedAt A g.b.gCt2Sampled.2 (a + 64#64) v.uc ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt roBase ∗ memRegion (a + 120#64) 104 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x800000000000000a#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_prologue_to_64 b abs entry roBase hfn hjt
        a s0.sp 0x800000000000000a#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to entry 868 s1 10#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ct2Sampled b A abs entry hfn hbl_c2s1 hbl_c2s2 g.b.gCt2Sampled a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A roBase a g ⟨some (.ct2Sampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f

/-! ## 2. `.rodata` Jump-Table Facts and Top-Level Contracts -/

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLenLocal1Name)
    (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56) (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60))))

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLenLocal1Name)
    (v1StateEncodedLenRoSpec A (b + bv% (ls_xref% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56) (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60))))

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLenLocal1Name)
    (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56) (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60))))

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLenLocal1Name)
    (v1StateEncodedLenRoSpec A (b + bv% (ls_xref% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56) (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60))))

/-- Resolve a `BL` call in `V1State::encoded_len` from term-level `fnOff` and decode witnesses. -/
macro "v1State_bl_call_cli " b:term:max ext:term:max fnOff:term:max k:num dec:term:max
    tgtOff:term:max calleeOk:ident : tactic =>
  `(tactic| (have hf := libsignalSessionCode_fetch_fnAddr (b := $b) (H := Rust.withPanics $ext) (k := $k)
                 $fnOff (by decide) $dec
             exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                 (fun _ _ _ _ => rfl) hf (fnAddr_bl_target $fnOff $tgtOff) ($calleeOk $b _ $ext)))

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PinnedOkExt b A ext := by
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.v1State_entry_ro_pinned_ok_ext b A ext _ (b + bv% (ls_xref% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56) (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60)))
    (Or.inl rfl) (CryptoVerification.Cli.SpqrV1.ProtoRepr.hasJumpTableAddr_local1 b ext hb)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 1024 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 1024)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::KeysUnsampled as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.keysUnsampledEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 600 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 600)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderSent as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 664 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 664)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 376 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 376)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.chunkedHeaderSentEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 408 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 408)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 472 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 472)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 124 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 124)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 188 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 188)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 1076 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 1076)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::NoHeaderReceived as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.noHeaderReceivedEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 1140 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 1140)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 756 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 756)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.headerReceivedEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 820 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 820)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 520 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 520)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 912 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 912)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 976 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 976)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 260 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 260)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 324 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 324)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 1192 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 1192)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.ct2SentEncodedLen_local1_pinned_ok_ext
  · v1State_bl_call_cli b ext (ls_lemma% fnOff "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]") 1256 (ls_decode% spqrV1StateBinCli (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 1256)) (ls_lemma% fnOff "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]") CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_pinned_ok_ext

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1OkExt b A ext :=
  v1StateEncodedLen_ro_ok_of_pinned (CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_pinned_ok_ext b A ext hb)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PinnedOk b C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs) hb

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1Ok b C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs) hb

end CryptoVerification.SpqrV1.ProtoRepr
