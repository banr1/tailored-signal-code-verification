/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPoly
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateBranches
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateBranchesB
import ProofLib.SepLogic.WPp

/-!
# Verification of `V1State::encoded_len` (`0x3902c`, `0x67df8`)

Composes the jump-table prologue with all 11 inner-state variant branches to prove `subroutine_ok`
for `<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#1, #2]` and
their placed blocks (`177`, `405`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 Arm64.Obj ProofLib ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux CryptoGames.LibsignalSession
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

/-! ## 1. Jump-Table Address Fetch Bundle (`+56..+60`) -/

theorem hasJumpTableAddr_local1 (b : BitVec 64) (abs : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64) :
    HasJumpTableAddr b abs
      ((tripleRatchetProgAtExt b abs).fnAddr v1StateEncodedLenLocal1Name)
      (b + bv% (ls_xref% 0x39148 0x3914c)) := by
  refine ⟨_, _,
    libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics abs) (k := 56)
      libsignalSessionCode_fnOff_0x39110 (by decide) spqrV1StateBin_decode_0x39148,
    libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics abs) (k := 60)
      libsignalSessionCode_fnOff_0x39110 (by decide) spqrV1StateBin_decode_0x3914c,
    ?_⟩
  rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x39110]
  dsimp [BitVec.zeroExtend]
  clear *- hb
  bv_kernel

theorem hasJumpTableAddr_local2 (b : BitVec 64) (abs : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64) :
    HasJumpTableAddr b abs
      ((tripleRatchetProgAtExt b abs).fnAddr v1StateEncodedLenLocal2Name)
      (b + bv% (ls_xref% 0x62a38 0x62a3c)) := by
  refine ⟨_, _,
    libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics abs) (k := 56)
      libsignalSessionCode_fnOff_0x62a00 (by decide) spqrV1StateBin_decode_0x62a38,
    libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics abs) (k := 60)
      libsignalSessionCode_fnOff_0x62a00 (by decide) spqrV1StateBin_decode_0x62a3c,
    ?_⟩
  rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x62a00]
  dsimp [BitVec.zeroExtend]
  clear *- hb
  bv_kernel

/-! ## 2. Master Entry-Point Proof (`v1State_entry_ro_pinned_wp_p2`) -/

theorem v1State_entry_ro_pinned_wp_p2 (Φ : Memory → Prop) [FrozenInv Φ]
    (prog : Program) (A : RustAlloc) (entry roBase : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hjt : HasJumpTableStepP2 prog entry roBase)
    (hbl_ku : CallPinnedEncLenAtF Φ prog entry 1024
      (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen polyEncodedLenStack)
    (hbl_ks1 : CallPinnedEncLenAtF Φ prog entry 600
      (headerSentPBPinnedAt A) headerSentPBEncodedLen polyEncodedLenStack)
    (hbl_ks2 : CallPinnedEncLenAtF Φ prog entry 664
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl_hs : CallPinnedEncLenAtF Φ prog entry 376
      (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen chunkedEncodedLenStack)
    (hbl_cr1 : CallPinnedEncLenAtF Φ prog entry 408
      (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_cr2 : CallPinnedEncLenAtF Φ prog entry 472
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl_escr1 : CallPinnedEncLenAtF Φ prog entry 124
      (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_escr2 : CallPinnedEncLenAtF Φ prog entry 188
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_nhr1 : CallPinnedEncLenAtF Φ prog entry 1076
      (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_nhr2 : CallPinnedEncLenAtF Φ prog entry 1140
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_hr1 : CallPinnedEncLenAtF Φ prog entry 756
      (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_hr2 : CallPinnedEncLenAtF Φ prog entry 820
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_cs : CallPinnedEncLenAtF Φ prog entry 520
      (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen chunkedEncodedLenStack)
    (hbl_ercs1 : CallPinnedEncLenAtF Φ prog entry 912
      (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_ercs2 : CallPinnedEncLenAtF Φ prog entry 976
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl_ca1 : CallPinnedEncLenAtF Φ prog entry 260
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (hbl_ca2 : CallPinnedEncLenAtF Φ prog entry 324
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_c2s1 : CallPinnedEncLenAtF Φ prog entry 1192
      (ct2SentPBPinnedAt A) ct2SentPBEncodedLen polyEncodedLenStack)
    (hbl_c2s2 : CallPinnedEncLenAtF Φ prog entry 1256
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (x : V1StateEncodedLenPinnedGhost) (R : SepProp) (s0 : State)
    (hpc0 : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (v1StateEncodedLenRoPinnedSpec A roBase).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    ∃ P Fr, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPpF Φ prog (s0.readReg64 .lr) s0 P
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (v1StateEncodedLenRoPinnedSpec A roBase).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (v1StateEncodedLenRoPinnedSpec A roBase).onPanic x s0 sf ∗ R)) := by
  v1State_fetches_range hfn 64 80
  rcases x with ⟨a, g, m⟩
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
    refine step_v1State_none Φ prog entry hfn a s0.sp v32 v24 v16
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
      refine step_v1State_prologue_to_64 Φ prog entry roBase hfn hjt
        a s0.sp 0x8000000000000000#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F entry 80 s1 0#64 hx8_1
      refine step_v1State_keysUnsampled Φ prog A entry hfn hbl_ku g.a.gKeysUnsampled a s0.sp v hfit
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
      refine step_v1State_prologue_to_64 Φ prog entry roBase hfn hjt
        a s0.sp 0x8000000000000001#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F entry 576 s1 1#64 hx8_1
      refine step_v1State_keysSampled Φ prog A entry hfn hbl_ks1 hbl_ks2 g.a.gKeysSampled a s0.sp v hfit
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
      refine step_v1State_prologue_to_64 Φ prog entry roBase hfn hjt
        a s0.sp 0x8000000000000002#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F entry 372 s1 2#64 hx8_1
      refine step_v1State_headerSent Φ prog A entry hfn hbl_hs g.a.gHeaderSent a s0.sp v hfit
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
      refine step_v1State_prologue_to_64 Φ prog entry roBase hfn hjt
        a s0.sp 0x8000000000000003#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F entry 384 s1 3#64 hx8_1
      refine step_v1State_ct1Received Φ prog A entry hfn hbl_cr1 hbl_cr2 g.a.gCt1Received a s0.sp v hfit
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
      refine step_v1State_prologue_to_64 Φ prog entry roBase hfn hjt
        a s0.sp 0x8000000000000004#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F entry 100 s1 4#64 hx8_1
      refine step_v1State_ekSentCt1Received Φ prog A entry hfn hbl_escr1 hbl_escr2 g.a.gEkSentCt1Received a s0.sp v hfit
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
      refine step_v1State_prologue_to_64 Φ prog entry roBase hfn hjt
        a s0.sp 0x8000000000000005#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F entry 712 s1 5#64 hx8_1
      refine step_v1State_noHeaderReceived Φ prog A entry hfn hbl_nhr1 hbl_nhr2 g.a.gNoHeaderReceived a s0.sp v hfit
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
      refine step_v1State_prologue_to_64 Φ prog entry roBase hfn hjt
        a s0.sp 0x8000000000000006#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F entry 732 s1 6#64 hx8_1
      refine step_v1State_headerReceived Φ prog A entry hfn hbl_hr1 hbl_hr2 g.b.gHeaderReceived a s0.sp v hfit
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
      refine step_v1State_prologue_to_64 Φ prog entry roBase hfn hjt
        a s0.sp (optCt1SentCap g.b.gCt1Sampled.uc v.uc) v32 v24 v16
        hpc0 hrun rfl halign hx0 hw_beq hw_bne (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F entry 520 s1 7#64 (by rw [hx8_1, hw_ult]; rfl)
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
      refine step_v1State_ct1Sampled Φ prog A entry hfn hbl_cs g.b.gCt1Sampled a s0.sp v hfit
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
      refine step_v1State_prologue_to_64 Φ prog entry roBase hfn hjt
        a s0.sp 0x8000000000000008#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F entry 888 s1 8#64 hx8_1
      refine step_v1State_ekReceivedCt1Sampled Φ prog A entry hfn hbl_ercs1 hbl_ercs2 g.b.gEkReceivedCt1Sampled a s0.sp v hfit
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
      refine step_v1State_prologue_to_64 Φ prog entry roBase hfn hjt
        a s0.sp 0x8000000000000009#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F entry 236 s1 9#64 hx8_1
      refine step_v1State_ct1Acknowledged Φ prog A entry hfn hbl_ca1 hbl_ca2 g.b.gCt1Acknowledged a s0.sp v hfit
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
      refine step_v1State_prologue_to_64 Φ prog entry roBase hfn hjt
        a s0.sp 0x800000000000000a#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F entry 868 s1 10#64 hx8_1
      refine step_v1State_ct2Sampled Φ prog A entry hfn hbl_c2s1 hbl_c2s2 g.b.gCt2Sampled a s0.sp v hfit
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

theorem v1State_entry_ro_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry roBase : BitVec 64)
    (hfn : IsV1StateEntry b abs entry)
    (hjt : HasJumpTableAddr b abs entry roBase)
    (hbl_ku : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1024 (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen polyEncodedLenStack)
    (hbl_ks1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 600 (headerSentPBPinnedAt A) headerSentPBEncodedLen polyEncodedLenStack)
    (hbl_ks2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 664 (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl_hs : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 376 (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen chunkedEncodedLenStack)
    (hbl_cr1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 408 (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_cr2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 472 (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl_escr1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 124 (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_escr2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 188 (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_nhr1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1076 (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_nhr2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1140 (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_hr1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 756 (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_hr2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 820 (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_cs : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 520 (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen chunkedEncodedLenStack)
    (hbl_ercs1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 912 (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_ercs2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 976 (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl_ca1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 260 (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (hbl_ca2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 324 (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_c2s1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1192 (ct2SentPBPinnedAt A) ct2SentPBEncodedLen polyEncodedLenStack)
    (hbl_c2s2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b abs) entry 1256 (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack) :
    subroutine_ok (tripleRatchetProgAtExt b abs) entry (v1StateEncodedLenRoPinnedSpec A roBase) := by
  apply subroutine_ok_of_sepWPpF_true
  exact v1State_entry_ro_pinned_wp_p2 (fun _ => True) _ A entry roBase
    (Or.inl ⟨b, abs, rfl, hfn⟩) (hasJumpTableStepP2_of_addr hjt)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_ku)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_ks1)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_ks2)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_hs)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_cr1)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_cr2)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_escr1)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_escr2)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_nhr1)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_nhr2)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_hr1)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_hr2)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_cs)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_ercs1)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_ercs2)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_ca1)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_ca2)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_c2s1)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl_c2s2)

theorem v1State_entry_ro_pinned_lscl_ok (pl : MultiPlacement) (prog : Program) (A : RustAlloc)
    (entry roBase : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hjt : HasJumpTableStepP2 prog entry roBase)
    (hbl_ku : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 1024 (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen polyEncodedLenStack)
    (hbl_ks1 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 600 (headerSentPBPinnedAt A) headerSentPBEncodedLen polyEncodedLenStack)
    (hbl_ks2 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 664 (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl_hs : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 376 (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen chunkedEncodedLenStack)
    (hbl_cr1 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 408 (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_cr2 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 472 (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl_escr1 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 124 (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_escr2 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 188 (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_nhr1 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 1076 (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_nhr2 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 1140 (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_hr1 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 756 (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_hr2 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 820 (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_cs : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 520 (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen chunkedEncodedLenStack)
    (hbl_ercs1 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 912 (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen polyEncodedLenStack)
    (hbl_ercs2 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 976 (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl_ca1 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 260 (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (hbl_ca2 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 324 (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (hbl_c2s1 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 1192 (ct2SentPBPinnedAt A) ct2SentPBEncodedLen polyEncodedLenStack)
    (hbl_c2s2 : CallPinnedEncLenAtF (LibsignalCodeLoaded pl) prog entry 1256 (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack) :
    subroutine_ok prog entry (withLsCodeLoaded pl (v1StateEncodedLenRoPinnedSpec A roBase)) :=
  subroutine_ok_of_sepWPpF_lscl
    (v1State_entry_ro_pinned_wp_p2 (LibsignalCodeLoaded pl) prog A entry roBase hfn hjt
      hbl_ku hbl_ks1 hbl_ks2 hbl_hs hbl_cr1 hbl_cr2 hbl_escr1 hbl_escr2
      hbl_nhr1 hbl_nhr2 hbl_hr1 hbl_hr2 hbl_cs hbl_ercs1 hbl_ercs2 hbl_ca1 hbl_ca2 hbl_c2s1 hbl_c2s2)

/-! ## 3. `.rodata` Jump-Table Facts and Top-Level `[local#1]` / `[local#2]` Theorems -/

open ProofLib.ProgramReflection in
theorem rodata_0x7e53a_eq_v1StateJumpTable :
    (libsignalSessionImage.data.drop (num% (ls_xref% 0x39148 0x3914c) - num% (ls_xref% 0x2440 0x2444))).take 11 =
      v1StateJumpTableBytes := by
  rfl_kernel

open ProofLib.ProgramReflection in
theorem rodata_0x8245a_eq_v1StateJumpTable :
    (libsignalSessionImage.data.drop (num% (ls_xref% 0x62a38 0x62a3c) - num% (ls_xref% 0x2440 0x2444))).take 11 =
      v1StateJumpTableBytes := by
  rfl_kernel

open ProofLib.ProgramReflection in
theorem rodata_v1StateJumpTable_local1_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% 0x39148 0x3914c)) ↦ᵣ v1StateJumpTableBytes) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% 0x39148 0x3914c)) (secLen := 11) (dataOff := num% (ls_xref% 0x2440 0x2444))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x7e53a_eq_v1StateJumpTable] at h

open ProofLib.ProgramReflection in
theorem rodata_v1StateJumpTable_local2_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% 0x62a38 0x62a3c)) (secLen := 11) (dataOff := num% (ls_xref% 0x2440 0x2444))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x8245a_eq_v1StateJumpTable] at h

macro "v1State_bl_call " b:term:max ext:term:max fnOff:ident k:num dec:ident tgtOff:ident calleeOk:ident : term =>
  `(callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := $b) (H := Rust.withPanics $ext) (k := $k)
        $fnOff (by decide) $dec)
      (fnAddr_bl_target $fnOff $tgtOff)
      ($calleeOk $b _ $ext))

def V1StateEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr v1StateEncodedLenLocal1Name)
    (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x39148 0x3914c)))
def V1StateEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr v1StateEncodedLenLocal1Name)
    (v1StateEncodedLenRoSpec A (b + bv% (ls_xref% 0x39148 0x3914c)))
def V1StateEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr v1StateEncodedLenLocal1Name)
    (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x39148 0x3914c)))
def V1StateEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr v1StateEncodedLenLocal1Name)
    (v1StateEncodedLenRoSpec A (b + bv% (ls_xref% 0x39148 0x3914c)))

def V1StateEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr v1StateEncodedLenLocal2Name)
    (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))
def V1StateEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr v1StateEncodedLenLocal2Name)
    (v1StateEncodedLenRoSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))
def V1StateEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr v1StateEncodedLenLocal2Name)
    (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))
def V1StateEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr v1StateEncodedLenLocal2Name)
    (v1StateEncodedLenRoSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))

def V1StateEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_177).rebase (blkPl_177).base (Rust.withPanics ext)) (blkPl_177).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A (lsρ v1StateJtSymLocal1)))
def V1StateEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_177).rebase (blkPl_177).base (Rust.withPanics ext)) (blkPl_177).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoSpec A (lsρ v1StateJtSymLocal1)))
def V1StateEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  V1StateEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)
def V1StateEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  V1StateEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)
def V1StateEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_405).rebase (blkPl_405).base (Rust.withPanics ext)) (blkPl_405).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A (lsρ v1StateJtSymLocal2)))
def V1StateEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_405).rebase (blkPl_405).base (Rust.withPanics ext)) (blkPl_405).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoSpec A (lsρ v1StateJtSymLocal2)))
def V1StateEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  V1StateEncodedLenLocal2PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)
def V1StateEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  V1StateEncodedLenLocal2PlacedOkExt A (tripleRatchetExterns C ctl abs)

theorem v1StateEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) :
    V1StateEncodedLenLocal1PinnedOkExt b A ext := by
  refine v1State_entry_ro_pinned_ok_ext b A ext _ (b + bv% (ls_xref% 0x39148 0x3914c))
    (Or.inl rfl) (hasJumpTableAddr_local1 b ext hb)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 1024 spqrV1StateBin_decode_0x39510 libsignalSessionCode_fnOff_0x38d84 keysUnsampledEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 600 spqrV1StateBin_decode_0x39368 libsignalSessionCode_fnOff_0x39e34 headerSentEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 664 spqrV1StateBin_decode_0x393a8 libsignalSessionCode_fnOff_0x38e70 polynomialEncoderEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 376 spqrV1StateBin_decode_0x39288 libsignalSessionCode_fnOff_0x3a0ac chunkedHeaderSentEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 408 spqrV1StateBin_decode_0x392a8 libsignalSessionCode_fnOff_0x3a330 ekSentCt1ReceivedEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 472 spqrV1StateBin_decode_0x392e8 libsignalSessionCode_fnOff_0x38e70 polynomialEncoderEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 124 spqrV1StateBin_decode_0x3918c libsignalSessionCode_fnOff_0x3a330 ekSentCt1ReceivedEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 188 spqrV1StateBin_decode_0x391cc libsignalSessionCode_fnOff_0x39f7c polynomialDecoderEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 1076 spqrV1StateBin_decode_0x39544 libsignalSessionCode_fnOff_0x3a478 noHeaderReceivedEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 1140 spqrV1StateBin_decode_0x39584 libsignalSessionCode_fnOff_0x39f7c polynomialDecoderEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 756 spqrV1StateBin_decode_0x39404 libsignalSessionCode_fnOff_0x38fe0 headerReceivedEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 820 spqrV1StateBin_decode_0x39444 libsignalSessionCode_fnOff_0x39f7c polynomialDecoderEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 520 spqrV1StateBin_decode_0x39318 libsignalSessionCode_fnOff_0x39974 chunkedCt1SampledEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 912 spqrV1StateBin_decode_0x394a0 libsignalSessionCode_fnOff_0x388b8 ct1SentEkReceivedEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 976 spqrV1StateBin_decode_0x394e0 libsignalSessionCode_fnOff_0x38e70 polynomialEncoderEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 260 spqrV1StateBin_decode_0x39214 libsignalSessionCode_fnOff_0x39a94 ct1SentEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 324 spqrV1StateBin_decode_0x39254 libsignalSessionCode_fnOff_0x39f7c polynomialDecoderEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 1192 spqrV1StateBin_decode_0x395b8 libsignalSessionCode_fnOff_0x38a2c ct2SentEncodedLen_local1_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x39110 1256 spqrV1StateBin_decode_0x395f8 libsignalSessionCode_fnOff_0x38e70 polynomialEncoderEncodedLen_local1_pinned_ok_ext

theorem v1StateEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) :
    V1StateEncodedLenLocal1OkExt b A ext :=
  v1StateEncodedLen_ro_ok_of_pinned (v1StateEncodedLen_local1_pinned_ok_ext b A ext hb)
theorem v1StateEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) :
    V1StateEncodedLenLocal1PinnedOk b C A ctl abs :=
  v1StateEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs) hb
theorem v1StateEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) :
    V1StateEncodedLenLocal1Ok b C A ctl abs :=
  v1StateEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs) hb

theorem v1StateEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) :
    V1StateEncodedLenLocal2PinnedOkExt b A ext := by
  refine v1State_entry_ro_pinned_ok_ext b A ext _ (b + bv% (ls_xref% 0x62a38 0x62a3c))
    (Or.inr rfl) (hasJumpTableAddr_local2 b ext hb)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 1024 spqrV1StateBin_decode_0x62e00 libsignalSessionCode_fnOff_0x613cc keysUnsampledEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 600 spqrV1StateBin_decode_0x62c58 libsignalSessionCode_fnOff_0x63eac headerSentEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 664 spqrV1StateBin_decode_0x62c98 libsignalSessionCode_fnOff_0x615f4 polynomialEncoderEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 376 spqrV1StateBin_decode_0x62b78 libsignalSessionCode_fnOff_0x64b78 chunkedHeaderSentEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 408 spqrV1StateBin_decode_0x62b98 libsignalSessionCode_fnOff_0x67474 ekSentCt1ReceivedEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 472 spqrV1StateBin_decode_0x62bd8 libsignalSessionCode_fnOff_0x615f4 polynomialEncoderEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 124 spqrV1StateBin_decode_0x62a7c libsignalSessionCode_fnOff_0x67474 ekSentCt1ReceivedEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 188 spqrV1StateBin_decode_0x62abc libsignalSessionCode_fnOff_0x642fc polynomialDecoderEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 1076 spqrV1StateBin_decode_0x62e34 libsignalSessionCode_fnOff_0x6796c noHeaderReceivedEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 1140 spqrV1StateBin_decode_0x62e74 libsignalSessionCode_fnOff_0x642fc polynomialDecoderEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 756 spqrV1StateBin_decode_0x62cf4 libsignalSessionCode_fnOff_0x626c4 headerReceivedEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 820 spqrV1StateBin_decode_0x62d34 libsignalSessionCode_fnOff_0x642fc polynomialDecoderEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 520 spqrV1StateBin_decode_0x62c08 libsignalSessionCode_fnOff_0x63768 chunkedCt1SampledEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 912 spqrV1StateBin_decode_0x62d90 libsignalSessionCode_fnOff_0x5ed84 ct1SentEkReceivedEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 976 spqrV1StateBin_decode_0x62dd0 libsignalSessionCode_fnOff_0x615f4 polynomialEncoderEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 260 spqrV1StateBin_decode_0x62b04 libsignalSessionCode_fnOff_0x63948 ct1SentEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 324 spqrV1StateBin_decode_0x62b44 libsignalSessionCode_fnOff_0x642fc polynomialDecoderEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 1192 spqrV1StateBin_decode_0x62ea8 libsignalSessionCode_fnOff_0x5f2f0 ct2SentEncodedLen_local2_pinned_ok_ext
  · exact v1State_bl_call b ext libsignalSessionCode_fnOff_0x62a00 1256 spqrV1StateBin_decode_0x62ee8 libsignalSessionCode_fnOff_0x615f4 polynomialEncoderEncodedLen_local2_pinned_ok_ext

theorem v1StateEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) :
    V1StateEncodedLenLocal2OkExt b A ext :=
  v1StateEncodedLen_ro_ok_of_pinned (v1StateEncodedLen_local2_pinned_ok_ext b A ext hb)
theorem v1StateEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) :
    V1StateEncodedLenLocal2PinnedOk b C A ctl abs :=
  v1StateEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs) hb
theorem v1StateEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) :
    V1StateEncodedLenLocal2Ok b C A ctl abs :=
  v1StateEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs) hb

macro "v1State_bl_plain " fetchLem:ident calleeOk:ident A:term:max ext:term:max : term =>
  `(callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      ($fetchLem _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) ($calleeOk $A $ext))
macro "v1State_bl_lscl " fetchLem:ident calleeOk:ident A:term:max ext:term:max : term =>
  `(callPinnedEncLenAtF_of_bl_lscl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      ($fetchLem _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) ($calleeOk $A $ext))

theorem v1StateEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : V1StateEncodedLenLocal1PinnedPlacedOkExt A ext := by
  refine v1State_entry_ro_pinned_lscl_ok lsmpl _ A _ (lsρ v1StateJtSymLocal1)
    (Or.inr ⟨inferInstance, Rust.withPanics ext, Or.inl ⟨rfl, rfl⟩⟩)
    (hasJumpTableStepP2_placed_local1 (Rust.withPanics ext))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x400 keysUnsampledEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x258 headerSentEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x298 polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_lscl blkPC_177_rebase_fetch_0x178 chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x198 ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x1d8 polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x7c ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0xbc polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x434 noHeaderReceivedEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x474 polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x2f4 headerReceivedEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x334 polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_lscl blkPC_177_rebase_fetch_0x208 chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x390 ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x3d0 polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x104 ct1SentEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x144 polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x4a8 ct2SentEncodedLen_local1_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_177_rebase_fetch_0x4e8 polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A ext

theorem v1StateEncodedLen_local1_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : V1StateEncodedLenLocal1PlacedOkExt A ext :=
  v1StateEncodedLen_ro_lscl_ok_of_pinned (v1StateEncodedLen_local1_pinned_placed_ok_ext A ext)
theorem v1StateEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : V1StateEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  v1StateEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem v1StateEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : V1StateEncodedLenLocal1PlacedOk C A ctl abs :=
  v1StateEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem v1StateEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : V1StateEncodedLenLocal2PinnedPlacedOkExt A ext := by
  refine v1State_entry_ro_pinned_lscl_ok lsmpl _ A _ (lsρ v1StateJtSymLocal2)
    (Or.inr ⟨inferInstance, Rust.withPanics ext, Or.inr ⟨rfl, rfl⟩⟩)
    (hasJumpTableStepP2_placed_local2 (Rust.withPanics ext))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x400 keysUnsampledEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x258 headerSentEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x298 polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_lscl blkPC_405_rebase_fetch_0x178 chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x198 ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x1d8 polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x7c ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0xbc polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x434 noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x474 polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x2f4 headerReceivedEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x334 polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_lscl blkPC_405_rebase_fetch_0x208 chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x390 ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x3d0 polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x104 ct1SentEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x144 polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x4a8 ct2SentEncodedLen_local2_pinned_placed_ok_ext A ext
  · exact v1State_bl_plain blkPC_405_rebase_fetch_0x4e8 polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A ext

theorem v1StateEncodedLen_local2_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : V1StateEncodedLenLocal2PlacedOkExt A ext :=
  v1StateEncodedLen_ro_lscl_ok_of_pinned (v1StateEncodedLen_local2_pinned_placed_ok_ext A ext)
theorem v1StateEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : V1StateEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  v1StateEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem v1StateEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : V1StateEncodedLenLocal2PlacedOk C A ctl abs :=
  v1StateEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end CryptoVerification.SpqrV1.ProtoRepr
