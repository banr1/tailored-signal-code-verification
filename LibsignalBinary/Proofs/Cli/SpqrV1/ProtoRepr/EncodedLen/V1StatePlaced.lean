/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsV1StatePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateBranchesBPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateBranchesPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import ProofLib.SepLogic.WPp

/-!
# Relocatable `V1State::encoded_len [local#3]` Master Proof and Contracts (Block `484`)

Combines `.rodata` jump-table dispatch with all 11 placed variant branches to prove explicit
jump-table and `LibsignalRoLoaded`-discharged `subroutine_ok` contracts on CLI Block `484` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open EncodedLen
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero

local notation "cliV1JtAddr" => lsρ CryptoVerification.Cli.SpqrV1.ProtoRepr.cliV1StateJtSym

/-! ## 1. Master Entry-Point Proof (`v1State_484_entry_ro_pinned_wp_placed`) -/

theorem v1State_484_entry_ro_pinned_wp_placed [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State))
    (x : V1StateEncodedLenPinnedGhost) (R : SepProp) (s0 : State)
    (hpc0 : s0.pc = (blkPl_484).base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (v1StateEncodedLenRoPinnedSpec A cliV1JtAddr).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    ∃ P Fr, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPpF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (s0.readReg64 .lr) s0 P
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (v1StateEncodedLenRoPinnedSpec A cliV1JtAddr).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (v1StateEncodedLenRoPinnedSpec A cliV1JtAddr).onPanic x s0 sf ∗ R)) := by
  v1State_484_fetches_range H 64 80
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
      v1StateJumpTableBytesAt cliV1JtAddr ∗
      v1StatePBPinnedAt A g a m ∗ R, emp,
    by rw [sepConj_emp]; convert hpre using 1; ac_rfl, ?_⟩
  rcases m with ⟨inner⟩
  cases inner with
  | none =>
    have hP_eq (u32 u24 u16 : BitVec 64) :
        (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
          ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
          stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
          v1StateJumpTableBytesAt cliV1JtAddr ∗
          v1StatePBPinnedAt A g a ⟨none⟩ ∗ R) =
        (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
          ((s0.sp - 16#64) ↦₆₄ u16) ∗
          (((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 8#64) 216 ∗ R) ∗
          (a ↦₆₄ noneCap2)) := by
      dsimp only [v1StatePBPinnedAt]; ac_rfl
    refine step_v1State_none_placed (LibsignalCodeLoaded lsmpl) H a s0.sp v32 v24 v16
      hpc0 hrun rfl halign hx0 (hP_eq v32 v24 v16) ?_
    intro sf hpcf hrunf hspf htrf hx0f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
    exact v1State_post_of_body A cliV1JtAddr a g ⟨none⟩ R s0 sf _ _ _ v8 hx0f htrf hm_f
  | some is =>
    cases is with
    | keysUnsampled v =>
      have hcap : (optKeysUnsampledCap g.a.gKeysUnsampled v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
          (optKeysUnsampledCap g.a.gKeysUnsampled v.uc + 2#64 != 0#64) = v.uc.isSome := by
        apply optKeysUnsampledPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000000#64) ∗
            memRegion (a + 64#64) 160 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.keysUnsampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optKeysUnsampledPBPinnedAt A g.a.gKeysUnsampled (a + 8#64) v.uc ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 64#64) 160 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000000#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine step_v1State_prologue_to_64_placed (LibsignalCodeLoaded lsmpl) H
        a s0.sp 0x8000000000000000#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 80 s1 0#64 hx8_1
      refine step_v1State_keysUnsampled_placed (LibsignalCodeLoaded lsmpl) A H
        (v1State_484_bl_ku A H) g.a.gKeysUnsampled a s0.sp v hfit
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
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.keysUnsampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | keysSampled v =>
      have hcap1 : (optHeaderSentCap g.a.gKeysSampled.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optHeaderSentCap g.a.gKeysSampled.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optHeaderSentPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000001#64) ∗
            optPolynomialEncoderPBPinnedAt A g.a.gKeysSampled.2 (a + 112#64) v.sendingHdr ∗
            memRegion (a + 168#64) 56 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyEncCap g.a.gKeysSampled.2 v.sendingHdr + 1#64 == 0#64) = !v.sendingHdr.isSome ∧
          (optPolyEncCap g.a.gKeysSampled.2 v.sendingHdr + 1#64 != 0#64) = v.sendingHdr.isSome := by
        apply optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 112#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000001#64) ∗
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
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.keysSampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optHeaderSentPBPinnedAt A g.a.gKeysSampled.1 (a + 8#64) v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.a.gKeysSampled.2 (a + 112#64) v.sendingHdr ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 168#64) 56 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000001#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine step_v1State_prologue_to_64_placed (LibsignalCodeLoaded lsmpl) H
        a s0.sp 0x8000000000000001#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 576 s1 1#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_keysSampled_placed
        (LibsignalCodeLoaded lsmpl) A H (v1State_484_bl_ks1 A H) (v1State_484_bl_ks2 A H)
        g.a.gKeysSampled a s0.sp v hfit
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
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.keysSampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | headerSent v =>
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.headerSent v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (chunkedHeaderSentPBPinnedAt A g.a.gHeaderSent (a + 8#64) v ∗
              stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 184#64) 40 ∗
                ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000002#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]; ac_rfl
      refine step_v1State_prologue_to_64_placed (LibsignalCodeLoaded lsmpl) H
        a s0.sp 0x8000000000000002#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 372 s1 2#64 hx8_1
      refine step_v1State_headerSent_placed (LibsignalCodeLoaded lsmpl) A H
        (v1State_484_bl_hs A H) g.a.gHeaderSent a s0.sp v hfit
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
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.headerSent v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ct1Received v =>
      have hcap1 : (optEkSentCt1ReceivedCap g.a.gCt1Received.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optEkSentCt1ReceivedCap g.a.gCt1Received.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optEkSentCt1ReceivedPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000003#64) ∗
            optPolynomialEncoderPBPinnedAt A g.a.gCt1Received.2 (a + 112#64) v.sendingEk ∗
            memRegion (a + 168#64) 56 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyEncCap g.a.gCt1Received.2 v.sendingEk + 1#64 == 0#64) = !v.sendingEk.isSome ∧
          (optPolyEncCap g.a.gCt1Received.2 v.sendingEk + 1#64 != 0#64) = v.sendingEk.isSome := by
        apply optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 112#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000003#64) ∗
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
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.ct1Received v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optEkSentCt1ReceivedPBPinnedAt A g.a.gCt1Received.1 (a + 8#64) v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.a.gCt1Received.2 (a + 112#64) v.sendingEk ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 168#64) 56 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000003#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine step_v1State_prologue_to_64_placed (LibsignalCodeLoaded lsmpl) H
        a s0.sp 0x8000000000000003#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 384 s1 3#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ct1Received_placed
        (LibsignalCodeLoaded lsmpl) A H (v1State_484_bl_cr1 A H) (v1State_484_bl_cr2 A H)
        g.a.gCt1Received a s0.sp v hfit
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
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.ct1Received v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ekSentCt1Received v =>
      have hcap1 : (optEkSentCt1ReceivedCap g.a.gEkSentCt1Received.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optEkSentCt1ReceivedCap g.a.gEkSentCt1Received.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optEkSentCt1ReceivedPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000004#64) ∗
            optPolynomialDecoderPBPinnedAt A g.a.gEkSentCt1Received.2 (a + 112#64) v.receivingCt2 ∗
            memRegion (a + 152#64) 72 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyDecCap g.a.gEkSentCt1Received.2 v.receivingCt2 + 1#64 == 0#64) = !v.receivingCt2.isSome ∧
          (optPolyDecCap g.a.gEkSentCt1Received.2 v.receivingCt2 + 1#64 != 0#64) = v.receivingCt2.isSome := by
        apply optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 112#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000004#64) ∗
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
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.ekSentCt1Received v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optEkSentCt1ReceivedPBPinnedAt A g.a.gEkSentCt1Received.1 (a + 8#64) v.uc ∗
              optPolynomialDecoderPBPinnedAt A g.a.gEkSentCt1Received.2 (a + 112#64) v.receivingCt2 ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 152#64) 72 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000004#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine step_v1State_prologue_to_64_placed (LibsignalCodeLoaded lsmpl) H
        a s0.sp 0x8000000000000004#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 100 s1 4#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ekSentCt1Received_placed
        (LibsignalCodeLoaded lsmpl) A H (v1State_484_bl_escr1 A H) (v1State_484_bl_escr2 A H)
        g.a.gEkSentCt1Received a s0.sp v hfit
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
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.ekSentCt1Received v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | noHeaderReceived v =>
      have hcap1 : (optNoHeaderReceivedCap g.a.gNoHeaderReceived.2 v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
          (optNoHeaderReceivedCap g.a.gNoHeaderReceived.2 v.uc + 2#64 != 0#64) = v.uc.isSome := by
        apply optNoHeaderReceivedPBPinnedAt_cap_bounds (p := a + 48#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000005#64) ∗
            optPolynomialDecoderPBPinnedAt A g.a.gNoHeaderReceived.1 (a + 8#64) v.receivingHdr ∗
            memRegion (a + 104#64) 120 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyDecCap g.a.gNoHeaderReceived.1 v.receivingHdr + 1#64 == 0#64) = !v.receivingHdr.isSome ∧
          (optPolyDecCap g.a.gNoHeaderReceived.1 v.receivingHdr + 1#64 != 0#64) = v.receivingHdr.isSome := by
        apply optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000005#64) ∗
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
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.noHeaderReceived v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optPolynomialDecoderPBPinnedAt A g.a.gNoHeaderReceived.1 (a + 8#64) v.receivingHdr ∗
              optNoHeaderReceivedPBPinnedAt A g.a.gNoHeaderReceived.2 (a + 48#64) v.uc ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 104#64) 120 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000005#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine step_v1State_prologue_to_64_placed (LibsignalCodeLoaded lsmpl) H
        a s0.sp 0x8000000000000005#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 712 s1 5#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_noHeaderReceived_placed
        (LibsignalCodeLoaded lsmpl) A H (v1State_484_bl_nhr1 A H) (v1State_484_bl_nhr2 A H)
        g.a.gNoHeaderReceived a s0.sp v hfit
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
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.noHeaderReceived v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | headerReceived v =>
      have hcap1 : (optHeaderReceivedCap g.b.gHeaderReceived.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optHeaderReceivedCap g.b.gHeaderReceived.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optHeaderReceivedPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000006#64) ∗
            optPolynomialDecoderPBPinnedAt A g.b.gHeaderReceived.2 (a + 88#64) v.receivingEk ∗
            memRegion (a + 128#64) 96 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyDecCap g.b.gHeaderReceived.2 v.receivingEk + 1#64 == 0#64) = !v.receivingEk.isSome ∧
          (optPolyDecCap g.b.gHeaderReceived.2 v.receivingEk + 1#64 != 0#64) = v.receivingEk.isSome := by
        apply optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 88#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000006#64) ∗
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
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.headerReceived v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optHeaderReceivedPBPinnedAt A g.b.gHeaderReceived.1 (a + 8#64) v.uc ∗
              optPolynomialDecoderPBPinnedAt A g.b.gHeaderReceived.2 (a + 88#64) v.receivingEk ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 128#64) 96 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000006#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine step_v1State_prologue_to_64_placed (LibsignalCodeLoaded lsmpl) H
        a s0.sp 0x8000000000000006#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 732 s1 6#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_headerReceived_placed
        (LibsignalCodeLoaded lsmpl) A H (v1State_484_bl_hr1 A H) (v1State_484_bl_hr2 A H)
        g.b.gHeaderReceived a s0.sp v hfit
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
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.headerReceived v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ct1Sampled v =>
      have ⟨hw_beq, hw_bne, hw_ult⟩ :
          (optCt1SentCap g.b.gCt1Sampled.uc v.uc + 2#64 == 0#64) = false ∧
          (optCt1SentCap g.b.gCt1Sampled.uc v.uc + 2#64 != 0#64) = true ∧
          ((optCt1SentCap g.b.gCt1Sampled.uc v.uc ^^^ 0x8000000000000000#64).ult 11#64) = false := by
        apply optCt1SentRest_disc_bounds (p := a)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc) ∗
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
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.ct1Sampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optCt1SentRest A g.b.gCt1Sampled.uc a v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (a + 128#64) v.sendingCt1 ∗
              optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (a + 184#64) v.receivingEk ∗
              stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt, chunkedCt1SampledPBPinnedAt]
        rw [optCt1SentPBPinnedAt_eq]; ac_rfl
      refine step_v1State_prologue_to_64_placed (LibsignalCodeLoaded lsmpl) H
        a s0.sp (optCt1SentCap g.b.gCt1Sampled.uc v.uc) v32 v24 v16
        hpc0 hrun rfl halign hx0 hw_beq hw_bne (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 520 s1 7#64 (by rw [hx8_1, hw_ult]; rfl)
      rw [fold_v1StateJumpTableBytesAt]
      have hP_cs :
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
            (optCt1SentRest A g.b.gCt1Sampled.uc a v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (a + 128#64) v.sendingCt1 ∗
              optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (a + 184#64) v.receivingEk ∗
              stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc)) =
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
            chunkedCt1SampledPBPinnedAt A g.b.gCt1Sampled a v ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            (v1StateJumpTableBytesAt cliV1JtAddr ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) := by
        dsimp only [chunkedCt1SampledPBPinnedAt]
        rw [optCt1SentPBPinnedAt_eq]; ac_rfl
      refine step_v1State_ct1Sampled_placed (LibsignalCodeLoaded lsmpl) A H
        (v1State_484_bl_cs A H) g.b.gCt1Sampled a s0.sp v hfit
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
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.ct1Sampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ekReceivedCt1Sampled v =>
      have hcap1 : (optCt1SentEkReceivedCap g.b.gEkReceivedCt1Sampled.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optCt1SentEkReceivedCap g.b.gEkReceivedCt1Sampled.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optCt1SentEkReceivedPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000008#64) ∗
            optPolynomialEncoderPBPinnedAt A g.b.gEkReceivedCt1Sampled.2 (a + 136#64) v.sendingCt1 ∗
            memRegion (a + 192#64) 32 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyEncCap g.b.gEkReceivedCt1Sampled.2 v.sendingCt1 + 1#64 == 0#64) = !v.sendingCt1.isSome ∧
          (optPolyEncCap g.b.gEkReceivedCt1Sampled.2 v.sendingCt1 + 1#64 != 0#64) = v.sendingCt1.isSome := by
        apply optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 136#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000008#64) ∗
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
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.ekReceivedCt1Sampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optCt1SentEkReceivedPBPinnedAt A g.b.gEkReceivedCt1Sampled.1 (a + 8#64) v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.b.gEkReceivedCt1Sampled.2 (a + 136#64) v.sendingCt1 ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 192#64) 32 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000008#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine step_v1State_prologue_to_64_placed (LibsignalCodeLoaded lsmpl) H
        a s0.sp 0x8000000000000008#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 888 s1 8#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ekReceivedCt1Sampled_placed
        (LibsignalCodeLoaded lsmpl) A H (v1State_484_bl_ercs1 A H) (v1State_484_bl_ercs2 A H)
        g.b.gEkReceivedCt1Sampled a s0.sp v hfit
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
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.ekReceivedCt1Sampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ct1Acknowledged v =>
      have hcap1 : (optCt1SentCap g.b.gCt1Acknowledged.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optCt1SentCap g.b.gCt1Acknowledged.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optCt1SentPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000009#64) ∗
            optPolynomialDecoderPBPinnedAt A g.b.gCt1Acknowledged.2 (a + 136#64) v.receivingEk ∗
            memRegion (a + 176#64) 48 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyDecCap g.b.gCt1Acknowledged.2 v.receivingEk + 1#64 == 0#64) = !v.receivingEk.isSome ∧
          (optPolyDecCap g.b.gCt1Acknowledged.2 v.receivingEk + 1#64 != 0#64) = v.receivingEk.isSome := by
        apply optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 136#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000009#64) ∗
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
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.ct1Acknowledged v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optCt1SentPBPinnedAt A g.b.gCt1Acknowledged.1 (a + 8#64) v.uc ∗
              optPolynomialDecoderPBPinnedAt A g.b.gCt1Acknowledged.2 (a + 136#64) v.receivingEk ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 176#64) 48 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000009#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine step_v1State_prologue_to_64_placed (LibsignalCodeLoaded lsmpl) H
        a s0.sp 0x8000000000000009#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 236 s1 9#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ct1Acknowledged_placed
        (LibsignalCodeLoaded lsmpl) A H (v1State_484_bl_ca1 A H) (v1State_484_bl_ca2 A H)
        g.b.gCt1Acknowledged a s0.sp v hfit
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
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.ct1Acknowledged v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ct2Sampled v =>
      have hcap1 : (optCt2SentCap g.b.gCt2Sampled.2 v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
          (optCt2SentCap g.b.gCt2Sampled.2 v.uc + 2#64 != 0#64) = v.uc.isSome := by
        apply optCt2SentPBPinnedAt_cap_bounds (p := a + 64#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x800000000000000a#64) ∗
            optPolynomialEncoderPBPinnedAt A g.b.gCt2Sampled.1 (a + 8#64) v.sendingCt2 ∗
            memRegion (a + 120#64) 104 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; ac_rfl
      have hcap2 : (optPolyEncCap g.b.gCt2Sampled.1 v.sendingCt2 + 1#64 == 0#64) = !v.sendingCt2.isSome ∧
          (optPolyEncCap g.b.gCt2Sampled.1 v.sendingCt2 + 1#64 != 0#64) = v.sendingCt2.isSome := by
        apply optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x800000000000000a#64) ∗
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
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.ct2Sampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optPolynomialEncoderPBPinnedAt A g.b.gCt2Sampled.1 (a + 8#64) v.sendingCt2 ∗
              optCt2SentPBPinnedAt A g.b.gCt2Sampled.2 (a + 64#64) v.uc ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 120#64) 104 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x800000000000000a#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; ac_rfl
      refine step_v1State_prologue_to_64_placed (LibsignalCodeLoaded lsmpl) H
        a s0.sp 0x800000000000000a#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 868 s1 10#64 hx8_1
      refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_v1State_ct2Sampled_placed
        (LibsignalCodeLoaded lsmpl) A H (v1State_484_bl_c2s1 A H) (v1State_484_bl_c2s2 A H)
        g.b.gCt2Sampled a s0.sp v hfit
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
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.ct2Sampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f

/-! ## 2. Explicit `.rodata` Jump-Table Placed Contracts (`lsρ cliV1StateJtSym`) -/

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_484 (Rust.withPanics ext)) (blkPl_484).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A cliV1JtAddr))

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_484 (Rust.withPanics ext)) (blkPl_484).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoSpec A cliV1JtAddr))

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PinnedPlacedOkExt
    A (tripleRatchetExterns C ctl abs)

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PlacedOkExt
    A (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_484 H) (blkPl_484).base
      (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A cliV1JtAddr)) :=
  subroutine_ok_of_sepWPpF_lscl (v1State_484_entry_ro_pinned_wp_placed A H)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_484 H) (blkPl_484).base
      (withLsCodeLoaded lsmpl (v1StateEncodedLenRoSpec A cliV1JtAddr)) :=
  v1StateEncodedLen_ro_lscl_ok_of_pinned
    (CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_pinned_placed_ok_x A H)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PinnedPlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_pinned_placed_ok_x
    A (Rust.withPanics ext)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_placed_ok_x
    A (Rust.withPanics ext)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_pinned_placed_ok_ext
    A (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1PlacedOk C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_placed_ok_ext
    A (tripleRatchetExterns C ctl abs)

/-! ## 3. `LibsignalRoLoaded` Jump-Table-Discharged Placed Contracts (`*_ro_*` / `ro_*`) -/

abbrev _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded
    {α : Type} (pl : MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalRoLoaded pl s0.mem⌝ }

private theorem subroutine_ok_v1State_ro_pinned_of_roBase [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A cliV1JtAddr))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
          (v1StateEncodedLenPinnedSpec A))) := by
  refine subroutine_ok_mono h (fun x R s0 hp => ?_) (fun x R s0 sf hq => ?_)
  · obtain ⟨hcl, hp1⟩ := extract_withLsCodeLoaded hp
    dsimp only [CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded] at hp1
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp1
    obtain ⟨hro, hp2⟩ := hp1
    have hp3 := CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateJumpTableBytes_lsro_cli_intro hro hp2
    dsimp only [withLsCodeLoaded, v1StateEncodedLenRoPinnedSpec,
      v1StateEncodedLenPinnedSpec, lsρ] at hp3 ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, Satisfies.mono (Entails.of_eq (by ac_rfl)) hp3⟩
  · dsimp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded,
      v1StateEncodedLenRoPinnedSpec, v1StateEncodedLenPinnedSpec] at hq ⊢
    have hperm : sf.mem ⊨
        (cliV1JtAddr ↦ᵣ v1StateJumpTableBytes) ∗
        ((⌜sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
          v1StatePBPinnedAt A x.g x.a x.m ∗ stackAt s0.sp v1StateEncodedLenStack) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
    exact Satisfies.of_sep_right hperm

private theorem subroutine_ok_v1State_ro_unpin [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
          (v1StateEncodedLenPinnedSpec A)))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
          (v1StateEncodedLenSpec A))) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded,
    v1StateEncodedLenSpec] at hpre
  rw [v1StatePBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨x.a, g, x.m⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded,
      v1StateEncodedLenSpec]
    rw [v1StatePBAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

private theorem subroutine_ok_swap_lsro_lscl {α : Type} {pl : MultiPlacement}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded pl
        (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded pl spec))) :
    subroutine_ok prog entry
      (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded pl
        (withLsCodeLoaded pl spec)) := by
  refine subroutine_ok_mono h
    (fun _ _ _ hp => Satisfies.mono (Entails.of_eq (by
      dsimp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded]
      ac_rfl)) hp)
    (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ he => he)
    (fun _ _ _ _ ho => ho)

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1RoPinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_484 (Rust.withPanics ext)) (blkPl_484).base
    (withLsCodeLoaded lsmpl
      (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
        (v1StateEncodedLenPinnedSpec A)))

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1RoPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_484 (Rust.withPanics ext)) (blkPl_484).base
    (withLsCodeLoaded lsmpl
      (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
        (v1StateEncodedLenSpec A)))

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1RoPinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1RoPinnedPlacedOkExt
    A (tripleRatchetExterns C ctl abs)

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1RoPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1RoPlacedOkExt
    A (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_484 H) (blkPl_484).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
          (v1StateEncodedLenPinnedSpec A))) :=
  subroutine_ok_v1State_ro_pinned_of_roBase
    (CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_pinned_placed_ok_x A H)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_484 H) (blkPl_484).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
          (v1StateEncodedLenSpec A))) :=
  subroutine_ok_v1State_ro_unpin
    (CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_pinned_placed_ok_x A H)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1RoPinnedPlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_pinned_placed_ok_x
    A (Rust.withPanics ext)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1RoPlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_placed_ok_x
    A (Rust.withPanics ext)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1RoPinnedPlacedOk C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_pinned_placed_ok_ext
    A (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.V1StateEncodedLenLocal1RoPlacedOk C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_placed_ok_ext
    A (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ro_v1StateEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_484 H) (blkPl_484).base
      (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl (v1StateEncodedLenPinnedSpec A))) :=
  subroutine_ok_swap_lsro_lscl
    (CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_pinned_placed_ok_x A H)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ro_v1StateEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_484 H) (blkPl_484).base
      (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl (v1StateEncodedLenSpec A))) :=
  subroutine_ok_swap_lsro_lscl
    (CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateEncodedLen_local1_ro_placed_ok_x A H)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ro_v1StateEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_484 (Rust.withPanics ext)) (blkPl_484).base
      (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl (v1StateEncodedLenPinnedSpec A))) :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ro_v1StateEncodedLen_local1_pinned_placed_ok_x
    A (Rust.withPanics ext)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ro_v1StateEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_484 (Rust.withPanics ext)) (blkPl_484).base
      (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl (v1StateEncodedLenSpec A))) :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ro_v1StateEncodedLen_local1_placed_ok_x
    A (Rust.withPanics ext)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ro_v1StateEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (lsProg_484 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_484).base
      (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl (v1StateEncodedLenPinnedSpec A))) :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ro_v1StateEncodedLen_local1_pinned_placed_ok_ext
    A (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ro_v1StateEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (lsProg_484 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_484).base
      (CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl (v1StateEncodedLenSpec A))) :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ro_v1StateEncodedLen_local1_placed_ok_ext
    A (tripleRatchetExterns C ctl abs)

end CryptoVerification.SpqrV1.ProtoRepr
