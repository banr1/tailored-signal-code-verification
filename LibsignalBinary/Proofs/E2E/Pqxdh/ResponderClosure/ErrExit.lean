/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import Aesop.BuiltinRules
public import ProofLib.Lemmas
public import ProofLib.SepLogic
import GeneratedLean.LibsignalSessionCode -- shake: keep
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.SepLogic.WPp
import VCVio.Prelude.Core
public import GeneratedLean.LibsignalSessionObj -- shake: keep

/-!
# Error-Branch Normalization Helpers for `message_decrypt_prekey::{closure#0}`

Address-arithmetic, bitvector-condition, and separation-logic normalization lemmas supporting the
Stage P2 and Stage P3 error-exit funnels of `message_decrypt_prekey::<PqxdhRng>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. Helper Normalization Lemmas for Error Branches -/

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_adds64_neg1_2 :
    ConditionHolds CondCode.NE (addsPState64 0xffffffffffffffff#64 2#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_eq_adds64_neg1_1 :
    ConditionHolds CondCode.EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_adds64_dup_2 :
    ConditionHolds CondCode.NE (addsPState64 0x8000000000000017#64 2#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_adds64_18_2 :
    ConditionHolds CondCode.NE (addsPState64 0x8000000000000018#64 2#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_eq_subs64_dup_dup :
    ConditionHolds CondCode.EQ (subsPState64 0x8000000000000017#64 0x8000000000000017#64) =
      true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_subs64_0_0 :
    ConditionHolds CondCode.NE (subsPState64 0#64 0#64) = false := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_eq_subs32_3_2 :
    ConditionHolds CondCode.EQ (subsPState32 3#32 2#32) = false := by
  simp only [ConditionHolds, subsPState32]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_subs32_3_3 :
    ConditionHolds CondCode.NE (subsPState32 3#32 3#32) = false := by
  simp only [ConditionHolds, subsPState32]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_subs64_1_1 :
    ConditionHolds CondCode.NE (subsPState64 1#64 1#64) = false := by
  simp only [ConditionHolds, subsPState64]; decide

theorem cond_ne_adds64_of_ne_neg3 {w : BitVec 64} (h : w ≠ 0xfffffffffffffffd#64) :
    ConditionHolds CondCode.NE (addsPState64 w 3#64) = true := by
  have hne : w + 3#64 ≠ 0#64 := fun heq => h (by rw [← BitVec.add_sub_cancel w 3#64, heq]; rfl)
  rw [conditionHolds_ne_addsPState64]
  exact bne_iff_ne.mpr hne

theorem cond_ne_adds64_of_ne_neg2 {w : BitVec 64} (h : w ≠ 0xfffffffffffffffe#64) :
    ConditionHolds CondCode.NE (addsPState64 w 2#64) = true := by
  have hne : w + 2#64 ≠ 0#64 := fun heq => h (by rw [← BitVec.add_sub_cancel w 2#64, heq]; rfl)
  rw [conditionHolds_ne_addsPState64]
  exact bne_iff_ne.mpr hne

theorem cond_eq_adds64_of_ne_neg1 {w : BitVec 64} (h : w ≠ 0xffffffffffffffff#64) :
    ConditionHolds CondCode.EQ (addsPState64 w 1#64) = false := by
  have hne : w + 1#64 ≠ 0#64 := fun heq => h (by rw [← BitVec.add_sub_cancel w 1#64, heq]; rfl)
  rw [conditionHolds_eq_addsPState64]
  exact beq_eq_false_iff_ne.mpr hne

theorem cond_eq_subs64_of_ne_dup {w : BitVec 64} (h : w ≠ 0x8000000000000017#64) :
    ConditionHolds CondCode.EQ (subsPState64 w 0x8000000000000017#64) = false := by
  rw [conditionHolds_eq_subsPState64, beq_eq_false_iff_ne]
  exact h

theorem adrp_logLevel_0x2dec {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64) (he : entry = b + 0x7200c#64) :
    (((entry + 0x2dec#64) &&& 0xfffffffffffff000#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x74000) = b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) ∧
    (((0x7200c#64 + (b + 0x2dec#64)) &&& 0xfffffffffffff000#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x74000) = b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) := by
  subst he
  constructor
  · have hp : ((b + 0x7200c#64 + 0x2dec#64) &&& 0xfffffffffffff000#64) = b + 0x74000#64 := by
      rw [BitVec.add_assoc, ProofLib.ObjectLoad.adrp_page_of_aligned hb]
      rfl
    rw [hp]
    bv_omega
  · have hp : ((0x7200c#64 + (b + 0x2dec#64)) &&& 0xfffffffffffff000#64) = b + 0x74000#64 := by
      rw [show 0x7200c#64 + (b + 0x2dec#64) = b + (0x7200c#64 + 0x2dec#64) by bv_omega,
          ProofLib.ObjectLoad.adrp_page_of_aligned hb]
      rfl
    rw [hp]
    bv_omega

/-! ## 2. Stage P2 Error-Exit Helpers -/

theorem pointsTo64_split32_coro_268 (coroPtr w : BitVec 64) :
    ((coroPtr + 0x268#64) ↦₆₄ w) =
      (((coroPtr + 0x268#64) ↦₃₂ w.extractLsb' 0 32) ∗
       ((coroPtr + 0x26c#64) ↦₃₂ w.extractLsb' 32 32)) := by
  have h : coroPtr + 0x26c#64 = (coroPtr + 0x268#64) + 4#64 := by bv_omega
  rw [h, pointsTo64_split32]

theorem pointsTo32_pair_coro_268 (coroPtr : BitVec 64) (lo hi : BitVec 32) :
    (((coroPtr + 0x268#64) ↦₃₂ lo) ∗ ((coroPtr + 0x26c#64) ↦₃₂ hi)) =
      ((coroPtr + 0x268#64) ↦₆₄ (hi ++ lo)) := by
  have h : coroPtr + 0x26c#64 = (coroPtr + 0x268#64) + 4#64 := by bv_omega
  rw [h, pointsTo32_pair]

theorem realign_40_at_a98 (sp w0 w1 w2 w3 w4 : BitVec 64) :
    (((sp + 0xa98#64) ↦₆₄ w0) ∗
     ((sp + 0xaa0#64) ↦₆₄ w1) ∗
     ((sp + 0xaa8#64) ↦₆₄ w2) ∗
     ((sp + 0xab0#64) ↦₆₄ w3) ∗
     ((sp + 0xab8#64) ↦₆₄ w4)) =
    (((sp + 0xa98#64) ↦₃₂ w0.extractLsb' 0 32) ∗
     ((sp + 0xa9c#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
     ((sp + 0xaa4#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
     ((sp + 0xaac#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
     ((sp + 0xab4#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
     ((sp + 0xabc#64) ↦₃₂ w4.extractLsb' 32 32)) := by
  have h9c : sp + 0xa9c#64 = (sp + 0xa98#64) + 4#64 := by bv_omega
  have ha0 : sp + 0xaa0#64 = (sp + 0xa9c#64) + 4#64 := by bv_omega
  have ha4 : sp + 0xaa4#64 = (sp + 0xaa0#64) + 4#64 := by bv_omega
  have ha8 : sp + 0xaa8#64 = (sp + 0xaa4#64) + 4#64 := by bv_omega
  have hac : sp + 0xaac#64 = (sp + 0xaa8#64) + 4#64 := by bv_omega
  have hb0 : sp + 0xab0#64 = (sp + 0xaac#64) + 4#64 := by bv_omega
  have hb4 : sp + 0xab4#64 = (sp + 0xab0#64) + 4#64 := by bv_omega
  have hb8 : sp + 0xab8#64 = (sp + 0xab4#64) + 4#64 := by bv_omega
  have hbc : sp + 0xabc#64 = (sp + 0xab8#64) + 4#64 := by bv_omega
  rw [pointsTo64_split32 (sp + 0xa98#64) w0,
      pointsTo64_split32 (sp + 0xaa0#64) w1,
      pointsTo64_split32 (sp + 0xaa8#64) w2,
      pointsTo64_split32 (sp + 0xab0#64) w3,
      pointsTo64_split32 (sp + 0xab8#64) w4,
      ← h9c, ← ha4, ← hac, ← hb4, ← hbc]
  simp only [sepConj_assoc]
  rw [← sepConj_assoc ((sp + 0xa9c#64) ↦₃₂ _), ha0, pointsTo32_pair,
      ← sepConj_assoc ((sp + 0xaa4#64) ↦₃₂ _), ha8, pointsTo32_pair,
      ← sepConj_assoc ((sp + 0xaac#64) ↦₃₂ _), hb0, pointsTo32_pair,
      ← sepConj_assoc ((sp + 0xab4#64) ↦₃₂ _), hb8, pointsTo32_pair]

end CryptoVerification.E2E.Pqxdh.ResponderClosure
