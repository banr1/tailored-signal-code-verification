/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec

public import Arm64
public import ProofLib

/-!
# Arithmetic and Flag Lemmas for `SystemTime::add`

Pure arithmetic, NZCV flag, and 16-byte stack-frame lemmas for `<SystemTime as Add<Duration>>::add`:
`i64::checked_add_unsigned` overflow guards, nanosecond `10^9` carry normalization, and
`addsPState64` branch-condition equivalences.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd.TimeAddLemmas

open Arm64 ProofLib

theorem addWithCarry64_v_eq_msb (x y : BitVec 64) :
    (AddWithCarry64 x y false).2.v = ((x.msb == y.msb) && ((x + y).msb != x.msb)) := by
  unfold AddWithCarry64
  bv_robdd

theorem cmp_zero64_n_eq_msb (y : BitVec 64) :
    (AddWithCarry64 y (~~~0#64) true).2.n = y.msb := by
  unfold AddWithCarry64
  bv_robdd

theorem timeAdd_v_bne_msb_eq_overflow (sec dsecs : BitVec 64) :
    ((AddWithCarry64 sec dsecs false).2.v != dsecs.msb) =
      decide ((2 ^ 63 - 1 : Int) < sec.toInt + (dsecs.toNat : Int)) := by
  rw [addWithCarry64_v_eq_msb]
  have hs_lt : sec.toNat < 2 ^ 64 := sec.isLt
  have hd_lt : dsecs.toNat < 2 ^ 64 := dsecs.isLt
  have hsum_tn : (sec + dsecs).toNat = (sec.toNat + dsecs.toNat) % 2 ^ 64 :=
    BitVec.toNat_add sec dsecs
  have hs_toInt : sec.toInt =
      if 2 ^ 63 ≤ sec.toNat then (sec.toNat : Int) - 2 ^ 64 else (sec.toNat : Int) := by
    rw [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide]
    split <;> simp_all <;> omega
  rw [BitVec.msb_eq_decide, BitVec.msb_eq_decide, BitVec.msb_eq_decide, hsum_tn, hs_toInt]
  by_cases hs : 2 ^ 63 ≤ sec.toNat <;> by_cases hd : 2 ^ 63 ≤ dsecs.toNat
  · by_cases h1 : 2 ^ 63 ≤ (sec.toNat + dsecs.toNat) % 2 ^ 64
    · simp [hs, hd, h1]; omega
    · simp [hs, hd, h1]; omega
  · simp [hs, hd]; omega
  · simp [hs, hd]; omega
  · by_cases h1 : 2 ^ 63 ≤ (sec.toNat + dsecs.toNat) % 2 ^ 64
    · simp [hs, hd, h1]; omega
    · simp [hs, hd, h1]; omega

theorem cset_eor_getLsbD0 (v n : Bool) :
    (((if !n then 0#32 else 1#32) ^^^ (if !v then 0#32 else 1#32)).zeroExtend 64).getLsbD 0 =
      (v != n) := by
  cases v <;> cases n <;> decide

theorem timeAdd_eor_bit0_eq_overflow (sec dsecs : BitVec 64) :
    (((if !(AddWithCarry64 dsecs (~~~0#64) true).2.n then 0#32 else 1#32) ^^^
      (if !(AddWithCarry64 sec dsecs false).2.v then 0#32 else 1#32)).zeroExtend 64).getLsbD 0 =
      decide ((2 ^ 63 - 1 : Int) < sec.toInt + (dsecs.toNat : Int)) := by
  rw [cset_eor_getLsbD0, cmp_zero64_n_eq_msb, timeAdd_v_bne_msb_eq_overflow]

theorem timeAdd_sec_add_no_overflow (sec dsecs : BitVec 64)
    (h : ¬ ((2 ^ 63 - 1 : Int) < sec.toInt + (dsecs.toNat : Int))) :
    sec + dsecs = BitVec.ofInt 64 (sec.toInt + (dsecs.toNat : Int)) ∧
      (sec + dsecs).toInt = sec.toInt + (dsecs.toNat : Int) ∧
      -(2 ^ 63 : Int) ≤ sec.toInt + (dsecs.toNat : Int) ∧
      sec.toInt + (dsecs.toNat : Int) ≤ 2 ^ 63 - 1 := by
  have hs_lo : -(2 ^ 63 : Int) ≤ sec.toInt := BitVec.le_toInt sec
  have hlo : -(2 ^ 63 : Int) ≤ sec.toInt + (dsecs.toNat : Int) := by omega
  have hhi : sec.toInt + (dsecs.toNat : Int) ≤ 2 ^ 63 - 1 := by omega
  have h_eq : sec + dsecs = BitVec.ofInt 64 (sec.toInt + (dsecs.toNat : Int)) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_toInt]
    have hd : BitVec.ofInt 64 (dsecs.toNat : Int) = dsecs := by
      change BitVec.ofNat 64 dsecs.toNat = dsecs
      simp [BitVec.ofNat_toNat]
    rw [hd]
  have h_toInt : (sec + dsecs).toInt = sec.toInt + (dsecs.toNat : Int) := by
    rw [h_eq]
    exact BitVec.toInt_ofInt_eq_self (by decide : 0 < 64) hlo (by omega)
  exact ⟨h_eq, h_toInt, hlo, hhi⟩

theorem timeAdd_nsec_add_toNat (nsec nanos : BitVec 32)
    (hn1 : nsec.toNat < 10 ^ 9) (hn2 : nanos.toNat < 10 ^ 9) :
    (nanos + nsec).toNat = nsec.toNat + nanos.toNat ∧
      nanos + nsec = BitVec.ofNat 32 (nsec.toNat + nanos.toNat) := by
  have hsum : nanos.toNat + nsec.toNat < 2 ^ 32 := by omega
  have htn : (nanos + nsec).toNat = nsec.toNat + nanos.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum, Nat.add_comm]
  refine ⟨htn, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [htn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem addWithCarry32_cmp_billion_c (w : BitVec 32) :
    (AddWithCarry32 w (~~~1000000000#32) true).2.c = decide (10 ^ 9 ≤ w.toNat) := by
  unfold AddWithCarry32
  simp only [↓reduceIte]
  rw [BitVec.msb_eq_decide]
  have hw : w.toNat < 2 ^ 32 := w.isLt
  have htn : (1#33 + ((~~~1000000000#32).zeroExtend 33 + w.zeroExtend 33)).toNat =
      2 ^ 32 - 10 ^ 9 + w.toNat := by
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth,
      show (1#33).toNat = 1 from rfl,
      show (~~~1000000000#32).toNat = 2 ^ 32 - 1 - 10 ^ 9 from rfl]
    omega
  rw [htn]
  by_cases hle : 10 ^ 9 ≤ w.toNat
  · have hge : 2 ^ (33 - 1) ≤ 2 ^ 32 - 10 ^ 9 + w.toNat := by omega
    rw [decide_eq_true hge, decide_eq_true hle]
  · have hlt : ¬ (2 ^ (33 - 1) ≤ 2 ^ 32 - 10 ^ 9 + w.toNat) := by omega
    rw [decide_eq_false hlt, decide_eq_false hle]

theorem timeAdd_nsec_cmp_carry_eq (nsec nanos : BitVec 32)
    (hn1 : nsec.toNat < 10 ^ 9) (hn2 : nanos.toNat < 10 ^ 9) :
    (AddWithCarry32 (nanos + nsec) (~~~1000000000#32) true).2.c =
      decide (10 ^ 9 ≤ nsec.toNat + nanos.toNat) := by
  rw [addWithCarry32_cmp_billion_c, (timeAdd_nsec_add_toNat nsec nanos hn1 hn2).1]

theorem timeAdd_nsec_sub_billion (nsec nanos : BitVec 32)
    (hn1 : nsec.toNat < 10 ^ 9) (hn2 : nanos.toNat < 10 ^ 9)
    (hge : 10 ^ 9 ≤ nsec.toNat + nanos.toNat) :
    (nanos + nsec) + 0xc4653600#32 = BitVec.ofNat 32 (nsec.toNat + nanos.toNat - 10 ^ 9) := by
  have htn := (timeAdd_nsec_add_toNat nsec nanos hn1 hn2).1
  have hneg : 0xc4653600#32 = -1000000000#32 := by decide
  rw [hneg, ← BitVec.sub_eq_add_neg]
  apply BitVec.eq_of_toNat_eq
  have h10 : (1000000000#32).toNat = 10 ^ 9 := rfl
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, htn, h10]; exact hge),
      htn, h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem timeAdd_carry_v_eq_overflow (x : BitVec 64) (secs : Int)
    (hx : x = BitVec.ofInt 64 secs)
    (hlo : -(2 ^ 63 : Int) ≤ secs) (hhi : secs ≤ 2 ^ 63 - 1) :
    (AddWithCarry64 x 1#64 false).2.v = decide ((2 ^ 63 - 1 : Int) < secs + 1) ∧
      x + 1#64 = BitVec.ofInt 64 (secs + 1) := by
  have h_toInt : x.toInt = secs := by
    rw [hx]
    exact BitVec.toInt_ofInt_eq_self (by decide : 0 < 64) hlo (by omega)
  have h_max_iff : x = 0x7fff_ffff_ffff_ffff#64 ↔ secs = 2 ^ 63 - 1 := by
    constructor
    · intro hxeq
      rw [← h_toInt, hxeq]
      decide
    · intro hseq
      rw [hx, hseq]
      decide
  have hv_max : (AddWithCarry64 x 1#64 false).2.v = (x == 0x7fff_ffff_ffff_ffff#64) := by
    unfold AddWithCarry64
    bv_robdd
  have hv : (AddWithCarry64 x 1#64 false).2.v = decide ((2 ^ 63 - 1 : Int) < secs + 1) := by
    rw [hv_max]
    by_cases hmax : secs = 2 ^ 63 - 1
    · have hxeq : (x == 0x7fff_ffff_ffff_ffff#64) = true := beq_iff_eq.mpr (h_max_iff.mpr hmax)
      have hov : (2 ^ 63 - 1 : Int) < secs + 1 := by omega
      rw [hxeq, decide_eq_true hov]
    · have hxeq : (x == 0x7fff_ffff_ffff_ffff#64) = false :=
        beq_eq_false_iff_ne.mpr (fun he => hmax (h_max_iff.mp he))
      have hnov : ¬ ((2 ^ 63 - 1 : Int) < secs + 1) := by omega
      rw [hxeq, decide_eq_false hnov]
  have hadd : x + 1#64 = BitVec.ofInt 64 (secs + 1) := by
    rw [hx, BitVec.ofInt_add]
    rfl
  exact ⟨hv, hadd⟩

theorem timeAdd_stackFrameAt16_eq (sp : BitVec 64) :
    stackFrameAt sp 16 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1) := rfl

theorem timeAdd_stackFrameAt16_unfold (sp : BitVec 64) :
    stackFrameAt sp 16 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1) :=
  Entails.refl _

theorem timeAdd_stackFrameAt16_fold (sp w0 w1 : BitVec 64) :
    ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1) ⊢ stackFrameAt sp 16 := by
  sep_entail

theorem conditionHolds_vs_addsPState64 (x y : BitVec 64) :
    ConditionHolds .VS (addsPState64 x y) = (AddWithCarry64 x y false).2.v := by
  rw [addsPState64.eq_def, ConditionHolds.eq_def]

theorem conditionHolds_vc_addsPState64 (x y : BitVec 64) :
    ConditionHolds .VC (addsPState64 x y) = !(AddWithCarry64 x y false).2.v := by
  rw [addsPState64.eq_def, ConditionHolds.eq_def]

theorem timeAdd_tbnz_guard (sec dsecs : BitVec 64) :
    (BitVec.setWidth 64
      (BitVec.setWidth 32
        ((if ¬dsecs.msb = true then 0#64 else 1#64) ^^^
          if ConditionHolds .VC (addsPState64 sec dsecs) = true then 0#64 else 1#64))).getLsbD 0 =
      decide ((2 ^ 63 - 1 : Int) < sec.toInt + (dsecs.toNat : Int)) := by
  rw [conditionHolds_vc_addsPState64, ← timeAdd_v_bne_msb_eq_overflow]
  generalize (AddWithCarry64 sec dsecs false).2.v = v
  generalize dsecs.msb = m
  cases v <;> cases m <;> decide

theorem timeAdd_nsec_ult_billion (nsec nanos : BitVec 32)
    (hn1 : nsec.toNat < 10 ^ 9) (hn2 : nanos.toNat < 10 ^ 9) :
    BitVec.ult (nanos + nsec) 1000000000#32 = decide (¬ (10 ^ 9 ≤ nsec.toNat + nanos.toNat)) := by
  have htn := (timeAdd_nsec_add_toNat nsec nanos hn1 hn2).1
  simp only [BitVec.ult, htn, show (1000000000#32).toNat = 10 ^ 9 from rfl]
  by_cases h : 10 ^ 9 ≤ nsec.toNat + nanos.toNat
  · have hlt : ¬ (nsec.toNat + nanos.toNat < 10 ^ 9) := by omega
    simp [h, hlt]
  · have hlt : nsec.toNat + nanos.toNat < 10 ^ 9 := by omega
    simp [h, hlt]

theorem timeAdd_carry_vs_guard (secs : Int)
    (hlo : -(2 ^ 63 : Int) ≤ secs) (hhi : secs ≤ 2 ^ 63 - 1) :
    ConditionHolds .VS (addsPState64 (BitVec.ofInt 64 secs) 1#64) =
      decide ((2 ^ 63 - 1 : Int) < secs + 1) := by
  rw [conditionHolds_vs_addsPState64]
  exact (timeAdd_carry_v_eq_overflow (BitVec.ofInt 64 secs) secs rfl hlo hhi).1

theorem timeAdd_carry_vs_guard_add (sec dsecs : BitVec 64)
    (h : ¬ ((2 ^ 63 - 1 : Int) < sec.toInt + (dsecs.toNat : Int))) :
    ConditionHolds .VS (addsPState64 (sec + dsecs) 1#64) =
      decide ((2 ^ 63 - 1 : Int) < (sec.toInt + (dsecs.toNat : Int)) + 1) := by
  obtain ⟨heq, _, hlo, hhi⟩ := timeAdd_sec_add_no_overflow sec dsecs h
  rw [heq]
  exact timeAdd_carry_vs_guard _ hlo hhi

end VerifiedLibraries.RustStd.TimeAddLemmas
