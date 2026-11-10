/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.BV
public import VerifiedLibraries.Mallocng.Proofs.Common
import VerifiedLibraries.Mallocng.Proofs.MallocLargeProof

/-!
# Shared `__rustc::__rdl_*` Shim Helpers

Proves alignment, permission-congruence, preservation transitivity, and `memRegion` / `↦₆₄`
spatial lemmas shared across the placed `__rustc::__rdl_*` allocator shim proofs.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

private theorem and_neg_eq_self_of_and_sub_one_zero {a : BitVec 64}
    (h : (a &&& (a - 1#64)) = 0#64) : (a &&& (0#64 - a)) = a := by
  revert h; bv_robdd

private theorem alignedAllocAlignOk_of_pow2 {align : BitVec 64} (hPow2 : IsPow2Align align) :
    alignedAllocAlignOk align = true := by
  unfold alignedAllocAlignOk
  exact beq_iff_eq.mpr (and_neg_eq_self_of_and_sub_one_zero hPow2.2)

private theorem isPow2Align_of_pow2 {align : BitVec 64} (hPow2 : IsPow2Align align) :
    isPow2Align align = true :=
  decide_eq_true hPow2

private theorem isPow2Align_8 : IsPow2Align 8#64 := by
  unfold IsPow2Align; decide

theorem pow2_dvd_16_of_le_16 {align : BitVec 64} (hPow2 : IsPow2Align align)
    (hle : align.toNat ≤ 16) : align.toNat ∣ 16 := by
  obtain ⟨hne0, hand⟩ := hPow2
  have hpos : 0 < align.toNat := by
    cases Nat.eq_zero_or_pos align.toNat with
    | inl hz => exact False.elim (hne0 (BitVec.eq_of_toNat_eq hz))
    | inr hp => exact hp
  have hEq : align = BitVec.ofNat 64 align.toNat := (BitVec.ofNat_toNat 64 align).symm
  have hCases :
      align.toNat = 1 ∨ align.toNat = 2 ∨ align.toNat = 3 ∨ align.toNat = 4 ∨
      align.toNat = 5 ∨ align.toNat = 6 ∨ align.toNat = 7 ∨ align.toNat = 8 ∨
      align.toNat = 9 ∨ align.toNat = 10 ∨ align.toNat = 11 ∨ align.toNat = 12 ∨
      align.toNat = 13 ∨ align.toNat = 14 ∨ align.toNat = 15 ∨ align.toNat = 16 := by omega
  rcases hCases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals (rw [h] at hEq ⊢; try (rw [hEq] at hand; revert hand; decide))

theorem pow2_dvd_max16 {align : BitVec 64} (hPow2 : IsPow2Align align) :
    align.toNat ∣ max align.toNat 16 := by
  by_cases hle : align.toNat ≤ 16
  · rw [Nat.max_eq_right hle]; exact pow2_dvd_16_of_le_16 hPow2 hle
  · rw [Nat.max_eq_left (by omega)]; exact Nat.dvd_refl _

namespace RdlAllocH
theorem cond_hi_subs64_iff_lt (a b : BitVec 64) :
    ConditionHolds .HI (subsPState64 a b) = true ↔ b.toNat < a.toNat := by
  have h1 : ConditionHolds .HI (subsPState64 a b) = true ↔ b < a := by
    unfold subsPState64; bv_robdd
  simpa [BitVec.lt_def] using h1
end RdlAllocH
export RdlAllocH (cond_hi_subs64_iff_lt)

theorem cond_eq_subs32_iff_eq (a b : BitVec 32) :
    ConditionHolds .EQ (subsPState32 a b) = true ↔ a = b := by
  unfold subsPState32; bv_robdd

theorem effAlign_props {align size : BitVec 64}
    (hPow2 : IsPow2Align align) (hMax : align.toNat ≤ MaxAlignedAllocAlign) :
    let effAlign := if ConditionHolds .HI (subsPState64 align 8#64) then align else 8#64
    effAlign.toNat = max align.toNat 8 ∧
    8 ≤ effAlign.toNat ∧
    effAlign.toNat ≤ MaxAlignedAllocAlign ∧
    IsPow2Align effAlign ∧
    max effAlign.toNat 16 = max align.toNat 16 ∧
    mallocngAlignedEffSize effAlign.toNat size.toNat =
      mallocngAlignedEffSize align.toNat size.toNat ∧
    mallocngPosixMemalignOk effAlign size = decide (MallocngLayoutFit size align) ∧
    mallocngPosixMemalignRet effAlign size =
      (if MallocngLayoutFit size align then 0#32 else 12#32) := by
  dsimp only
  have hBase :
      let effAlign := if ConditionHolds .HI (subsPState64 align 8#64) then align else 8#64
      effAlign.toNat = max align.toNat 8 ∧
      8 ≤ effAlign.toNat ∧
      effAlign.toNat ≤ MaxAlignedAllocAlign ∧
      IsPow2Align effAlign ∧
      max effAlign.toNat 16 = max align.toNat 16 := by
    dsimp only
    split
    · next hgt =>
      have h8lt : 8 < align.toNat := by
        have := (cond_hi_subs64_iff_lt align 8#64).mp hgt
        simpa using this
      exact ⟨by omega, by omega, hMax, hPow2, by omega⟩
    · next hgt =>
      have h8ge : align.toNat ≤ 8 := by
        have hnot : ¬ (8#64).toNat < align.toNat := fun h =>
          hgt ((cond_hi_subs64_iff_lt align 8#64).mpr h)
        change ¬ 8 < align.toNat at hnot; omega
      refine ⟨?_, ?_, ?_, isPow2Align_8, ?_⟩
      · change 8 = max align.toNat 8; omega
      · change 8 ≤ 8; omega
      · change 8 ≤ MaxAlignedAllocAlign; unfold MaxAlignedAllocAlign; omega
      · change max 8 16 = max align.toNat 16; omega
  obtain ⟨hNat, hGe8, hLeMax, hPowEff, hMax16⟩ := hBase
  have hEffSz :
      mallocngAlignedEffSize
        (if ConditionHolds .HI (subsPState64 align 8#64) then align else 8#64).toNat size.toNat =
      mallocngAlignedEffSize align.toNat size.toNat := by
    rw [hNat]; unfold mallocngAlignedEffSize; split <;> split <;> omega
  have hAlOk : alignedAllocAlignOk
      (if ConditionHolds .HI (subsPState64 align 8#64) then align else 8#64) = true :=
    alignedAllocAlignOk_of_pow2 hPowEff
  have hIsP2 : isPow2Align
      (if ConditionHolds .HI (subsPState64 align 8#64) then align else 8#64) = true :=
    isPow2Align_of_pow2 hPowEff
  have hGe8T : decide (8 ≤
      (if ConditionHolds .HI (subsPState64 align 8#64) then align else 8#64).toNat) = true :=
    decide_eq_true hGe8
  refine ⟨hNat, hGe8, hLeMax, hPowEff, hMax16, hEffSz, ?_, ?_⟩
  · unfold mallocngPosixMemalignOk mallocngAlignedAllocOk MallocngLayoutFit
    rw [hGe8T, hAlOk, hEffSz]; rfl
  · unfold mallocngPosixMemalignRet MallocngLayoutFit
    rw [hIsP2, hEffSz, hNat]
    have hNot8 : ¬ max align.toNat 8 < 8 := by omega
    by_cases hfit : mallocngAlignedEffSize align.toNat size.toNat ≤ MallocngMaxAllocSize <;>
      simp [hNot8, hfit]

namespace RdlAllocH
theorem mappedDelta_congr_perm {k nb : Nat} {m0 m0' mf mf' : Memory}
    (h0 : m0'.perm = m0.perm) (hf : mf.perm = mf'.perm)
    (hd : MallocngMappedDelta k nb m0' mf') : MallocngMappedDelta k nb m0 mf := by
  obtain ⟨ivs, hlen, hsum, hcov⟩ := hd
  refine ⟨ivs, hlen, hsum, fun a ha => ?_⟩
  rw [hf] at ha
  rcases hcov a ha with hm0' | hiv
  · exact Or.inl (by rwa [← h0])
  · exact Or.inr hiv

theorem noOrphanMappings_congr_perm {ivs0 ivsf : List (BitVec 64 × Nat)}
    {m0 m0' mf mf' : Memory} (h0 : m0'.perm = m0.perm) (hf : mf.perm = mf'.perm)
    (hno : MallocngNoOrphanMappings ivs0 ivsf m0' mf') :
    MallocngNoOrphanMappings ivs0 ivsf m0 mf := by
  intro a ha hsrc; rw [hf] at ha; rw [← h0] at hsrc; exact hno a ha hsrc
end RdlAllocH
export RdlAllocH (mappedDelta_congr_perm noOrphanMappings_congr_perm)

theorem procPreserved_trans {s0 s1 s2 : State}
    (h01 : MallocngProcPreserved s0 s1) (h12 : MallocngProcPreserved s1 s2) :
    MallocngProcPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

theorem calleeSavedPreserved_trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  obtain ⟨a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, av⟩ := h01
  obtain ⟨b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, bv⟩ := h12
  exact ⟨b19.trans a19, b20.trans a20, b21.trans a21, b22.trans a22, b23.trans a23,
    b24.trans a24, b25.trans a25, b26.trans a26, b27.trans a27, b28.trans a28,
    b29.trans a29, bv.trans av⟩

theorem pointsTo64_entails_memRegion8 (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ memRegion a 8 :=
  (IsBlock.pointsTo64 a v).entails_memRegion

namespace RdlAllocH
theorem memRegion8_entails_exists_pointsTo64 (a : BitVec 64) :
    memRegion a 8 ⊢ ∃∗ v : BitVec 64, a ↦₆₄ v := by
  rw [memRegion_uncons a (by omega) (by omega), show 8 - 8 = 0 by rfl, memRegion_zero]
  refine Entails.sepExists_mono fun v => ?_
  rw [sepConj_emp]; exact Entails.refl _
end RdlAllocH
export RdlAllocH (memRegion8_entails_exists_pointsTo64)

end VerifiedLibraries.Mallocng.Proofs
