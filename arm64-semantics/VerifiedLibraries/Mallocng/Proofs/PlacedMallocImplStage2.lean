/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplStage1
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocLargeHelpers
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Placed `__libc_malloc_impl` Stage 2: Small and Medium Path

Proves symbolic execution of the small/medium path in `blk09` (`__libc_malloc_impl`), covering
`size_to_class`, the lock check (`mallocImpl_sizeToClass_lock_step`), and the even-class coarse
size-class bump (`coarseBump_sc_props`, `mallocImpl_coarse_step`) up to `miOff_try_avail` and
`miOff_alloc_prep`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Symbolic Offsets and Size-Class / Coarse-Bump Lemmas -/

abbrev miOff_small_entry : BitVec 64 := words_insn_off% mallocImplWords 0x91000e93#32 0
abbrev miOff_after_lock  : BitVec 64 := words_insn_off% mallocImplWords 0x91002aa0#32 0
abbrev miOff_try_avail   : BitVec 64 := words_insn_off% mallocImplWords 0xb4000d36#32 0
abbrev miOff_alloc_prep  : BitVec 64 := words_insn_off% mallocImplWords 0xaa1403e1#32 0
abbrev miOff_call_slot   : BitVec 64 :=
  reloc_call_off% VerifiedLibraries.mallocng_blk09_libc_malloc_impl.relocs "alloc_slot" 0
abbrev miOff_after_slot  : BitVec 64 := words_insn_off% mallocImplWords 0x2a0003f7#32 0

@[simp, arm64_norm, wp_norm]
theorem pageOf_add_zext_lo12Of (T : BitVec 64) :
    pageOf T + BitVec.zeroExtend 64 ((lo12Of T).truncate 12) = T := by
  have h : BitVec.zeroExtend 64 ((lo12Of T).truncate 12) = lo12Of T := by
    unfold lo12Of; bv_bits
  rw [h, pageOf_add_lo12Of]

theorem coarseBump_sc_props {req sc : Nat} (hReq : req ≤ 131051)
    (hScChoice :
      let sc0 := sizeToClassUnits ((req + 3) / 16)
      sc = sc0 ∨ (4 ≤ sc0 ∧ sc0 ≤ 31 ∧ sc0 ≠ 6 ∧ sc0 % 2 = 0 ∧ sc = sc0 + 1)) :
    sc < 48 ∧
    req ≤ nominalSlotCap sc ∧
    (2 ≤ sc ∧ sc < 48 → nominalSlotCap (sc - 2) < max req 16) ∧
    (sc = 24 → nominalSlotCap 23 < req) ∧
    (sc = 24 → nominalSlotCap 23 < max req MallocngMinBlockCost) := by
  dsimp only at hScChoice
  obtain ⟨hsc0_lt, hfit0, hmin0⟩ := sizeToClass_spec hReq
  generalize hsc0_eq : sizeToClassUnits ((req + 3) / 16) = sc0 at hsc0_lt hfit0 hmin0 hScChoice
  rcases hScChoice with rfl | ⟨hlo, hhi, _, hpar, rfl⟩
  · refine ⟨hsc0_lt, hfit0, ?_, ?_, ?_⟩
    · rintro ⟨h2, _⟩
      have hne0 : sc ≠ 0 := by omega
      have hprev : nominalSlotCap (sc - 1) < req := hmin0.resolve_left hne0
      have hmono := sizeClass_strictMono (sc₁ := sc - 2) (sc₂ := sc - 1) (by omega) (by omega)
      have hb2 := (sizeClass_bounds (sc := sc - 2) (by omega)).1
      unfold nominalSlotCap at hprev ⊢
      omega
    · intro h24
      subst h24
      exact hmin0.resolve_left (by decide)
    · intro h24
      subst h24
      have hprev : nominalSlotCap 23 < req := hmin0.resolve_left (by decide)
      omega
  · have hlt48 : sc0 + 1 < 48 := by omega
    have hmono := sizeClass_strictMono (sc₁ := sc0) (sc₂ := sc0 + 1) (by omega) hlt48
    have hb0 := (sizeClass_bounds (sc := sc0) (by omega)).1
    have hprev : nominalSlotCap (sc0 - 1) < req := hmin0.resolve_left (by omega)
    refine ⟨hlt48, ?_, ?_, ?_, ?_⟩
    · unfold nominalSlotCap at hfit0 ⊢; omega
    · rintro ⟨_, _⟩
      have hsub : sc0 + 1 - 2 = sc0 - 1 := by omega
      rw [hsub]; omega
    · intro h24; omega
    · intro h24; omega

/-! ## `size_to_class` and Lock Check (`+0x03c .. +0x0dc`) -/

private theorem sizeToClass_entry_bv (req : Nat) (hReq : req ≤ 131051) :
    let u := (req + 3) / 16
    BitVec.ofNat 64 req + 3#64 = BitVec.ofNat 64 (req + 3) ∧
    (BitVec.ofNat 64 (req + 3) >>> 4) = BitVec.ofNat 64 u ∧
    (((BitVec.ofNat 64 (req + 3)).ule 0x9f#64 = true) ↔ u ≤ 9) ∧
    (((0x9f#64).ult (BitVec.ofNat 64 (req + 3)) = true) ↔ 10 ≤ u) ∧
    (u ≤ 9 → BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 u)) = BitVec.ofNat 64 u) := by
  intro u
  have hlt64 : req + 3 < 2 ^ 64 := by omega
  have hAdd : BitVec.ofNat 64 req + 3#64 = BitVec.ofNat 64 (req + 3) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hShr : BitVec.ofNat 64 (req + 3) >>> 4 = BitVec.ofNat 64 u := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, u]
    have : (req + 3) % 2 ^ 64 = req + 3 := Nat.mod_eq_of_lt hlt64
    rw [this, Nat.shiftRight_eq_div_pow]
    have hdivlt : (req + 3) / 16 < 2 ^ 64 := by omega
    exact (Nat.mod_eq_of_lt hdivlt).symm
  have hLe : ((BitVec.ofNat 64 (req + 3)).ule 0x9f#64 = true) ↔ u ≤ 9 := by
    simp only [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, u]
    change req + 3 ≤ 159 ↔ (req + 3) / 16 ≤ 9
    omega
  have hGt : ((0x9f#64).ult (BitVec.ofNat 64 (req + 3)) = true) ↔ 10 ≤ u := by
    simp only [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, u]
    change 159 < req + 3 ↔ 10 ≤ (req + 3) / 16
    omega
  refine ⟨hAdd, hShr, hLe, hGt, fun hu => ?_⟩
  have hU : (List.range 10).all (fun k =>
    decide (BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 k)) = BitVec.ofNat 64 k)) = true := by
    decide
  exact of_decide_eq_true (List.all_eq_true.mp hU u (List.mem_range.mpr (by omega)))

private theorem sc_sxtw_bv (sc : Nat) (hsc : sc < 48) :
    BitVec.signExtend 64 (BitVec.ofNat 32 sc) = BitVec.ofNat 64 sc ∧
    BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 sc)) = BitVec.ofNat 64 sc ∧
    (BitVec.signExtend 64 (BitVec.ofNat 32 sc) <<< 1) = BitVec.ofNat 64 (2 * sc) ∧
    (BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 sc)) <<< 1) = BitVec.ofNat 64 (2 * sc) := by
  have hAll : (List.range 48).all (fun k =>
    decide (BitVec.signExtend 64 (BitVec.ofNat 32 k) = BitVec.ofNat 64 k ∧
      BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 k)) = BitVec.ofNat 64 k ∧
      (BitVec.signExtend 64 (BitVec.ofNat 32 k) <<< 1) = BitVec.ofNat 64 (2 * k) ∧
      (BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 k)) <<< 1) = BitVec.ofNat 64 (2 * k))) = true := by
    decide
  exact of_decide_eq_true (List.all_eq_true.mp hAll sc (List.mem_range.mpr hsc))

abbrev miOff_stc_ldrb   : BitVec 64 := words_insn_off% mallocImplWords 0x38604873#32 0
abbrev miOff_stc_after_ldrb  : BitVec 64 := words_insn_off% mallocImplWords 0x51000673#32 0
abbrev miOff_stc_ldrh1  : BitVec 64 := words_insn_off% mallocImplWords 0x7863d843#32 0
abbrev miOff_stc_after_ldrh1 : BitVec 64 := words_insn_off% mallocImplWords 0xeb03003f#32 0
abbrev miOff_stc_ldrh2  : BitVec 64 := words_insn_off% mallocImplWords 0x7873d840#32 0
abbrev miOff_stc_after_ldrh2 : BitVec 64 := words_insn_off% mallocImplWords 0xeb00003f#32 0
abbrev miOff_stc_sxtw   : BitVec 64 := words_insn_off% mallocImplWords 0x93407e75#32 1
abbrev miOff_lock_check : BitVec 64 := words_insn_off% mallocImplWords 0x90000000#32 0

private theorem zext32_eq_ofNat (w : BitVec 32) :
    BitVec.zeroExtend 64 w = BitVec.ofNat 64 w.toNat := by
  simp

private theorem zext8_eq_ofNat (w : BitVec 8) :
    BitVec.zeroExtend 64 w = BitVec.ofNat 64 w.toNat := by
  simp

private theorem zext16_ofNat_eq (n : Nat) (hn : n < 65536) :
    BitVec.zeroExtend 64 (BitVec.ofNat 16 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

@[simp, arm64_norm, wp_norm]
theorem setWidth32_lsr_setWidth64 (w : BitVec 32) (k : Nat) :
    BitVec.setWidth 32 (BitVec.setWidth 64 w >>> k) = w >>> k := by
  apply BitVec.eq_of_toNat_eq
  have hw := w.isLt
  have h64 : w.toNat % 2 ^ 64 = w.toNat := Nat.mod_eq_of_lt (by omega)
  have hle : w.toNat >>> k ≤ w.toNat := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, h64]
  exact Nat.mod_eq_of_lt (by omega)

@[simp, arm64_norm, wp_norm]
theorem setWidth32_shl_setWidth64 (w : BitVec 32) (k : Nat) :
    BitVec.setWidth 32 (BitVec.setWidth 64 w <<< k) = w <<< k := by
  ext i hi; simp

@[simp, arm64_norm, wp_norm]
theorem setWidth32_add_setWidth64 (a b : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 a + BitVec.setWidth 64 b) = a + b := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.add_mod]

@[simp, arm64_norm, wp_norm]
theorem setWidth32_sub_setWidth64 (a b : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 a - BitVec.setWidth 64 b) = a - b := by
  bv_omega

@[simp, arm64_norm, wp_norm]
theorem setWidth32_mul_setWidth64 (a b : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 a * BitVec.setWidth 64 b) = a * b := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, BitVec.toNat_setWidth, Nat.mul_mod]

@[simp, arm64_norm, wp_norm]
theorem setWidth32_not_setWidth64 (a : BitVec 32) :
    BitVec.setWidth 32 (~~~(BitVec.setWidth 64 a)) = ~~~a := by
  bv_bits

@[simp, arm64_norm, wp_norm]
theorem setWidth64_setWidth32_8 (w : BitVec 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 w) = BitVec.setWidth 64 w := by
  bv_bits

@[simp, arm64_norm, wp_norm]
theorem setWidth64_setWidth32_16 (w : BitVec 16) :
    BitVec.setWidth 64 (BitVec.setWidth 32 w) = BitVec.setWidth 64 w := by
  bv_bits

@[simp, arm64_norm, wp_norm]
theorem ofNat64_shl_one (n : Nat) :
    BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

private theorem sxtw_sbfm_all :
    (List.range 48).all (fun k =>
      decide (((BitVec.ofNat 64 k &&& 4294967295#64) |||
        ((if (BitVec.ofNat 64 k)[31] = true then 0xffffffffffffffff#64 else 0#64) &&&
          0xffffffff00000000#64)) = BitVec.ofNat 64 k)) = true := by decide

theorem sxtw_sbfm_ofNat {n : Nat} (hn : n < 48) :
    (BitVec.ofNat 64 n &&& 4294967295#64) |||
    ((if (BitVec.ofNat 64 n)[31] = true then 0xffffffffffffffff#64 else 0#64) &&&
      0xffffffff00000000#64) = BitVec.ofNat 64 n :=
  of_decide_eq_true (List.all_eq_true.mp sxtw_sbfm_all n (List.mem_range.mpr hn))

theorem uxtw_mask_ofNat {n : Nat} (hn : n < 65536) :
    BitVec.ofNat 64 n &&& 4294967295#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  have hlt : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  change n &&& (2 ^ 32 - 1) = n
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by omega)

private theorem readLE_sizeClassBytes {sc : Nat} (hsc : sc < 48) :
    ByteSlice.readLE sizeClassBytes (2 * sc) 2 = BitVec.ofNat 64 (sizeClass sc) := by
  have hB := (sizeClass_bounds (sc := sc) hsc).2.1
  rw [ByteSlice.readLE_two, pack16_sizeClassBytes hsc]
  exact zext16_ofNat_eq _ (Nat.lt_of_le_of_lt hB (by decide))

theorem sizeToClass_large_bv_pure
    {u bVal baseSc sc1 sz1 sz2 sc2 : Nat}
    (hu_hi : u ≤ 8190) (hb_lo : 2 ≤ bVal) (hb_hi : bVal ≤ 12)
    (hbaseEq : baseSc = (bVal - 1) * 4)
    (hbaseLt : baseSc + 2 < 48) (_hsc1Lt : sc1 < 48)
    (hsz1Lt : sz1 < 65536) (hsz2Lt : sz2 < 65536)
    (hsc1Eq : sc1 = if u + 1 > sz1 then baseSc + 2 else baseSc)
    (hsc2Eq : sc2 = if u + 1 > sz2 then sc1 + 1 else sc1) :
    BitVec.ofNat 64 u + 1#64 = BitVec.ofNat 64 (u + 1) ∧
    BitVec.truncate 32 (BitVec.ofNat 64 (u + 1)) = BitVec.ofNat 32 (u + 1) ∧
    (BitVec.truncate 32 (BitVec.ofNat 64 bVal) - 1#32) <<< 2 = BitVec.ofNat 32 baseSc ∧
    BitVec.ofNat 32 baseSc + 1#32 = BitVec.ofNat 32 (baseSc + 1) ∧
    BitVec.ofNat 32 baseSc + 2#32 = BitVec.ofNat 32 (baseSc + 2) ∧
    BitVec.zeroExtend 64
      (if (BitVec.ofNat 64 sz1).ult (BitVec.ofNat 64 (u + 1)) = true then
        BitVec.truncate 32 (BitVec.ofNat 64 (baseSc + 2))
      else BitVec.truncate 32 (BitVec.ofNat 64 baseSc)) = BitVec.ofNat 64 sc1 ∧
    ((BitVec.ofNat 64 (u + 1)).ule (BitVec.ofNat 64 sz2) = true → sc2 = sc1) ∧
    (¬ ((BitVec.ofNat 64 (u + 1)).ule (BitVec.ofNat 64 sz2) = true) → sc2 = sc1 + 1) ∧
    BitVec.ofNat 32 sc1 + 1#32 = BitVec.ofNat 32 (sc1 + 1) := by
  have hAddU : BitVec.ofNat 64 u + 1#64 = BitVec.ofNat 64 (u + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hTrU : BitVec.truncate 32 (BitVec.ofNat 64 (u + 1)) = BitVec.ofNat 32 (u + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have hBaseBv : (BitVec.truncate 32 (BitVec.ofNat 64 bVal) - 1#32) <<< 2 = BitVec.ofNat 32 baseSc := by
    have hB : (List.range 13).all (fun k =>
      if 2 ≤ k then decide ((BitVec.truncate 32 (BitVec.ofNat 64 k) - 1#32) <<< 2 = BitVec.ofNat 32 ((k - 1) * 4))
      else true) = true := by decide
    have hc := List.all_eq_true.mp hB bVal (List.mem_range.mpr (by omega))
    simpa [hb_lo, hbaseEq] using hc
  have hB1 : BitVec.ofNat 32 baseSc + 1#32 = BitVec.ofNat 32 (baseSc + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hB2 : BitVec.ofNat 32 baseSc + 2#32 = BitVec.ofNat 32 (baseSc + 2) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hCmp1 : ((BitVec.ofNat 64 sz1).ult (BitVec.ofNat 64 (u + 1)) = true) ↔ (u + 1 > sz1) := by
    simp only [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : sz1 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : u + 1 < 2 ^ 64), gt_iff_lt]
  have hCsel : BitVec.zeroExtend 64
      (if (BitVec.ofNat 64 sz1).ult (BitVec.ofNat 64 (u + 1)) = true then
        BitVec.truncate 32 (BitVec.ofNat 64 (baseSc + 2))
      else BitVec.truncate 32 (BitVec.ofNat 64 baseSc)) = BitVec.ofNat 64 sc1 := by
    by_cases hGt1 : u + 1 > sz1
    · have hUlt1 : (BitVec.ofNat 64 sz1).ult (BitVec.ofNat 64 (u + 1)) = true := hCmp1.mpr hGt1
      simp only [hUlt1, ↓reduceIte, hsc1Eq, hGt1]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    · have hNotUlt1 : ¬ ((BitVec.ofNat 64 sz1).ult (BitVec.ofNat 64 (u + 1)) = true) := mt hCmp1.mp hGt1
      simp only [hNotUlt1, Bool.false_eq_true, ↓reduceIte, hsc1Eq, hGt1]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have hCmp2 : ((BitVec.ofNat 64 (u + 1)).ule (BitVec.ofNat 64 sz2) = true) ↔ ¬ (u + 1 > sz2) := by
    simp only [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : sz2 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : u + 1 < 2 ^ 64)]
    omega
  have hSc2Le : (BitVec.ofNat 64 (u + 1)).ule (BitVec.ofNat 64 sz2) = true → sc2 = sc1 := by
    intro hUle; simp [hsc2Eq, hCmp2.mp hUle]
  have hSc2Gt : ¬ ((BitVec.ofNat 64 (u + 1)).ule (BitVec.ofNat 64 sz2) = true) → sc2 = sc1 + 1 := by
    intro hNUle; have hGt : u + 1 > sz2 := by have := mt hCmp2.mpr hNUle; omega
    simp [hsc2Eq, hGt]
  have hS1Add : BitVec.ofNat 32 sc1 + 1#32 = BitVec.ofNat 32 (sc1 + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact ⟨hAddU, hTrU, hBaseBv, hB1, hB2, hCsel, hSc2Le, hSc2Gt, hS1Add⟩

def sizeToClassHashRaw (u : Nat) : BitVec 32 :=
  let w1 : BitVec 32 := BitVec.ofNat 32 (u + 1)
  let w0a := (w1 >>> 2) ||| (w1 >>> 1)
  let w0b := w0a ||| (w0a >>> 2)
  let w0d := (w0b ||| (w0b >>> 4)) ||| ((w0b ||| (w0b >>> 4)) >>> 8)
  let p2  := (w0d + 1#32) &&& (~~~w0d)
  (p2 * 0x076be629#32) >>> 27

theorem sizeToClass_large_unpack (u : Nat) (hu_lo : 10 ≤ u) (hu_hi : u ≤ 8190) :
    ∃ (idx : Nat) (bByte : BitVec 8) (baseSc sc1 sz1 sz2 : Nat),
      debruijn32Table.getD idx 0#8 = bByte ∧
      ByteSlice.readLE sizeClassBytes (2 * (baseSc + 1)) 2 = BitVec.ofNat 64 sz1 ∧
      ByteSlice.readLE sizeClassBytes (2 * sc1) 2 = BitVec.ofNat 64 sz2 ∧
      idx < 32 ∧ baseSc + 2 < 48 ∧ sc1 < 48 ∧
      BitVec.ofNat 64 u + 1#64 = BitVec.ofNat 64 (u + 1) ∧
      BitVec.truncate 32 (BitVec.ofNat 64 (u + 1)) = BitVec.ofNat 32 (u + 1) ∧
      BitVec.zeroExtend 64 (sizeToClassHashRaw u) = BitVec.ofNat 64 idx ∧
      (BitVec.truncate 32 (BitVec.ofNat 64 bByte.toNat) - 1#32) <<< 2 = BitVec.ofNat 32 baseSc ∧
      BitVec.ofNat 32 baseSc + 1#32 = BitVec.ofNat 32 (baseSc + 1) ∧
      BitVec.ofNat 32 baseSc + 2#32 = BitVec.ofNat 32 (baseSc + 2) ∧
      BitVec.zeroExtend 64
        (if (BitVec.ofNat 64 sz1).ult (BitVec.ofNat 64 (u + 1)) = true then
          BitVec.truncate 32 (BitVec.ofNat 64 (baseSc + 2))
        else BitVec.truncate 32 (BitVec.ofNat 64 baseSc)) = BitVec.ofNat 64 sc1 ∧
      ((BitVec.ofNat 64 (u + 1)).ule (BitVec.ofNat 64 sz2) = true → sizeToClassUnits u = sc1) ∧
      (¬ ((BitVec.ofNat 64 (u + 1)).ule (BitVec.ofNat 64 sz2) = true) →
        sizeToClassUnits u = sc1 + 1 ∧ sc1 + 1 < 48) ∧
      BitVec.ofNat 32 sc1 + 1#32 = BitVec.ofNat 32 (sc1 + 1) := by
  have hnot9 : ¬ u ≤ 9 := by omega
  have hHash : BitVec.zeroExtend 64 (sizeToClassHashRaw u) = BitVec.ofNat 64 (sizeToClassHashIdx u) :=
    zext32_eq_ofNat _
  have hUnits : sizeToClassUnits u =
      (let idx := sizeToClassHashIdx u
       let b := (debruijn32Table.getD idx 0#8).toNat
       let baseSc := (b - 1) * 4
       let sc1 := if u + 1 > sizeClass (baseSc + 1) then baseSc + 2 else baseSc
       if u + 1 > sizeClass sc1 then sc1 + 1 else sc1) := by
    unfold sizeToClassUnits
    exact ite_eq_right hnot9
  have hok := sizeToClassLarge_spec hu_lo hu_hi
  unfold sizeToClassLargeOk at hok
  dsimp only at hok hUnits
  generalize sizeToClassHashIdx u = idx at hok hUnits hHash
  generalize hDebEq : debruijn32Table.getD idx 0#8 = bByte at hok hUnits
  generalize hbValEq : bByte.toNat = bVal at hok hUnits
  generalize hbaseEq : (bVal - 1) * 4 = baseSc at hok hUnits
  generalize hsz1Eq : sizeClass (baseSc + 1) = sz1 at hok hUnits
  generalize hsc1Eq : (if u + 1 > sz1 then baseSc + 2 else baseSc) = sc1 at hok hUnits
  generalize hsz2Eq : sizeClass sc1 = sz2 at hok hUnits
  generalize hsc2Eq : (if u + 1 > sz2 then sc1 + 1 else sc1) = sc2 at hok hUnits
  generalize sizeClass sc2 = sz3 at hok
  generalize sizeClass (sc2 - 1) = sz4 at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hidx, hb_lo⟩, hb_hi⟩, hbaseLt⟩, hsc1Lt⟩, hsc2Lt⟩, _⟩, _⟩, _⟩ := hok
  have hbase1Lt : baseSc + 1 < 48 := Nat.lt_of_succ_lt hbaseLt
  have hReadSc1 : ByteSlice.readLE sizeClassBytes (2 * (baseSc + 1)) 2 = BitVec.ofNat 64 sz1 := by
    rw [← hsz1Eq]; exact readLE_sizeClassBytes hbase1Lt
  have hReadSc2 : ByteSlice.readLE sizeClassBytes (2 * sc1) 2 = BitVec.ofNat 64 sz2 := by
    rw [← hsz2Eq]; exact readLE_sizeClassBytes hsc1Lt
  have hsz1Lt : sz1 < 65536 := by
    rw [← hsz1Eq]; exact Nat.lt_of_le_of_lt (sizeClass_bounds (sc := baseSc + 1) hbase1Lt).2.1 (by decide)
  have hsz2Lt : sz2 < 65536 := by
    rw [← hsz2Eq]; exact Nat.lt_of_le_of_lt (sizeClass_bounds (sc := sc1) hsc1Lt).2.1 (by decide)
  obtain ⟨hAddU, hTrU, hBaseBv, hB1, hB2, hCsel, hSc2Le, hSc2Gt, hS1Add⟩ :=
    sizeToClass_large_bv_pure hu_hi hb_lo hb_hi hbaseEq.symm hbaseLt hsc1Lt hsz1Lt hsz2Lt hsc1Eq.symm hsc2Eq.symm
  rw [← hbValEq] at hBaseBv
  have hSc2GtFull : ¬ ((BitVec.ofNat 64 (u + 1)).ule (BitVec.ofNat 64 sz2) = true) →
      sizeToClassUnits u = sc1 + 1 ∧ sc1 + 1 < 48 := by
    intro hN
    have hEq := hSc2Gt hN
    exact ⟨hUnits.trans hEq, hEq ▸ hsc2Lt⟩
  rw [← hUnits] at hSc2Le
  exact ⟨idx, bByte, baseSc, sc1, sz1, sz2, hDebEq, hReadSc1, hReadSc2, hidx, hbaseLt, hsc1Lt,
    hAddU, hTrU, hHash, hBaseBv, hB1, hB2, hCsel, hSc2Le, hSc2GtFull, hS1Add⟩

theorem pointsToBytesRO_focus8_at (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 1 ≤ bs.length) :
    (base ↦ᵣ bs) =
      ((base + BitVec.ofNat 64 off) ↦₈ᵣ bs.getD off 0#8) ∗
      ((base ↦ᵣ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 1)) ↦ᵣ bs.drop (off + 1))) := by
  rw [pointsToBytesRO_split3 base bs off 1 h,
      pointsToBytesRO_take1_eq_pointsTo8RO (base + BitVec.ofNat 64 off) bs off h]

theorem pointsToBytesRO_focus16_at (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 2 ≤ bs.length) :
    (base ↦ᵣ bs) =
      ((base + BitVec.ofNat 64 off) ↦₁₆ᵣ pack16 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)) ∗
      ((base ↦ᵣ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 2)) ↦ᵣ bs.drop (off + 2))) := by
  rw [pointsToBytesRO_split3 base bs off 2 h,
      pointsToBytesRO_take2_eq_pointsTo16RO (base + BitVec.ofNat 64 off) bs off h]

theorem writeReg_W32_zext8 (s : State) (rt : Reg) (v : BitVec 8) :
    s.writeReg .W32 rt (v.zeroExtend 64) = s.writeReg64 rt (BitVec.ofNat 64 v.toNat) := by
  have h : BitVec.zeroExtend 64 (BitVec.truncate 32 (v.zeroExtend 64)) = BitVec.ofNat 64 v.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := v.isLt; omega
  unfold State.writeReg; dsimp only; rw [h]

private theorem writeReg_W32_zext16 (s : State) (rt : Reg) (v : BitVec 16) :
    s.writeReg .W32 rt (v.zeroExtend 64) = s.writeReg64 rt (v.zeroExtend 64) := by
  have h : BitVec.zeroExtend 64 (BitVec.truncate 32 (v.zeroExtend 64)) = v.zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := v.isLt; omega
  unfold State.writeReg; dsimp only; rw [h]

set_option maxHeartbeats 400000 in
theorem mallocImpl_stc_table_step [MallocngMultiPlacement]
    {req u sc0 idx baseSc sc1 sz1 sz2 : Nat} {bByte : BitVec 8}
    {scAddr debAddr : BitVec 64}
    {scBytes debBytes : List (BitVec 8)} {s0 sA : State} {G : SepProp}
    (hScLen : scBytes.length = 96) (hDebLen : debBytes.length = 32)
    (hReadDeb : debBytes.getD idx 0#8 = bByte)
    (hReadSc1 : ByteSlice.readLE scBytes (2 * (baseSc + 1)) 2 = BitVec.ofNat 64 sz1)
    (hReadSc2 : ByteSlice.readLE scBytes (2 * sc1) 2 = BitVec.ofNat 64 sz2)
    (hIdxLt : idx < 32) (hBaseLt : baseSc + 2 < 48) (hSc1Lt : sc1 < 48)
    (hBaseBv : (BitVec.truncate 32 (BitVec.ofNat 64 bByte.toNat) - 1#32) <<< 2 = BitVec.ofNat 32 baseSc)
    (hB1Bv : BitVec.ofNat 32 baseSc + 1#32 = BitVec.ofNat 32 (baseSc + 1))
    (hB2Bv : BitVec.ofNat 32 baseSc + 2#32 = BitVec.ofNat 32 (baseSc + 2))
    (hCsel : BitVec.zeroExtend 64
      (if (BitVec.ofNat 64 sz1).ult (BitVec.ofNat 64 (u + 1)) = true then
        BitVec.truncate 32 (BitVec.ofNat 64 (baseSc + 2))
      else BitVec.truncate 32 (BitVec.ofNat 64 baseSc)) = BitVec.ofNat 64 sc1)
    (hSc2Le : (BitVec.ofNat 64 (u + 1)).ule (BitVec.ofNat 64 sz2) = true → sc0 = sc1)
    (hSc2Gt : ¬ ((BitVec.ofNat 64 (u + 1)).ule (BitVec.ofNat 64 sz2) = true) →
      sc0 = sc1 + 1 ∧ sc1 + 1 < 48)
    (hS1Add : BitVec.ofNat 32 sc1 + 1#32 = BitVec.ofNat 32 (sc1 + 1))
    (hpcA : sA.pc = mbase 9 + miOff_stc_ldrb) (hrunA : sA.status = .Running)
    (hspA : sA.sp = s0.sp - 80#64)
    (hProcA : MallocngProcPreserved s0 sA) (hcsA : MallocImplUntouchedCS s0 sA)
    (hx0A : sA.readReg64 (.gpr 0#5) = BitVec.ofNat 64 idx)
    (hx1A : sA.readReg64 (.gpr 1#5) = BitVec.ofNat 64 (u + 1))
    (hx2A : sA.readReg64 (.gpr 2#5) = scAddr)
    (hx3A : sA.readReg64 (.gpr 3#5) = debAddr)
    (hx20A : sA.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (mbase 9 + miOff_lock_check) sA
      (((scAddr ↦ᵣ scBytes) ∗ (debAddr ↦ᵣ debBytes) ∗ G))
      (fun s_m P_m =>
        (s_m.sp = s0.sp - 80#64 ∧ s_m.brk = sA.brk ∧ s_m.mem.perm = sA.mem.perm ∧
         MallocngProcPreserved s0 s_m ∧ MallocImplUntouchedCS s0 s_m ∧
         s_m.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc0 ∧
         s_m.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
         s_m.readReg64 (.gpr 21#5) = BitVec.ofNat 64 sc0) ∧
        (P_m ⊢ (scAddr ↦ᵣ scBytes) ∗ (debAddr ↦ᵣ debBytes) ∗ G))
      (fun _ => ⌜False⌝) := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b at hpcA ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  have _ := hb
  have hIdxUxt : BitVec.setWidth 64 (BitVec.ofNat 32 idx) = BitVec.ofNat 64 idx := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  refine SepWP.seq (mid := b + miOff_stc_ldrh1)
    (Mid := fun sB PB =>
      (sB.sp = s0.sp - 80#64 ∧ sB.brk = sA.brk ∧ sB.mem.perm = sA.mem.perm ∧
       MallocngProcPreserved s0 sB ∧ MallocImplUntouchedCS s0 sB ∧
       sB.readReg64 (.gpr 0#5) = BitVec.ofNat 64 (baseSc + 2) ∧
       sB.readReg64 (.gpr 1#5) = BitVec.ofNat 64 (u + 1) ∧
       sB.readReg64 (.gpr 2#5) = scAddr ∧
       sB.readReg64 (.gpr 3#5) = BitVec.ofNat 64 (baseSc + 1) ∧
       sB.readReg64 (.gpr 19#5) = BitVec.ofNat 64 baseSc ∧
       sB.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) ∧
      (PB ⊢ (scAddr ↦ᵣ scBytes) ∗ (debAddr ↦ᵣ debBytes) ∗ G)) ?_ ?_
  · refine SepWP.step_ldr8
      (s' := (sA.writeReg64 (.gpr 19#5) (BitVec.ofNat 64 bByte.toNat)).setPC (b + miOff_stc_after_ldrb))
      hpcA hrunA (by dsimp only [miOff_stc_ldrb]; simp only [arm64_norm]; rfl) rfl
      (ea := debAddr + BitVec.ofNat 64 idx) (wb := none)
      (by simp [evalAddrMode, extendVal, hx3A, hx0A, hIdxUxt])
      (SepLoad8.right (SepLoad8.of_pointsToBytesRO rfl (by omega) rfl))
      (by rw [applyWriteback, writeReg_W32_zext8, hReadDeb, BitVec.add_assoc]; rfl) ?_
    dsimp only [miOff_stc_after_ldrb, miOff_stc_ldrh1]
    wp_steps
    apply SepWP.done
    · simp
    · simp [hrunA]
    · have hZBase' : BitVec.zeroExtend 64 (BitVec.ofNat 32 baseSc) = BitVec.ofNat 64 baseSc := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      have hZB1 : BitVec.zeroExtend 64 (BitVec.ofNat 32 (baseSc + 1)) = BitVec.ofNat 64 (baseSc + 1) := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      have hZB2 : BitVec.zeroExtend 64 (BitVec.ofNat 32 (baseSc + 2)) = BitVec.ofNat 64 (baseSc + 2) := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      refine ⟨⟨by simp [hspA], rfl, rfl,
        by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProcA,
        untouchedCS_step hcsA (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
        ?_, by simpa using hx1A, by simpa using hx2A, ?_, ?_, by simpa using hx20A⟩, Entails.refl _⟩
      · simpa [hBaseBv, hB2Bv] using hZB2
      · simpa [hBaseBv, hB1Bv] using hZB1
      · simpa [hBaseBv] using hZBase'
  · rintro sB PB hpcB hrunB ⟨⟨hspB, hbrkB, hpermB, hProcB, hcsB, hx0B, hx1B, hx2B, hx3B, hx19B, hx20B⟩, hPB⟩
    apply SepWP.weaken_pre hPB
    have hSxMSc1 := sxtw_sbfm_ofNat hSc1Lt
    obtain ⟨_, _, hSxSc1Shl, _⟩ := sc_sxtw_bv sc1 hSc1Lt
    obtain ⟨_, _, hSxB1', _⟩ := sc_sxtw_bv (baseSc + 1) (by omega)
    have hPackSc1 : BitVec.zeroExtend 64
        (pack16 (scBytes.getD (2 * (baseSc + 1)) 0#8) (scBytes.getD (2 * (baseSc + 1) + 1) 0#8)) =
        BitVec.ofNat 64 sz1 := by
      rwa [← ByteSlice.readLE_two]
    have hPackSc2 : BitVec.zeroExtend 64
        (pack16 (scBytes.getD (2 * sc1) 0#8) (scBytes.getD (2 * sc1 + 1) 0#8)) =
        BitVec.ofNat 64 sz2 := by
      rwa [← ByteSlice.readLE_two]
    refine SepWP.seq (mid := b + miOff_stc_ldrh2)
      (Mid := fun sC PC =>
        (sC.sp = s0.sp - 80#64 ∧ sC.brk = sA.brk ∧ sC.mem.perm = sA.mem.perm ∧
         MallocngProcPreserved s0 sC ∧ MallocImplUntouchedCS s0 sC ∧
         sC.readReg64 (.gpr 1#5) = BitVec.ofNat 64 (u + 1) ∧
         sC.readReg64 (.gpr 2#5) = scAddr ∧
         sC.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc1 ∧
         sC.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
         sC.readReg64 (.gpr 21#5) = BitVec.ofNat 64 sc1) ∧
        (PC ⊢ (scAddr ↦ᵣ scBytes) ∗ (debAddr ↦ᵣ debBytes) ∗ G)) ?_ ?_
    · refine SepWP.step_ldr16
        (s' := (sB.writeReg64 (.gpr 3#5) (BitVec.ofNat 64 sz1)).setPC (b + miOff_stc_after_ldrh1))
        hpcB hrunB (by dsimp only [miOff_stc_ldrh1]; simp only [arm64_norm]; rfl) rfl
        (ea := scAddr + BitVec.ofNat 64 (2 * (baseSc + 1))) (wb := none)
        (by simp [evalAddrMode, extendVal, hx2B, hx3B, hSxB1'])
        (SepLoad16.of_pointsToBytesRO rfl (by omega) rfl)
        (by rw [applyWriteback, writeReg_W32_zext16, hPackSc1, BitVec.add_assoc]; rfl) ?_
      dsimp only [miOff_stc_after_ldrh1, miOff_stc_ldrh2]
      wp_steps
      apply SepWP.done
      · simp
      · simp [hrunB]
      · refine ⟨⟨by simp [hspB], hbrkB, hpermB,
          by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProcB,
          untouchedCS_step hcsB (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
          by simpa using hx1B, by simpa using hx2B, ?_, by simpa using hx20B, ?_⟩, Entails.refl _⟩
        · simp [arm64_norm]
        · simpa [hx0B, hx19B, hx1B, hCsel] using hSxMSc1
    · rintro sC PC hpcC hrunC ⟨⟨hspC, hbrkC, hpermC, hProcC, hcsC, hx1C, hx2C, hx19C, hx20C, hx21C⟩, hPC⟩
      apply SepWP.weaken_pre hPC
      refine SepWP.step_ldr16
        (s' := (sC.writeReg64 (.gpr 0#5) (BitVec.ofNat 64 sz2)).setPC (b + miOff_stc_after_ldrh2))
        hpcC hrunC (by dsimp only [miOff_stc_ldrh2]; simp only [arm64_norm]; rfl) rfl
        (ea := scAddr + BitVec.ofNat 64 (2 * sc1)) (wb := none)
        (by simp [evalAddrMode, extendVal, hx2C, hx19C, hSxSc1Shl])
        (SepLoad16.of_pointsToBytesRO rfl (by omega) rfl)
        (by rw [applyWriteback, writeReg_W32_zext16, hPackSc2, BitVec.add_assoc]; rfl) ?_
      dsimp only [miOff_stc_after_ldrh2, miOff_lock_check]
      wp_steps
      wp_if hBr2
      · have hSc0Eq : sc0 = sc1 := hSc2Le hBr2
        apply SepWP.done
        · simp
        · simp [hrunC]
        · refine ⟨⟨by simp [hspC], hbrkC, hpermC,
            by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProcC,
            untouchedCS_step hcsC (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
            by simpa [hSc0Eq] using hx19C, by simpa using hx20C, by simpa [hSc0Eq] using hx21C⟩, Entails.refl _⟩
      · obtain ⟨hSc0Eq, hSc2Lt48⟩ := hSc2Gt hBr2
        have hSxMSc2 := sxtw_sbfm_ofNat hSc2Lt48
        obtain ⟨hSxSc2, _, _, _⟩ := sc_sxtw_bv (sc1 + 1) hSc2Lt48
        have hZSc2 : BitVec.zeroExtend 64 (BitVec.ofNat 32 (sc1 + 1)) = BitVec.ofNat 64 (sc1 + 1) := by
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
        have hTrSc1 : BitVec.truncate 32 (BitVec.ofNat 64 sc1) = BitVec.ofNat 32 sc1 := by
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
        wp_steps
        apply SepWP.done
        · simp
        · simp [hrunC]
        · refine ⟨⟨by simp [hspC], hbrkC, hpermC,
            by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProcC,
            untouchedCS_step hcsC (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
            by simpa [hx19C, hTrSc1, hS1Add, hSc0Eq] using hZSc2,
            by simpa using hx20C,
            by simpa [hx19C, hTrSc1, hS1Add, hSc0Eq, hZSc2, hSxSc2] using hSxMSc2⟩, Entails.refl _⟩

set_option maxHeartbeats 400000 in
theorem mallocImpl_sizeToClass_lock_step [MallocngMultiPlacement]
    {tp : BitVec 64} {req sc0 : Nat} {s0 s : State} {F : SepProp}
    (hReq : req ≤ 131051)
    (hsc0 : sc0 = sizeToClassUnits ((req + 3) / 16))
    (hpc : s.pc = mbase 9 + miOff_small_entry) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (mbase 9 + miOff_after_lock) s
      (MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗ F)
      (fun s1 P1 =>
        (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
         MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
         s1.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc0 ∧
         s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
         s1.readReg64 (.gpr 21#5) = BitVec.ofNat 64 sc0 ∧
         s1.readReg64 (.gpr 24#5) = pageOf maddrs.lock) ∧
        (P1 ⊢ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗ F))
      (fun _ => ⌜False⌝) := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b at hpc ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  have _ := hb
  obtain ⟨hAdd3, hShr4, hLe9Iff, _hGt9Iff, _hSxtw9⟩ := sizeToClass_entry_bv req hReq
  have hu_hi : (req + 3) / 16 ≤ 8190 := by omega
  generalize hu_eq : (req + 3) / 16 = u at hsc0 hShr4 hLe9Iff hu_hi
  refine SepWP.seq (mid := b + miOff_lock_check)
    (Mid := fun s_m P_m =>
      (s_m.sp = s0.sp - 80#64 ∧ s_m.brk = s.brk ∧ s_m.mem.perm = s.mem.perm ∧
       MallocngProcPreserved s0 s_m ∧ MallocImplUntouchedCS s0 s_m ∧
       s_m.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc0 ∧
       s_m.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
       s_m.readReg64 (.gpr 21#5) = BitVec.ofNat 64 sc0) ∧
      (P_m ⊢ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗ F)) ?_ ?_
  · have hRoEq : MallocngRoTablesA maddrs =
        ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
         (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗
         ((maddrs.medCntTab ↦ᵣ medCntTabBytes) ∗
          (maddrs.smallCntTab ↦ᵣ smallCntTabBytes) ∗
          (maddrs.debruijnAlloc ↦ᵣ debruijn32Table))) := rfl
    rw [hRoEq]
    generalize hRoRestGen :
      ((maddrs.medCntTab ↦ᵣ medCntTabBytes) ∗
       (maddrs.smallCntTab ↦ᵣ smallCntTabBytes) ∗
       (maddrs.debruijnAlloc ↦ᵣ debruijn32Table)) = roRest at hRoEq ⊢
    wp_steps
    wp_if hBr9
    ·
      have hsc0_u : sc0 = u := by rw [hsc0]; simp [sizeToClassUnits, hBr9]
      have hSxM9 := sxtw_sbfm_ofNat (by omega : u < 48)
      wp_steps
      apply SepWP.done
      · simp
      · simp [hrun]
      · refine ⟨⟨by simp [hsp], rfl, rfl,
          by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc,
          untouchedCS_step hcsHi (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
          by simp [hsc0_u],
          by simpa using hx20,
          by simpa [hAdd3, hShr4, hsc0_u] using hSxM9⟩, ?_⟩
        rw [← hRoEq]; exact Entails.refl _
    ·
      have hu_lo : 10 ≤ u := by omega
      obtain ⟨idx, bByte, baseSc, sc1, sz1, sz2, hReadDeb, hReadSc1, hReadSc2,
        hIdxLt, hBaseLt, hSc1Lt, hAddU, hTrU, hHashBv, hBaseBv, hB1Bv, hB2Bv,
        hCsel, hSc2Le, hSc2Gt, hS1Add⟩ := sizeToClass_large_unpack u hu_lo hu_hi
      have hScLen : sizeClassBytes.length = 96 := sizeClassBytes_length
      have hDebLen : debruijn32Table.length = 32 := debruijn32Table_length
      generalize hScGen : sizeClassBytes = scBytes at hScLen hReadSc1 hReadSc2 ⊢
      generalize hDebGen : debruijn32Table = debBytes at hDebLen hReadDeb ⊢
      refine SepWP.seq (mid := b + miOff_stc_ldrb)
        (Mid := fun sA PA =>
          (sA.sp = s0.sp - 80#64 ∧ sA.brk = s.brk ∧ sA.mem.perm = s.mem.perm ∧
           MallocngProcPreserved s0 sA ∧ MallocImplUntouchedCS s0 sA ∧
           sA.readReg64 (.gpr 0#5) = BitVec.ofNat 64 idx ∧
           sA.readReg64 (.gpr 1#5) = BitVec.ofNat 64 (u + 1) ∧
           sA.readReg64 (.gpr 2#5) = maddrs.sizeClasses ∧
           sA.readReg64 (.gpr 3#5) = maddrs.debruijnFree ∧
           sA.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) ∧
          (PA ⊢ ((maddrs.sizeClasses ↦ᵣ scBytes) ∗
            (maddrs.debruijnFree ↦ᵣ debBytes) ∗ roRest) ∗ MallocngRuntime maddrs tp ∗ F)) ?_ ?_
      · wp_steps
        apply SepWP.done
        · simp
        · simp [hrun]
        · refine ⟨⟨by simp [hsp], rfl, rfl,
            by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc,
            untouchedCS_step hcsHi (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
            ?_, ?_, by simp [arm64_norm], by simp [arm64_norm], by simpa using hx20⟩, Entails.refl _⟩
          · simpa [hAdd3, hShr4, hAddU, hTrU, sizeToClassHashRaw, arm64_norm] using hHashBv
          · simp
      · rintro sA PA hpcA hrunA ⟨⟨hspA, hbrkA, hpermA, hProcA, hcsA, hx0A, hx1A, hx2A, hx3A, hx20A⟩, hPA⟩
        apply SepWP.weaken_pre (Entails.trans hPA (Entails.of_eq (by ac_rfl : (((maddrs.sizeClasses ↦ᵣ scBytes) ∗
            (maddrs.debruijnFree ↦ᵣ debBytes) ∗ roRest) ∗ MallocngRuntime maddrs tp ∗ F) =
          (maddrs.sizeClasses ↦ᵣ scBytes) ∗ (maddrs.debruijnFree ↦ᵣ debBytes) ∗
            (roRest ∗ MallocngRuntime maddrs tp ∗ F))))
        rw [← hb_eq] at hpcA ⊢
        rw [← mallocngBlockProg_eq_b09]
        refine SepWP.mono (oom := fun _ => ⌜False⌝)
          (post := fun s_m P_m =>
            (s_m.sp = s0.sp - 80#64 ∧ s_m.brk = sA.brk ∧ s_m.mem.perm = sA.mem.perm ∧
             MallocngProcPreserved s0 s_m ∧ MallocImplUntouchedCS s0 s_m ∧
             s_m.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc0 ∧
             s_m.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
             s_m.readReg64 (.gpr 21#5) = BitVec.ofNat 64 sc0) ∧
            (P_m ⊢ (maddrs.sizeClasses ↦ᵣ scBytes) ∗ (maddrs.debruijnFree ↦ᵣ debBytes) ∗
              (roRest ∗ MallocngRuntime maddrs tp ∗ F))) ?_ ?_ ?_
        · exact mallocImpl_stc_table_step hScLen hDebLen hReadDeb hReadSc1 hReadSc2
            hIdxLt hBaseLt hSc1Lt hBaseBv hB1Bv hB2Bv hCsel
            (fun h => hsc0.trans (hSc2Le h))
            (fun h => ⟨hsc0.trans (hSc2Gt h).1, (hSc2Gt h).2⟩)
            hS1Add hpcA hrunA hspA hProcA hcsA hx0A hx1A hx2A hx3A hx20A
        · rintro s_m P_m _hpc_m _hrun_m ⟨⟨hspm, hbrkm, hpermm, hProcm, hcsm, hx19m, hx20m, hx21m⟩, hPm⟩
          refine ⟨⟨hspm, hbrkm.trans hbrkA, hpermm.trans hpermA, hProcm, hcsm, hx19m, hx20m, hx21m⟩, ?_⟩
          refine Entails.trans hPm ?_
          rw [← hScGen, ← hDebGen]
          refine Entails.of_eq ?_
          rw [show (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗
                (roRest ∗ MallocngRuntime maddrs tp ∗ F) =
              ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗
                roRest) ∗ MallocngRuntime maddrs tp ∗ F by ac_rfl,
              ← hRoEq]
        · intro _ _ _ h; exact h
  ·
    rintro s_m P_m hpc_m hrun_m ⟨⟨hsp_m, hbrk_m, hperm_m, hProc_m, hcs_m, hx19_m, hx20_m, hx21_m⟩, hPm⟩
    apply SepWP.weaken_pre hPm
    dsimp only [MallocngRuntime]
    wp_steps
    apply SepWP.done
    · simp
    · simp [hrun_m]
    · refine ⟨⟨by simp [hsp_m], hbrk_m, hperm_m,
        by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc_m,
        untouchedCS_step hcs_m (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
        by simpa using hx19_m, by simpa using hx20_m, by simpa using hx21_m,
        by simp [arm64_norm]⟩, Entails.refl _⟩

/-! ## Coarse Size-Class Bump (`+0x0dc .. +0x150` / `+0x2f4`) -/

abbrev miOff_coarse_ldr1  : BitVec 64 := words_insn_off% mallocImplWords 0xf8607836#32 0
abbrev miOff_coarse_cmp0  : BitVec 64 := words_insn_off% mallocImplWords 0xf10002df#32 0
abbrev miOff_coarse_ldr2  : BitVec 64 := words_insn_off% mallocImplWords 0xf8757820#32 0
abbrev miOff_coarse_cbnz  : BitVec 64 := words_insn_off% mallocImplWords 0xb5000f20#32 0
abbrev miOff_coarse_ldr3  : BitVec 64 := words_insn_off% mallocImplWords 0xf8637836#32 0
abbrev miOff_coarse_ldr4  : BitVec 64 := words_insn_off% mallocImplWords 0xf8607820#32 0
abbrev miOff_coarse_cbz22 : BitVec 64 := words_insn_off% mallocImplWords 0xb40000b6#32 0
abbrev miOff_coarse_cmp12 : BitVec 64 := words_insn_off% mallocImplWords 0xf100301f#32 0

theorem meta_extract {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt} (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hNoRes : st.reservedMetas = []) {g : GroupDesc} (hg : g ∈ st.groups) :
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      ((g.metaPtr ↦ₛ g.metaBytes) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal) := by
  obtain ⟨hMetaOwn, _⟩ := group_meta_and_claimed_ownedRw hwf hNoRes hg
  have hMetaBytes : readBytesFromMap st.byteVal g.metaPtr 40 = g.metaBytes :=
    (hwf.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hExt := ByteMap_extract_slice hwf.masterDom_wf.1 (keep := OwnedRwByte st)
    st.byteVal g.metaPtr (n := 40) (by omega)
    (fun a ha => (hMetaOwn a ha).2)
    (fun a ha => (hMetaOwn a ha).1)
  rwa [hMetaBytes] at hExt

private theorem coarse_sc0_bv {sc0 : Nat} (hsc0 : sc0 < 48) :
    BitVec.ofNat 64 sc0 + 10#64 = BitVec.ofNat 64 (sc0 + 10) ∧
    (BitVec.ofNat 64 (sc0 + 10)) <<< 3 = BitVec.ofNat 64 (80 + 8 * sc0) ∧
    (∀ bEq : Bool,
      ¬ ((if bEq = true then (BitVec.ofNat 32 sc0).sle 3#32 else true) = true) → 4 ≤ sc0) ∧
    (¬ ((if (BitVec.ofNat 32 sc0).sle 31#32 = true then
          (BitVec.ofNat 32 sc0 == 6#32) else true) = true) →
      sc0 ≤ 31 ∧ sc0 ≠ 6) ∧
    (¬ ((BitVec.ofNat 64 sc0).getLsbD 0 = true) → sc0 % 2 = 0) ∧
    (¬ ((BitVec.ofNat 32 sc0).getLsbD 0 = true) → sc0 % 2 = 0) ∧
    (¬ (((BitVec.ofNat 64 sc0 &&& 1#64) != 0#64) = true) → sc0 % 2 = 0) ∧
    BitVec.ofNat 64 sc0 + 58#64 = BitVec.ofNat 64 (sc0 + 58) ∧
    (BitVec.ofNat 64 (sc0 + 58)) <<< 3 = BitVec.ofNat 64 (464 + 8 * sc0) ∧
    (sc0 % 2 = 0 →
      (BitVec.ofNat 32 sc0 ||| 1#32) = BitVec.ofNat 32 (sc0 + 1) ∧
      (BitVec.ofNat 64 sc0 ||| 1#64) = BitVec.ofNat 64 (sc0 + 1) ∧
      BitVec.zeroExtend 64 (BitVec.ofNat 32 (sc0 + 1)) = BitVec.ofNat 64 (sc0 + 1) ∧
      BitVec.ofNat 64 (sc0 + 1) + 10#64 = BitVec.ofNat 64 (sc0 + 1 + 10) ∧
      (BitVec.ofNat 64 (sc0 + 1 + 10)) <<< 3 = BitVec.ofNat 64 (80 + 8 * (sc0 + 1)) ∧
      BitVec.ofNat 64 (sc0 + 1) + 58#64 = BitVec.ofNat 64 (sc0 + 1 + 58) ∧
      (BitVec.ofNat 64 (sc0 + 1 + 58)) <<< 3 = BitVec.ofNat 64 (464 + 8 * (sc0 + 1))) := by
  have hAll : (List.range 48).all (fun k =>
    decide (
      BitVec.ofNat 64 k + 10#64 = BitVec.ofNat 64 (k + 10) ∧
      (BitVec.ofNat 64 (k + 10)) <<< 3 = BitVec.ofNat 64 (80 + 8 * k) ∧
      (¬ ((if true = true then (BitVec.ofNat 32 k).sle 3#32 else true) = true) → 4 ≤ k) ∧
      (¬ ((if false = true then (BitVec.ofNat 32 k).sle 3#32 else true) = true) → 4 ≤ k) ∧
      (¬ ((if (BitVec.ofNat 32 k).sle 31#32 = true then
            (BitVec.ofNat 32 k == 6#32) else true) = true) →
        k ≤ 31 ∧ k ≠ 6) ∧
      (¬ ((BitVec.ofNat 64 k).getLsbD 0 = true) → k % 2 = 0) ∧
      (¬ ((BitVec.ofNat 32 k).getLsbD 0 = true) → k % 2 = 0) ∧
      (¬ (((BitVec.ofNat 64 k &&& 1#64) != 0#64) = true) → k % 2 = 0) ∧
      BitVec.ofNat 64 k + 58#64 = BitVec.ofNat 64 (k + 58) ∧
      (BitVec.ofNat 64 (k + 58)) <<< 3 = BitVec.ofNat 64 (464 + 8 * k) ∧
      (k % 2 = 0 →
        (BitVec.ofNat 32 k ||| 1#32) = BitVec.ofNat 32 (k + 1) ∧
        (BitVec.ofNat 64 k ||| 1#64) = BitVec.ofNat 64 (k + 1) ∧
        BitVec.zeroExtend 64 (BitVec.ofNat 32 (k + 1)) = BitVec.ofNat 64 (k + 1) ∧
        BitVec.ofNat 64 (k + 1) + 10#64 = BitVec.ofNat 64 (k + 1 + 10) ∧
        (BitVec.ofNat 64 (k + 1 + 10)) <<< 3 = BitVec.ofNat 64 (80 + 8 * (k + 1)) ∧
        BitVec.ofNat 64 (k + 1) + 58#64 = BitVec.ofNat 64 (k + 1 + 58) ∧
        (BitVec.ofNat 64 (k + 1 + 58)) <<< 3 = BitVec.ofNat 64 (464 + 8 * (k + 1))))) = true := by
    decide
  have hk := of_decide_eq_true (List.all_eq_true.mp hAll sc0 (List.mem_range.mpr hsc0))
  obtain ⟨h1, h2, h3t, h3f, h4, h5a, h5b, h5c, h6, h7, h8⟩ := hk
  refine ⟨h1, h2, fun bEq => ?_, h4, h5a, h5b, h5c, h6, h7, h8⟩
  cases bEq
  · exact h3f
  · exact h3t

set_option maxHeartbeats 400000 in
theorem mallocImpl_coarse_step [MallocngMultiPlacement]
    {brkStart target_pc : BitVec 64} {liveCost peakCost req sc0 : Nat}
    {st0 : MallocngSt} {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hwf0 : MallocngWF maddrs.base brkStart s.brk liveCost peakCost st0)
    (hsc0_lt : sc0 < 48)
    (hpc : s.pc = mbase 9 + miOff_after_lock) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx19 : s.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc0)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 sc0)
    (hx24 : s.readReg64 (.gpr 24#5) = pageOf maddrs.lock)
    (hTryAvail : ∀ (sc : Nat) (s_t : State) (P_t : SepProp),
      (sc = sc0 ∨ (4 ≤ sc0 ∧ sc0 ≤ 31 ∧ sc0 ≠ 6 ∧ sc0 % 2 = 0 ∧ sc = sc0 + 1)) →
      ∀ (_hScLt : sc < 48) (hAct : sc < st0.ctx.active.length),
      s_t.pc = mbase 9 + miOff_try_avail →
      s_t.status = .Running →
      s_t.sp = s0.sp - 80#64 →
      s_t.brk = s.brk →
      s_t.mem = s.mem →
      MallocngProcPreserved s0 s_t →
      MallocImplUntouchedCS s0 s_t →
      s_t.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc →
      s_t.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req →
      s_t.readReg64 (.gpr 22#5) = st0.ctx.active[sc]'hAct →
      s_t.readReg64 (.gpr 24#5) = pageOf maddrs.lock →
      s_t.readReg64 (.gpr 25#5) = pageOf maddrs.ctx →
      (P_t ⊢ (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
        ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ F) →
      SepWP (mallocngBlockProg mmpl 9 msvc) target_pc s_t P_t post oom)
    (hSlow : ∀ (sc : Nat) (s_p : State) (P_p : SepProp),
      (sc = sc0 ∨ (4 ≤ sc0 ∧ sc0 ≤ 31 ∧ sc0 ≠ 6 ∧ sc0 % 2 = 0 ∧ sc = sc0 + 1)) →
      sc < 48 →
      s_p.pc = mbase 9 + miOff_alloc_prep →
      s_p.status = .Running →
      s_p.sp = s0.sp - 80#64 →
      s_p.brk = s.brk →
      s_p.mem = s.mem →
      MallocngProcPreserved s0 s_p →
      MallocImplUntouchedCS s0 s_p →
      s_p.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc →
      s_p.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req →
      s_p.readReg64 (.gpr 24#5) = pageOf maddrs.lock →
      s_p.readReg64 (.gpr 25#5) = pageOf maddrs.ctx →
      (P_p ⊢ (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
        ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ F) →
      SepWP (mallocngBlockProg mmpl 9 msvc) target_pc s_p P_p post oom) :
    SepWP (mallocngBlockProg mmpl 9 msvc) target_pc s
      ((maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
       ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ F)
      post oom := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b at hpc ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  have _ := hb
  obtain ⟨hActLen, hUseLen, hUnmLen, hBncLen, hPadLen, hActLLen⟩ := hwf0.ctx_lens
  have hNoRes0 : st0.reservedMetas = [] := by
    have hInf := hwf0.inflight_wf
    cases hR : st0.reservedMetas with
    | nil => rfl
    | cons _ _ => rw [hR] at hInf; simp at hInf
  have hPadLen7 : st0.ctx.seqPad.length = 7 := by rw [hPadLen]; rfl
  have hCtxOps := ctxBytes_ops st0.ctx hActLen hUseLen hUnmLen hBncLen hPadLen7
  have hCtxLen : st0.ctx.toBytes.length = 928 := by
    have hFL : ∀ xs : List (BitVec 64), (xs.flatMap unpack64).length = 8 * xs.length := fun xs => by
      induction xs with | nil => rfl | cons _ _ ih => simp [ih]; omega
    simp [CtxFields.toBytes, hFL, hActLen, hUseLen, hUnmLen, hBncLen, hPadLen7]
  have hAct0Lt : sc0 < st0.ctx.active.length := by omega
  have hGetAct0 := hCtxOps.2.2.1 sc0 hsc0_lt
  have hGetUse0 := hCtxOps.2.2.2.1 sc0 hsc0_lt
  obtain ⟨hAdd10, hShl10, hNotLe, hNotEq, hNotOdd64, hNotOdd32, hNotOddAnd,
    hAdd58, hShl58, hEvenOps⟩ := coarse_sc0_bv hsc0_lt
  have hTrSc0 : BitVec.truncate 32 (BitVec.ofNat 64 sc0) = BitVec.ofNat 32 sc0 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  generalize hCtxGen : st0.ctx.toBytes = ctxBs at hCtxLen hGetAct0 hGetUse0 hCtxOps ⊢
  refine SepWP.seq (mid := b + miOff_coarse_ldr1)
    (Mid := fun s1 P1 =>
      (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem = s.mem ∧
       MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
       s1.readReg64 (.gpr 0#5) = BitVec.ofNat 64 (sc0 + 10) ∧
       s1.readReg64 (.gpr 1#5) = maddrs.ctx ∧
       s1.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc0 ∧
       s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
       s1.readReg64 (.gpr 21#5) = BitVec.ofNat 64 sc0 ∧
       s1.readReg64 (.gpr 24#5) = pageOf maddrs.lock ∧
       s1.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) ∧
      (P1 ⊢ (maddrs.ctx ↦ₛ ctxBs) ∗ ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ F)) ?_ ?_
  · dsimp only [miOff_after_lock, miOff_coarse_ldr1] at hpc ⊢
    wp_steps
    apply SepWP.done
    · simp
    · simp [hrun]
    · refine ⟨⟨by simp [hsp], rfl, rfl,
        by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc,
        untouchedCS_step hcsHi (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
        by simp,
        by simp [arm64_norm],
        by simpa using hx19, by simpa using hx20, by simpa using hx21,
        by simpa using hx24, by simp [arm64_norm]⟩, Entails.refl _⟩
  · rintro s1 P1 hpc1 hrun1 ⟨⟨hsp1, hbrk1, hperm1, hProc1, hcs1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx24_1, hx25_1⟩, hP1⟩
    apply SepWP.weaken_pre hP1
    refine SepWP.step_ldr64
      (s' := (s1.writeReg64 (.gpr 22#5) (st0.ctx.active[sc0]'hAct0Lt)).setPC (b + miOff_coarse_cmp0))
      hpc1 hrun1 (by dsimp only [miOff_coarse_ldr1]; simp only [arm64_norm]; rfl) rfl
      (ea := maddrs.ctx + BitVec.ofNat 64 (80 + 8 * sc0)) (wb := none)
      (by simp [evalAddrMode, extendVal, hx1_1, hx0_1, hShl10])
      (SepLoad64.of_pointsToBytes rfl (by omega) rfl)
      (by rw [applyWriteback, hGetAct0, BitVec.add_assoc]; rfl) ?_
    dsimp only [miOff_coarse_cmp0, miOff_coarse_ldr2]
    wp_steps
    wp_if hBrLe
    ·
      rw [← hb_eq, ← mallocngBlockProg_eq_b09]
      exact hTryAvail sc0 _ _ (Or.inl rfl) hsc0_lt hAct0Lt
        (by rw [hb_eq]; rfl) (by simp [hrun1]) (by simp [hsp1]) hbrk1 hperm1
        (by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc1)
        (untouchedCS_step hcs1 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]))
        (by simpa using hx19_1) (by simpa using hx20_1) (by simp)
        (by simpa using hx24_1) (by simpa using hx25_1)
        (by rw [← hCtxGen]; exact Entails.refl _)
    ·
      have hGe4 : 4 ≤ sc0 := by
        dsimp [ConditionHolds] at hBrLe
        split at hBrLe
        · exact hNotLe true (by simp [hBrLe])
        · simp at hBrLe
      wp_steps
      wp_if hBrEq
      ·
        rw [← hb_eq, ← mallocngBlockProg_eq_b09]
        exact hSlow sc0 _ _ (Or.inl rfl) hsc0_lt
          (by rw [hb_eq]; rfl) (by simp [hrun1]) (by simp [hsp1]) hbrk1 hperm1
          (by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc1)
          (untouchedCS_step hcs1 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]))
          (by simpa using hx19_1) (by simpa using hx20_1)
          (by simpa using hx24_1) (by simpa using hx25_1)
          (by rw [← hCtxGen]; exact Entails.refl _)
      ·
        obtain ⟨hLe31, hNe6⟩ := hNotEq (by simpa [hx19_1, hTrSc0] using hBrEq)
        wp_steps
        wp_if hBrOdd
        ·
          rw [← hb_eq, ← mallocngBlockProg_eq_b09]
          exact hSlow sc0 _ _ (Or.inl rfl) hsc0_lt
            (by rw [hb_eq]; rfl) (by simp [hrun1]) (by simp [hsp1]) hbrk1 hperm1
            (by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc1)
            (untouchedCS_step hcs1 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]))
            (by simpa using hx19_1) (by simpa using hx20_1)
            (by simpa using hx24_1) (by simpa using hx25_1)
            (by rw [← hCtxGen]; exact Entails.refl _)
        ·
          have hEven : sc0 % 2 = 0 := by
            first
            | exact hNotOdd64 (by simpa [hx19_1, hTrSc0] using hBrOdd)
            | exact hNotOdd32 (by simpa [hx19_1, hTrSc0] using hBrOdd)
            | exact hNotOddAnd (by simpa [hx19_1, hTrSc0] using hBrOdd)
          obtain ⟨hOrr32, hOrr64, hZSc1, hAdd10_1, hShl10_1, hAdd58_1, hShl58_1⟩ := hEvenOps hEven
          have hSc1Lt : sc0 + 1 < 48 := by omega
          have hAct1Lt : sc0 + 1 < st0.ctx.active.length := by omega
          have hActL1Lt : sc0 + 1 < st0.activeLists.length := by omega
          have hGetAct1 := hCtxOps.2.2.1 (sc0 + 1) hSc1Lt
          have hGetUse1 := hCtxOps.2.2.2.1 (sc0 + 1) hSc1Lt
          have hSxMSc1 := sxtw_sbfm_ofNat hSc1Lt
          obtain ⟨hSxSc1, _, _, _⟩ := sc_sxtw_bv (sc0 + 1) hSc1Lt
          refine SepWP.seq (mid := b + miOff_coarse_ldr2)
            (Mid := fun s2 P2 =>
              (s2.sp = s0.sp - 80#64 ∧ s2.brk = s.brk ∧ s2.mem = s.mem ∧
               MallocngProcPreserved s0 s2 ∧ MallocImplUntouchedCS s0 s2 ∧
               s2.readReg64 (.gpr 1#5) = maddrs.ctx ∧
               s2.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc0 ∧
               s2.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
               s2.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (sc0 + 58) ∧
               s2.readReg64 (.gpr 24#5) = pageOf maddrs.lock ∧
               s2.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) ∧
              (P2 ⊢ (maddrs.ctx ↦ₛ ctxBs) ∗ ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ F)) ?_ ?_
          · wp_steps
            apply SepWP.done
            · simp
            · simp [hrun1]
            · refine ⟨⟨by simp [hsp1], hbrk1, hperm1,
                by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc1,
                untouchedCS_step hcs1 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
                by simpa using hx1_1, by simpa using hx19_1, by simpa using hx20_1,
                by simp,
                by simpa using hx24_1, by simpa using hx25_1⟩, Entails.refl _⟩
          · rintro s2 P2 hpc2 hrun2 ⟨⟨hsp2, hbrk2, hperm2, hProc2, hcs2, hx1_2, hx19_2, hx20_2, hx21_2, hx24_2, hx25_2⟩, hP2⟩
            apply SepWP.weaken_pre hP2
            refine SepWP.step_ldr64
              (s' := (s2.writeReg64 (.gpr 0#5) (st0.ctx.usageByClass[sc0]'(by omega))).setPC (b + miOff_coarse_cbnz))
              hpc2 hrun2 (by dsimp only [miOff_coarse_ldr2]; simp only [arm64_norm]; rfl) rfl
              (ea := maddrs.ctx + BitVec.ofNat 64 (464 + 8 * sc0)) (wb := none)
              (by simp [evalAddrMode, extendVal, hx1_2, hx21_2, hShl58])
              (SepLoad64.of_pointsToBytes rfl (by omega) rfl)
              (by rw [applyWriteback, hGetUse0, BitVec.add_assoc]; rfl) ?_
            dsimp only [miOff_coarse_cbnz, miOff_coarse_ldr3]
            wp_steps
            wp_if hBrUse0
            ·
              rw [← hb_eq, ← mallocngBlockProg_eq_b09]
              exact hSlow sc0 _ _ (Or.inl rfl) hsc0_lt
                (by rw [hb_eq]; rfl) (by simp [hrun2]) (by simp [hsp2]) hbrk2 hperm2
                (by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc2)
                (untouchedCS_step hcs2 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]))
                (by simpa using hx19_2) (by simpa using hx20_2)
                (by simpa using hx24_2) (by simpa using hx25_2)
                (by rw [← hCtxGen]; exact Entails.refl _)
            ·
              refine SepWP.seq (mid := b + miOff_coarse_ldr3)
                (Mid := fun s3 P3 =>
                  (s3.sp = s0.sp - 80#64 ∧ s3.brk = s.brk ∧ s3.mem = s.mem ∧
                   MallocngProcPreserved s0 s3 ∧ MallocImplUntouchedCS s0 s3 ∧
                   s3.readReg64 (.gpr 0#5) = BitVec.ofNat 64 (sc0 + 1 + 58) ∧
                   s3.readReg64 (.gpr 1#5) = maddrs.ctx ∧
                   s3.readReg64 (.gpr 2#5) = BitVec.ofNat 64 (sc0 + 1) ∧
                   s3.readReg64 (.gpr 3#5) = BitVec.ofNat 64 (sc0 + 1 + 10) ∧
                   s3.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc0 ∧
                   s3.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
                   s3.readReg64 (.gpr 24#5) = pageOf maddrs.lock ∧
                   s3.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) ∧
                  (P3 ⊢ (maddrs.ctx ↦ₛ ctxBs) ∗ ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ F)) ?_ ?_
              · wp_steps
                apply SepWP.done
                · simp
                · simp [hrun2]
                · refine ⟨⟨by simp [hsp2], hbrk2, hperm2,
                    by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc2,
                    untouchedCS_step hcs2 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
                    by simpa [hx19_2, hTrSc0, hOrr32, hOrr64, hZSc1, hSxSc1, hSxMSc1] using hAdd58_1,
                    by simpa using hx1_2,
                    by simpa [hx19_2, hTrSc0, hOrr32, hOrr64] using hZSc1,
                    by simpa [hx19_2, hTrSc0, hOrr32, hOrr64, hZSc1, hSxSc1, hSxMSc1] using hAdd10_1,
                    by simpa using hx19_2, by simpa using hx20_2,
                    by simpa using hx24_2, by simpa using hx25_2⟩, Entails.refl _⟩
              · rintro s3 P3 hpc3 hrun3 ⟨⟨hsp3, hbrk3, hperm3, hProc3, hcs3, hx0_3, hx1_3, hx2_3, hx3_3, hx19_3, hx20_3, hx24_3, hx25_3⟩, hP3⟩
                apply SepWP.weaken_pre hP3
                refine SepWP.step_ldr64
                  (s' := (s3.writeReg64 (.gpr 22#5) (st0.ctx.active[sc0 + 1]'hAct1Lt)).setPC (b + miOff_coarse_ldr4))
                  hpc3 hrun3 (by dsimp only [miOff_coarse_ldr3]; simp only [arm64_norm]; rfl) rfl
                  (ea := maddrs.ctx + BitVec.ofNat 64 (80 + 8 * (sc0 + 1))) (wb := none)
                  (by simp [evalAddrMode, extendVal, hx1_3, hx3_3, hShl10_1])
                  (SepLoad64.of_pointsToBytes rfl (by omega) rfl)
                  (by rw [applyWriteback, hGetAct1, BitVec.add_assoc]; rfl) ?_
                refine SepWP.step_ldr64 (pc := b + miOff_coarse_ldr4)
                  (s' := ((s3.writeReg64 (.gpr 22#5) (st0.ctx.active[sc0 + 1]'hAct1Lt)).writeReg64
                    (.gpr 0#5) (st0.ctx.usageByClass[sc0 + 1]'(by omega))).setPC (b + miOff_coarse_cbz22))
                  rfl (by simp [hrun3]) (by dsimp only [miOff_coarse_ldr4]; simp only [arm64_norm]; rfl) rfl
                  (ea := maddrs.ctx + BitVec.ofNat 64 (464 + 8 * (sc0 + 1))) (wb := none)
                  (by simp [evalAddrMode, extendVal, hx1_3, hx0_3, hShl58_1])
                  (SepLoad64.of_pointsToBytes rfl (by omega) rfl)
                  (by cases s3; rw [applyWriteback, hGetUse1, BitVec.add_assoc]; rfl) ?_
                refine SepWP.seq (mid := b + miOff_coarse_cmp12)
                  (Mid := fun s4 P4 =>
                    (s4.sp = s0.sp - 80#64 ∧ s4.brk = s.brk ∧ s4.mem = s.mem ∧
                     MallocngProcPreserved s0 s4 ∧ MallocImplUntouchedCS s0 s4 ∧
                     s4.readReg64 (.gpr 2#5) = BitVec.ofNat 64 (sc0 + 1) ∧
                     s4.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc0 ∧
                     s4.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
                     s4.readReg64 (.gpr 22#5) = st0.ctx.active[sc0 + 1]'hAct1Lt ∧
                     s4.readReg64 (.gpr 24#5) = pageOf maddrs.lock ∧
                     s4.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) ∧
                    (P4 ⊢ (maddrs.ctx ↦ₛ ctxBs) ∗ ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ F)) ?_ ?_
                · dsimp only [miOff_coarse_cbz22, miOff_coarse_cmp12]
                  wp_steps
                  wp_if hCbzAct1
                  · wp_steps
                    apply SepWP.done
                    · simp
                    · simp [hrun3]
                    · refine ⟨⟨by simp [hsp3], hbrk3, hperm3,
                        by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc3,
                        untouchedCS_step hcs3 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
                        by simpa using hx2_3, by simpa using hx19_3, by simpa using hx20_3,
                        by simp [hCbzAct1],
                        by simpa using hx24_3, by simpa using hx25_3⟩, Entails.refl _⟩
                  · have hAct1Ne : st0.ctx.active[sc0 + 1]'hAct1Lt ≠ 0#64 := by
                      intro hEq0; simp [hEq0] at hCbzAct1
                    have hwf_s : MallocngWF maddrs.base brkStart s.brk liveCost peakCost st0 := hwf0
                    obtain ⟨g1, hg1, hMetaEq1, _, _⟩ :=
                      active_head_group_of_nonzero hwf_s hAct1Lt hActL1Lt hAct1Ne
                    have hExt1 := meta_extract hwf_s hNoRes0 hg1
                    have hm1Len : g1.metaBytes.length = 40 := by simp [GroupDesc.metaBytes]
                    generalize hm1Gen : g1.metaBytes = m1Bs at hExt1 hm1Len
                    have hRearr1 : ((maddrs.ctx ↦ₛ ctxBs) ∗ ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ F) =
                        ((st0.ctx.active[sc0 + 1]'hAct1Lt ↦ₛ m1Bs) ∗
                         ((maddrs.ctx ↦ₛ ctxBs) ∗
                          ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g1.metaPtr 40 a) st0.byteVal ∗ F)) := by
                      rw [hExt1, hMetaEq1]; ac_rfl
                    rw [hRearr1]
                    wp_steps
                    wp_if hAv1
                    · apply SepWP.done
                      · simp
                      · simp [hrun3]
                      · refine ⟨⟨by simp [hsp3], hbrk3, hperm3,
                          by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc3,
                          untouchedCS_step hcs3 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
                          by simpa using hx2_3, by simpa using hx19_3, by simpa using hx20_3,
                          by simp, by simpa using hx24_3, by simpa using hx25_3⟩, ?_⟩
                        rw [← hRearr1]; exact Entails.refl _
                    · wp_steps
                      wp_if hFr1
                      · apply SepWP.done
                        · simp
                        · simp [hrun3]
                        · refine ⟨⟨by simp [hsp3], hbrk3, hperm3,
                            by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc3,
                            untouchedCS_step hcs3 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
                            by simpa using hx2_3, by simpa using hx19_3, by simpa using hx20_3,
                            by simp, by simpa using hx24_3, by simpa using hx25_3⟩, ?_⟩
                          rw [← hRearr1]; exact Entails.refl _
                      · wp_steps
                        apply SepWP.done
                        · simp
                        · simp [hrun3]
                        · refine ⟨⟨by simp [hsp3], hbrk3, hperm3,
                            by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc3,
                            untouchedCS_step hcs3 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
                            by simpa using hx2_3, by simpa using hx19_3, by simpa using hx20_3,
                            by simp, by simpa using hx24_3, by simpa using hx25_3⟩, ?_⟩
                          rw [← hRearr1]; exact Entails.refl _
                · rintro s4 P4 hpc4 hrun4 ⟨⟨hsp4, hbrk4, hperm4, hProc4, hcs4, hx2_4, hx19_4, hx20_4, hx22_4, hx24_4, hx25_4⟩, hP4⟩
                  apply SepWP.weaken_pre hP4
                  dsimp only [miOff_coarse_cmp12] at hpc4
                  wp_steps
                  wp_if hBrHi
                  ·
                    rw [← hb_eq, ← mallocngBlockProg_eq_b09]
                    exact hSlow sc0 _ _ (Or.inl rfl) hsc0_lt
                      (by rw [hb_eq]; rfl) (by simp [hrun4]) (by simp [hsp4]) hbrk4 hperm4
                      (by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc4)
                      (untouchedCS_step hcs4 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]))
                      (by simpa using hx19_4) (by simpa using hx20_4)
                      (by simpa using hx24_4) (by simpa using hx25_4)
                      (by rw [← hCtxGen]; exact Entails.refl _)
                  ·
                    refine SepWP.seq (mid := b + miOff_try_avail)
                      (Mid := fun s5 P5 =>
                        (s5.sp = s0.sp - 80#64 ∧ s5.brk = s.brk ∧ s5.mem = s.mem ∧
                         MallocngProcPreserved s0 s5 ∧ MallocImplUntouchedCS s0 s5 ∧
                         s5.readReg64 (.gpr 19#5) = BitVec.ofNat 64 (sc0 + 1) ∧
                         s5.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
                         s5.readReg64 (.gpr 22#5) = st0.ctx.active[sc0 + 1]'hAct1Lt ∧
                         s5.readReg64 (.gpr 24#5) = pageOf maddrs.lock ∧
                         s5.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) ∧
                        (P5 ⊢ (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
                          ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ F)) ?_ ?_
                    · dsimp only [miOff_try_avail]
                      wp_steps
                      apply SepWP.done
                      · simp
                      · simp [hrun4]
                      · refine ⟨⟨by simp [hsp4], hbrk4, hperm4,
                          by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc4,
                          untouchedCS_step hcs4 (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
                          by apply BitVec.eq_of_toNat_eq; simp; omega,
                          by simpa using hx20_4, by simpa using hx22_4,
                          by simpa using hx24_4, by simpa using hx25_4⟩, ?_⟩
                        rw [← hCtxGen]; exact Entails.refl _
                    · rintro s5 P5 hpc5 hrun5 ⟨⟨hsp5, hbrk5, hperm5, hProc5, hcs5, hx19_5, hx20_5, hx22_5, hx24_5, hx25_5⟩, hP5⟩
                      rw [← hb_eq, ← mallocngBlockProg_eq_b09]
                      exact hTryAvail (sc0 + 1) s5 P5 (Or.inr ⟨hGe4, hLe31, hNe6, hEven, rfl⟩) hSc1Lt hAct1Lt
                        (by rwa [hb_eq]) hrun5 hsp5 hbrk5 hperm5 hProc5 hcs5
                        hx19_5 hx20_5 hx22_5 hx24_5 hx25_5 hP5

end VerifiedLibraries.Mallocng.Proofs
