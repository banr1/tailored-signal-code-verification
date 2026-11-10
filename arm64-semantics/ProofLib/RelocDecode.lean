/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.CoreLemmas
public import ProofLib.ObjectLoad
public import ProofLib.Library
public import ProofLib.Library.Calls
public import ProofLib.BV.ReflectROBDD
public import ProofLib.SepLogic.CodeLookup
public import ProofLib.ProgramReflection.IdxTree
import ProofLib.Hoare.Model

/-!
# Layout-Generic Relocation Decoding and Linking

Proves page and low-12-bit cancellation identities, symbolic instruction decoders for AArch64
relocation word patchers against `Arm64.decode`, fetch rules for `Program.hasWords`, linker
range-extension veneers, and layout-generic code and data relocation linking over `Obj.LinkedImage`.
-/

@[expose] public section

namespace Arm64
namespace Obj

set_option linter.literalFetch false

/-! ## Page and Low-12-Bit Cancellation Identities -/

/-- `ADRP` page-cancellation identity:
    `(place &&& ~0xfff) + (pageOf target - pageOf place) = pageOf target`. -/
@[simp, arm64_norm, wp_norm]
theorem adrp_pageOf_cancel (place target : BitVec 64) :
    (place &&& 0xfffffffffffff000#64) + (pageOf target - pageOf place) = pageOf target := by
  change pageOf place + (pageOf target - pageOf place) = pageOf target
  bv_lin

/-- Variant of `adrp_pageOf_cancel` with `pageOf place` on the left. -/
@[simp, arm64_norm, wp_norm]
theorem pageOf_add_sub_cancel (place target : BitVec 64) :
    pageOf place + (pageOf target - pageOf place) = pageOf target := by
  bv_lin

/-- Page and `:lo12:` reconstruction identity: `pageOf target + lo12Of target = target`. -/
@[simp, arm64_norm, wp_norm]
theorem pageOf_add_lo12Of (target : BitVec 64) :
    pageOf target + lo12Of target = target := by
  unfold pageOf lo12Of
  bv_bits

/-- Reassociated page + index + `:lo12:` reconstruction identity:
    `(pageOf target + idx) + lo12Of target = target + idx`. -/
@[simp, arm64_norm, wp_norm]
theorem pageOf_add_idx_add_lo12Of (target idx : BitVec 64) :
    (pageOf target + idx) + lo12Of target = target + idx := by
  rw [show (pageOf target + idx) + lo12Of target = (pageOf target + lo12Of target) + idx by bv_lin]
  rw [pageOf_add_lo12Of]

/-- Reassociated page + `:lo12:` + index identity:
    `pageOf target + (lo12Of target + idx) = target + idx`. -/
@[simp, arm64_norm, wp_norm]
theorem pageOf_add_lo12Of_add_idx (target idx : BitVec 64) :
    pageOf target + (lo12Of target + idx) = target + idx := by
  rw [← BitVec.add_assoc, pageOf_add_lo12Of]

@[simp]
theorem lo12Of_zero : lo12Of 0#64 = 0#64 := rfl

@[simp]
theorem pageOf_zero : pageOf 0#64 = 0#64 := rfl

theorem pageOf_and_fff (x : BitVec 64) : pageOf x &&& 0xfff#64 = 0#64 := by
  unfold pageOf
  bv_slice

theorem pageOf_base_add {base off : BitVec 64} (hb : base &&& 0xfff#64 = 0#64) :
    pageOf (base + off) = base + pageOf off := by
  unfold pageOf
  bv_bits

theorem lo12Of_base_add {base off : BitVec 64} (hb : base &&& 0xfff#64 = 0#64) :
    lo12Of (base + off) = lo12Of off := by
  unfold lo12Of
  bv_bits

theorem pageOf_diff_base_add {base place target : BitVec 64} (hb : base &&& 0xfff#64 = 0#64) :
    pageOf (base + target) - pageOf (base + place) = pageOf target - pageOf place := by
  rw [pageOf_base_add hb, pageOf_base_add hb]
  bv_lin

theorem pageOf_diff_base_add3 {base : BitVec 64} {off roff t : Nat}
    (hb : base &&& 0xfff#64 = 0#64) :
    pageOf (base + BitVec.ofNat 64 t) -
      pageOf (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff) =
    pageOf (BitVec.ofNat 64 t) - pageOf (BitVec.ofNat 64 (off + roff)) := by
  have h1 : base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff =
      base + BitVec.ofNat 64 (off + roff) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [h1, pageOf_diff_base_add hb]

/-! ## Symbolic Decoders for Relocation Word Patchers -/

theorem adrpWordOff_extract (w : BitVec 32) (d : BitVec 64) :
    ((adrpWordOff w d).extractLsb' 5 19) ++ ((adrpWordOff w d).extractLsb' 29 2) =
      d.extractLsb' 12 21 := by
  unfold adrpWordOff
  bv_slice

theorem adrpWordOff_mask (w : BitVec 32) (d : BitVec 64) :
    adrpWordOff w d &&& 0x9f00001f#32 = w &&& 0x9f00001f#32 := by
  unfold adrpWordOff
  bv_slice

theorem adrp_mask_preserve {v w : BitVec 32} (hmask : v &&& 0x9f00001f#32 = w &&& 0x9f00001f#32) :
    v &&& 0x9f000000#32 = w &&& 0x9f000000#32 ∧ v.extractLsb' 0 5 = w.extractLsb' 0 5 := by
  bv_slice

theorem pageOf_sub_and_fff (place target : BitVec 64) :
    (pageOf target - pageOf place) &&& 0xfff#64 = 0#64 := by
  have ht : (pageOf target).toNat % 4096 = 0 := by
    have h := congrArg BitVec.toNat (pageOf_and_fff target)
    rwa [BitVec.toNat_and, show (0xfff#64).toNat = 2 ^ 12 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] at h
  have hp : (pageOf place).toNat % 4096 = 0 := by
    have h := congrArg BitVec.toNat (pageOf_and_fff place)
    rwa [BitVec.toNat_and, show (0xfff#64).toNat = 2 ^ 12 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] at h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xfff#64).toNat = 2 ^ 12 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

theorem signExtend_extractLsb_12_21 {d : BitVec 64}
    (hal : d &&& 0xfff#64 = 0#64)
    (hlt : d + 0x100000000#64 < 0x200000000#64) :
    ((d.extractLsb' 12 21).signExtend 64) <<< 12 = d := by
  bv_bits

theorem adrpWord_imm {w : BitVec 32} {place target : BitVec 64}
    (hr : AdrpInRange place target) :
    ((((adrpWord w place target).extractLsb' 5 19) ++
      ((adrpWord w place target).extractLsb' 29 2)).signExtend 64) <<< 12 =
      pageOf target - pageOf place := by
  obtain ⟨hfit1, hfit2⟩ := hr
  have hal := pageOf_sub_and_fff place target
  unfold adrpWord
  rw [adrpWordOff_extract]
  apply signExtend_extractLsb_12_21 hal
  generalize pageOf target - pageOf place = d at hfit1 hfit2 ⊢
  rw [BitVec.toInt_eq_toNat_cond] at hfit1 hfit2
  rw [BitVec.lt_def, BitVec.toNat_add]
  have := d.isLt
  simp only [BitVec.toNat_ofNat]
  split at hfit1 <;> omega

set_option linter.deprecated false in
theorem decode_adr_or_adrp {v : BitVec 32}
    (hv : v &&& 0x1f000000#32 = 0x10000000#32) :
    decode v =
      let page := v.getLsbD 31
      let imm21 := (v.extractLsb' 5 19) ++ (v.extractLsb' 29 2)
      let offset := if page then (imm21.signExtend 64) <<< 12 else imm21.signExtend 64
      let rd := Reg.fromZRBits (v.extractLsb' 0 5)
      some (.adr page rd offset) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_pos (by simp [h4])]

set_option linter.deprecated false in
/-- Symbolic decoder for `R_AARCH64_ADR_PREL_PG_HI21`. -/
theorem decode_adrpWord {w : BitVec 32} (hw : w &&& 0x9f000000#32 = 0x90000000#32)
    {place target : BitVec 64} (hr : AdrpInRange place target) :
    decode (adrpWord w place target) =
      some (.adr true (Reg.fromZRBits (w.extractLsb' 0 5)) (pageOf target - pageOf place)) := by
  have himm := adrpWord_imm (w := w) hr
  have ⟨hm, hrd⟩ := adrp_mask_preserve (adrpWordOff_mask w (pageOf target - pageOf place))
  have hv9 : adrpWord w place target &&& 0x9f000000#32 = 0x90000000#32 := hm.trans hw
  have hv1 : adrpWord w place target &&& 0x1f000000#32 = 0x10000000#32 := by bv_bits
  have hp : (adrpWord w place target).getLsbD 31 = true := by bv_bits
  change (adrpWord w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrd
  rw [decode_adr_or_adrp hv1]
  dsimp only
  rw [hp, if_pos rfl, himm, hrd]

set_option linter.deprecated false in
/-- Symbolic decoder for `R_AARCH64_ADR_PREL_PG_HI21_NC` (unchecked range variant). -/
theorem decode_adrpWord_nc {w : BitVec 32} (hw : w &&& 0x9f000000#32 = 0x90000000#32)
    (place target : BitVec 64) :
    decode (adrpWord w place target) =
      some (.adr true (Reg.fromZRBits (w.extractLsb' 0 5))
        ((((pageOf target - pageOf place).extractLsb' 12 21).signExtend 64) <<< 12)) := by
  have ⟨hm, hrd⟩ := adrp_mask_preserve (adrpWordOff_mask w (pageOf target - pageOf place))
  have hv9 : adrpWord w place target &&& 0x9f000000#32 = 0x90000000#32 := hm.trans hw
  have hv1 : adrpWord w place target &&& 0x1f000000#32 = 0x10000000#32 := by bv_bits
  have hp : (adrpWord w place target).getLsbD 31 = true := by bv_bits
  change (adrpWord w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrd
  rw [decode_adr_or_adrp hv1]
  dsimp only
  rw [hp, if_pos rfl, hrd]
  unfold adrpWord
  rw [adrpWordOff_extract]

theorem adrWordOff_extract (w : BitVec 32) (d : BitVec 64) :
    ((adrWordOff w d).extractLsb' 5 19) ++ ((adrWordOff w d).extractLsb' 29 2) =
      d.extractLsb' 0 21 := by
  unfold adrWordOff
  bv_slice

theorem adrWordOff_mask (w : BitVec 32) (d : BitVec 64) :
    adrWordOff w d &&& 0x9f00001f#32 = w &&& 0x9f00001f#32 := by
  unfold adrWordOff
  bv_slice

theorem signExtend_extractLsb_0_21 {d : BitVec 64}
    (hlt : d + 0x100000#64 < 0x200000#64) :
    (d.extractLsb' 0 21).signExtend 64 = d := by
  bv_bits

theorem adrWord_imm {w : BitVec 32} {place target : BitVec 64}
    (hr : AdrInRange place target) :
    (((adrWord w place target).extractLsb' 5 19) ++
      ((adrWord w place target).extractLsb' 29 2)).signExtend 64 =
      target - place := by
  obtain ⟨hfit1, hfit2⟩ := hr
  unfold adrWord
  rw [adrWordOff_extract]
  apply signExtend_extractLsb_0_21
  generalize target - place = d at hfit1 hfit2 ⊢
  rw [BitVec.toInt_eq_toNat_cond] at hfit1 hfit2
  rw [BitVec.lt_def, BitVec.toNat_add]
  have := d.isLt
  simp only [BitVec.toNat_ofNat]
  split at hfit1 <;> omega

set_option linter.deprecated false in
/-- Symbolic decoder for `R_AARCH64_ADR_PREL_LO21`. -/
theorem decode_adrWord {w : BitVec 32} (hw : w &&& 0x9f000000#32 = 0x10000000#32)
    {place target : BitVec 64} (hr : AdrInRange place target) :
    decode (adrWord w place target) =
      some (.adr false (Reg.fromZRBits (w.extractLsb' 0 5)) (target - place)) := by
  have himm := adrWord_imm (w := w) hr
  have ⟨hm, hrd⟩ := adrp_mask_preserve (adrWordOff_mask w (target - place))
  have hv9 : adrWord w place target &&& 0x9f000000#32 = 0x10000000#32 := hm.trans hw
  have hv1 : adrWord w place target &&& 0x1f000000#32 = 0x10000000#32 := by bv_bits
  have hp : (adrWord w place target).getLsbD 31 = false := by bv_bits
  change (adrWord w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrd
  rw [decode_adr_or_adrp hv1]
  dsimp only
  rw [hp, if_neg Bool.false_ne_true, himm, hrd]

/-! ### `:lo12:` Immediate Relocations -/

theorem lo12Word_mask {scale : Nat} (w : BitVec 32) (target : BitVec 64) :
    lo12Word scale w target &&& 0xffc003ff#32 = w &&& 0xffc003ff#32 := by
  unfold lo12Word
  generalize (target &&& 0xfff#64) >>> scale = d
  bv_slice

theorem lo12_mask_preserve {v w : BitVec 32} (hmask : v &&& 0xffc003ff#32 = w &&& 0xffc003ff#32) :
    v &&& 0xffc00000#32 = w &&& 0xffc00000#32 ∧
    v &&& 0x3f000000#32 = w &&& 0x3f000000#32 ∧
    v.extractLsb' 30 2 = w.extractLsb' 30 2 ∧
    v.extractLsb' 22 2 = w.extractLsb' 22 2 ∧
    v.extractLsb' 5 5 = w.extractLsb' 5 5 ∧
    v.extractLsb' 0 5 = w.extractLsb' 0 5 := by
  bv_slice

theorem lo12Word_extract {scale : Nat} (w : BitVec 32) (target : BitVec 64) :
    (lo12Word scale w target).extractLsb' 10 12 =
      ((target &&& 0xfff#64) >>> scale).extractLsb' 0 12 := by
  unfold lo12Word
  generalize (target &&& 0xfff#64) >>> scale = d
  bv_slice

theorem lo12Word0_imm (w : BitVec 32) (target : BitVec 64) :
    ((lo12Word 0 w target).extractLsb' 10 12).zeroExtend 64 = lo12Of target := by
  rw [lo12Word_extract]
  unfold lo12Of
  bv_slice

theorem lo12Word0_imm12 (w : BitVec 32) (target : BitVec 64) :
    (lo12Word 0 w target).extractLsb' 10 12 = (lo12Of target).truncate 12 := by
  rw [lo12Word_extract]
  unfold lo12Of
  bv_slice

@[simp, arm64_norm, wp_norm]
theorem zeroExtend_truncate_lo12Of (target : BitVec 64) :
    ((lo12Of target).truncate 12).zeroExtend 64 = lo12Of target := by
  unfold lo12Of
  bv_bits

@[simp, arm64_norm, wp_norm]
theorem setWidth_truncate_lo12Of (target : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 12 (lo12Of target)) = lo12Of target := by
  unfold lo12Of
  bv_bits

theorem lo12Word1_imm (w : BitVec 32) (target : BitVec 64) (hal : Lo12Aligned 1 target) :
    (((lo12Word 1 w target).extractLsb' 10 12).zeroExtend 64) <<< 1 = lo12Of target := by
  rw [lo12Word_extract]
  change ((((target &&& 0xfff#64) >>> 1).extractLsb' 0 12).zeroExtend 64) <<< 1 = target &&& 0xfff#64
  have h0 : target &&& 1#64 = 0#64 := hal
  bv_bits

theorem lo12Word2_imm (w : BitVec 32) (target : BitVec 64) (hal : Lo12Aligned 2 target) :
    (((lo12Word 2 w target).extractLsb' 10 12).zeroExtend 64) <<< 2 = lo12Of target := by
  rw [lo12Word_extract]
  change ((((target &&& 0xfff#64) >>> 2).extractLsb' 0 12).zeroExtend 64) <<< 2 = target &&& 0xfff#64
  have h0 : target &&& 3#64 = 0#64 := hal
  bv_bits

theorem lo12Word3_imm (w : BitVec 32) (target : BitVec 64) (hal : Lo12Aligned 3 target) :
    (((lo12Word 3 w target).extractLsb' 10 12).zeroExtend 64) <<< 3 = lo12Of target := by
  rw [lo12Word_extract]
  change ((((target &&& 0xfff#64) >>> 3).extractLsb' 0 12).zeroExtend 64) <<< 3 = target &&& 0xfff#64
  have h0 : target &&& 7#64 = 0#64 := hal
  bv_bits

theorem lo12Word4_imm (w : BitVec 32) (target : BitVec 64) (hal : Lo12Aligned 4 target) :
    (((lo12Word 4 w target).extractLsb' 10 12).zeroExtend 64) <<< 4 = lo12Of target := by
  rw [lo12Word_extract]
  change ((((target &&& 0xfff#64) >>> 4).extractLsb' 0 12).zeroExtend 64) <<< 4 = target &&& 0xfff#64
  have h0 : target &&& 15#64 = 0#64 := hal
  bv_bits

theorem lo12Word_imm {scale : Nat} (hscale : scale ≤ 4) (w : BitVec 32) (target : BitVec 64)
    (hal : Lo12Aligned scale target) :
    (((lo12Word scale w target).extractLsb' 10 12).zeroExtend 64) <<< scale = lo12Of target := by
  match scale with
  | 0 => simpa using lo12Word0_imm w target
  | 1 => exact lo12Word1_imm w target hal
  | 2 => exact lo12Word2_imm w target hal
  | 3 => exact lo12Word3_imm w target hal
  | 4 => exact lo12Word4_imm w target hal
  | n + 5 => omega

set_option linter.deprecated false in
theorem decode_addLo12 {v : BitVec 32}
    (hv : v &&& 0xffc00000#32 = 0x91000000#32) :
    decode v = some (.addSubImm .W64 .ADD
      (Reg.fromSPBits (v.extractLsb' 0 5))
      (Reg.fromSPBits (v.extractLsb' 5 5))
      (v.extractLsb' 10 12) false) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = true := by bv_bits
  have hsf : v.getLsbD 31 = true := by bv_bits
  have h30 : v.getLsbD 30 = false := by bv_bits
  have h29 : v.getLsbD 29 = false := by bv_bits
  have h22 : v.getLsbD 22 = false := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_pos (by simp [h5])]
  dsimp only
  rw [hsf, h30, h29, h22]
  rfl

/-- Symbolic decoder for `R_AARCH64_ADD_ABS_LO12_NC`. -/
theorem decode_addLo12Word {w : BitVec 32} (hw : w &&& 0xffc00000#32 = 0x91000000#32)
    (target : BitVec 64) :
    decode (lo12Word 0 w target) =
      some (.addSubImm .W64 .ADD
        (Reg.fromSPBits (w.extractLsb' 0 5))
        (Reg.fromSPBits (w.extractLsb' 5 5))
        ((lo12Of target).truncate 12) false) := by
  have himm := lo12Word0_imm12 w target
  have ⟨hm1, _, _, _, hrn, hrd⟩ := lo12_mask_preserve (lo12Word_mask (scale := 0) w target)
  have hv : lo12Word 0 w target &&& 0xffc00000#32 = 0x91000000#32 := hm1.trans hw
  rw [decode_addLo12 hv, himm, hrd, hrn]

set_option linter.deprecated false in
theorem decode_ldstGprUnsigned {v : BitVec 32}
    (hv1 : v &&& 0x3f000000#32 = 0x39000000#32)
    (hv2 : (v &&& 0xffc00000#32 == 0xf9800000#32) = false) :
    decode v =
      let sizeBits := (v.extractLsb' 30 2).toNat
      let opc := (v.extractLsb' 22 2).toNat
      let imm12 : BitVec 12 := v.extractLsb' 10 12
      let offset : BitVec 64 := (imm12.zeroExtend 64) <<< sizeBits
      let rn := Reg.fromSPBits (v.extractLsb' 5 5)
      let rt := Reg.fromZRBits (v.extractLsb' 0 5)
      mkLoadStoreInst sizeBits opc rt (.Offset rn offset) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = false := by bv_bits
  have h11 : (v &&& 0x7e000000#32 == 0x34000000#32) = false := by bv_bits
  have h12 : (v &&& 0x7e000000#32 == 0x36000000#32) = false := by bv_bits
  have h13 : (v &&& 0xff000010#32 == 0x54000000#32) = false := by bv_bits
  have h14 : (v &&& 0xff9ffc1f#32 == 0xd61f0000#32) = false := by bv_bits
  have h15 : (v &&& 0x1f000000#32 == 0x0a000000#32) = false := by bv_bits
  have h16 : (v &&& 0x1f200000#32 == 0x0b000000#32) = false := by bv_bits
  have h17 : (v &&& 0x1fe00000#32 == 0x0b200000#32) = false := by bv_bits
  have h18 : (v &&& 0x1fe0fc00#32 == 0x1a000000#32) = false := by bv_bits
  have h19 : (v &&& 0x3fe00410#32 == 0x3a400000#32) = false := by bv_bits
  have h20 : (v &&& 0x3fe00800#32 == 0x1a800000#32) = false := by bv_bits
  have h21 : (v &&& 0x7fff0000#32 == 0x5ac00000#32) = false := by bv_bits
  have h21b : (v &&& 0x7fe0e000#32 == 0x1ac04000#32) = false := by bv_bits
  have h22 : (v &&& 0x7fe00000#32 == 0x1ac00000#32) = false := by bv_bits
  have h23 : (v &&& 0x7f000000#32 == 0x1b000000#32) = false := by bv_bits
  have h24 : (v &&& 0x7f800000#32 == 0x28000000#32) = false := by bv_bits
  have h25 : (v &&& 0x3e000000#32 == 0x28000000#32) = false := by bv_bits
  have h26 : (v &&& 0xffe00c00#32 == 0xf8800000#32) = false := by bv_bits
  have h27 : (v &&& 0xffe00c00#32 == 0xf8a00800#32) = false := by bv_bits
  have h28 : (v &&& 0x3f200c00#32 == 0x38200000#32) = false := by bv_bits
  have h29 : (v &&& 0x3f200c00#32 == 0x19000000#32) = false := by bv_bits
  have h30 : (v &&& 0x3f000000#32 == 0x39000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]),
    if_neg (by simp [h7]), if_neg (by simp [h8]), if_neg (by simp [h9]),
    if_neg (by simp [h10]), if_neg (by simp [h11]), if_neg (by simp [h12]),
    if_neg (by simp [h13]), if_neg (by simp [h14]), if_neg (by simp [h15]),
    if_neg (by simp [h16]), if_neg (by simp [h17]), if_neg (by simp [h18]),
    if_neg (by simp [h19]), if_neg (by simp [h20]), if_neg (by simp [h21]),
    if_neg (by simp [h21b]), if_neg (by simp [h22]), if_neg (by simp [h23]),
    if_neg (by simp [h24]), if_neg (by simp [h25]), if_neg (by simp [hv2]),
    if_neg (by simp [h26]), if_neg (by simp [h27]), if_neg (by simp [h28]),
    if_neg (by simp [h29]), if_pos (by simp [h30])]

/-- Symbolic decoder for all GPR unsigned-immediate `:lo12:` load/store relocations
    (`R_AARCH64_LDST{8,16,32,64}_ABS_LO12_NC`, covering `LDRB`, `STRB`, `LDRSB`, `LDRH`, `STRH`,
    `LDRSH`, `LDR` 32/64, `STR` 32/64, `LDRSW`). -/
theorem decode_ldstGprLo12Word {scale : Nat} {w : BitVec 32} {target : BitVec 64}
    (hscale : (w.extractLsb' 30 2).toNat = scale)
    (hw1 : w &&& 0x3f000000#32 = 0x39000000#32)
    (hw2 : (w &&& 0xffc00000#32 == 0xf9800000#32) = false)
    (hal : Lo12Aligned scale target) :
    decode (lo12Word scale w target) =
      mkLoadStoreInst scale (w.extractLsb' 22 2).toNat (Reg.fromZRBits (w.extractLsb' 0 5))
        (.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of target)) := by
  have hle : scale ≤ 4 := by
    subst hscale
    have := (w.extractLsb' 30 2).isLt
    omega
  have himm := lo12Word_imm hle w target hal
  have ⟨hm1, hm2, hsz, hopc, hrn, hrt⟩ :=
    lo12_mask_preserve (lo12Word_mask (scale := scale) w target)
  have hv1 : lo12Word scale w target &&& 0x3f000000#32 = 0x39000000#32 := hm2.trans hw1
  have hv2 : (lo12Word scale w target &&& 0xffc00000#32 == 0xf9800000#32) = false := by
    rw [hm1]; exact hw2
  rw [decode_ldstGprUnsigned hv1 hv2]
  dsimp only
  rw [hsz, hscale, hopc, hrn, hrt, himm]

set_option linter.deprecated false in
theorem decode_ldstSimdUnsigned {v : BitVec 32}
    (hv1 : v &&& 0x3f000000#32 = 0x3d000000#32) :
    decode v =
      (let sizeBits := (v.extractLsb' 30 2).toNat
       let opc := (v.extractLsb' 22 2).toNat
       match decodeSimdLoadStoreType sizeBits opc with
       | some (isLoad, sz, scale) =>
         let imm12 : BitVec 12 := v.extractLsb' 10 12
         let offset : BitVec 64 := (imm12.zeroExtend 64) <<< scale
         let rn := Reg.fromSPBits (v.extractLsb' 5 5)
         let vt : BitVec 5 := v.extractLsb' 0 5
         let addr := AddrMode.Offset rn offset
         if isLoad then some (.ldrSimd sz vt addr)
         else some (.strSimd sz vt addr)
       | none => none) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = false := by bv_bits
  have h11 : (v &&& 0x7e000000#32 == 0x34000000#32) = false := by bv_bits
  have h12 : (v &&& 0x7e000000#32 == 0x36000000#32) = false := by bv_bits
  have h13 : (v &&& 0xff000010#32 == 0x54000000#32) = false := by bv_bits
  have h14 : (v &&& 0xff9ffc1f#32 == 0xd61f0000#32) = false := by bv_bits
  have h15 : (v &&& 0x1f000000#32 == 0x0a000000#32) = false := by bv_bits
  have h16 : (v &&& 0x1f200000#32 == 0x0b000000#32) = false := by bv_bits
  have h17 : (v &&& 0x1fe00000#32 == 0x0b200000#32) = false := by bv_bits
  have h18 : (v &&& 0x1fe0fc00#32 == 0x1a000000#32) = false := by bv_bits
  have h19 : (v &&& 0x3fe00410#32 == 0x3a400000#32) = false := by bv_bits
  have h20 : (v &&& 0x3fe00800#32 == 0x1a800000#32) = false := by bv_bits
  have h21 : (v &&& 0x7fff0000#32 == 0x5ac00000#32) = false := by bv_bits
  have h21b : (v &&& 0x7fe0e000#32 == 0x1ac04000#32) = false := by bv_bits
  have h22 : (v &&& 0x7fe00000#32 == 0x1ac00000#32) = false := by bv_bits
  have h23 : (v &&& 0x7f000000#32 == 0x1b000000#32) = false := by bv_bits
  have h24 : (v &&& 0x7f800000#32 == 0x28000000#32) = false := by bv_bits
  have h25 : (v &&& 0x3e000000#32 == 0x28000000#32) = false := by bv_bits
  have h25b : (v &&& 0xffc00000#32 == 0xf9800000#32) = false := by bv_bits
  have h26 : (v &&& 0xffe00c00#32 == 0xf8800000#32) = false := by bv_bits
  have h27 : (v &&& 0xffe00c00#32 == 0xf8a00800#32) = false := by bv_bits
  have h28 : (v &&& 0x3f200c00#32 == 0x38200000#32) = false := by bv_bits
  have h29 : (v &&& 0x3f200c00#32 == 0x19000000#32) = false := by bv_bits
  have h30 : (v &&& 0x3f000000#32 == 0x39000000#32) = false := by bv_bits
  have h31 : (v &&& 0x3f000000#32 == 0x38000000#32) = false := by bv_bits
  have h32 : (v &&& 0x3f000000#32 == 0x18000000#32) = false := by bv_bits
  have h33 : (v &&& 0x3f000000#32 == 0x1c000000#32) = false := by bv_bits
  have h34 : (v &&& 0x3fbffc00#32 == 0x089ffc00#32) = false := by bv_bits
  have h35 : (v &&& 0x3fff7c00#32 == 0x085f7c00#32) = false := by bv_bits
  have h36 : (v &&& 0x3fe07c00#32 == 0x08007c00#32) = false := by bv_bits
  have h37 : (v &&& 0xbfff0000#32 == 0x887f0000#32) = false := by bv_bits
  have h38 : (v &&& 0xbfe00000#32 == 0x88200000#32) = false := by bv_bits
  have h39 : (v &&& 0x3fa07c00#32 == 0x08a07c00#32) = false := by bv_bits
  have h40 : (v &&& 0xbfa07c00#32 == 0x08207c00#32) = false := by bv_bits
  have h41 : (v &&& 0xffd00000#32 == 0xd5100000#32) = false := by bv_bits
  have h42 : (v &&& 0xfffff01f#32 == 0xd503301f#32) = false := by bv_bits
  have h43 : (v &&& 0x3f800000#32 == 0x2c000000#32) = false := by bv_bits
  have h44 : (v &&& 0x3e000000#32 == 0x2c000000#32) = false := by bv_bits
  have h45 : (v &&& 0x3f000000#32 == 0x3d000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]),
    if_neg (by simp [h7]), if_neg (by simp [h8]), if_neg (by simp [h9]),
    if_neg (by simp [h10]), if_neg (by simp [h11]), if_neg (by simp [h12]),
    if_neg (by simp [h13]), if_neg (by simp [h14]), if_neg (by simp [h15]),
    if_neg (by simp [h16]), if_neg (by simp [h17]), if_neg (by simp [h18]),
    if_neg (by simp [h19]), if_neg (by simp [h20]), if_neg (by simp [h21]),
    if_neg (by simp [h21b]), if_neg (by simp [h22]), if_neg (by simp [h23]),
    if_neg (by simp [h24]), if_neg (by simp [h25]), if_neg (by simp [h25b]),
    if_neg (by simp [h26]), if_neg (by simp [h27]), if_neg (by simp [h28]),
    if_neg (by simp [h29]), if_neg (by simp [h30]), if_neg (by simp [h31]),
    if_neg (by simp [h32]), if_neg (by simp [h33]), if_neg (by simp [h34]),
    if_neg (by simp [h35]), if_neg (by simp [h36]), if_neg (by simp [h37]),
    if_neg (by simp [h38]), if_neg (by simp [h39]), if_neg (by simp [h40]),
    if_neg (by simp [h41]), if_neg (by simp [h42]), if_neg (by simp [h43]),
    if_neg (by simp [h44]), if_pos (by simp [h45])]
  rfl

/-- Symbolic decoder for all SIMD/FP unsigned-immediate `:lo12:` load/store relocations
    (`R_AARCH64_LDST{8,16,32,64,128}_ABS_LO12_NC`, covering `LDR`/`STR` `Bt`/`Ht`/`St`/`Dt`/`Qt`). -/
theorem decode_ldstSimdLo12Word {scale : Nat} {w : BitVec 32} {target : BitVec 64}
    {isLoad : Bool} {sz : SimdMemSize}
    (htype : decodeSimdLoadStoreType (w.extractLsb' 30 2).toNat (w.extractLsb' 22 2).toNat =
      some (isLoad, sz, scale))
    (hw1 : w &&& 0x3f000000#32 = 0x3d000000#32)
    (hal : Lo12Aligned scale target) :
    decode (lo12Word scale w target) =
      let addr := AddrMode.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of target)
      if isLoad then some (.ldrSimd sz (w.extractLsb' 0 5) addr)
      else some (.strSimd sz (w.extractLsb' 0 5) addr) := by
  have hle : scale ≤ 4 := by
    revert htype
    generalize (w.extractLsb' 30 2).toNat = s
    generalize (w.extractLsb' 22 2).toNat = o
    unfold decodeSimdLoadStoreType
    split <;> intro h <;> cases h <;> omega
  have himm := lo12Word_imm hle w target hal
  have ⟨_, hm2, hsz, hopc, hrn, hrt⟩ :=
    lo12_mask_preserve (lo12Word_mask (scale := scale) w target)
  have hv1 : lo12Word scale w target &&& 0x3f000000#32 = 0x3d000000#32 := hm2.trans hw1
  rw [decode_ldstSimdUnsigned hv1]
  dsimp only
  rw [hsz, hopc, htype]
  dsimp only
  rw [hrn, hrt, himm]

/-! ### 19-Bit and 14-Bit PC-Relative Relocations -/

theorem imm19WordOff_extract (w : BitVec 32) (d : BitVec 64) :
    (imm19WordOff w d).extractLsb' 5 19 = (d >>> 2).extractLsb' 0 19 := by
  unfold imm19WordOff
  bv_slice

theorem imm19WordOff_mask (w : BitVec 32) (d : BitVec 64) :
    imm19WordOff w d &&& 0xff00001f#32 = w &&& 0xff00001f#32 := by
  unfold imm19WordOff
  bv_slice

theorem imm19_mask_preserve {v w : BitVec 32} (hmask : v &&& 0xff00001f#32 = w &&& 0xff00001f#32) :
    v &&& 0xff000010#32 = w &&& 0xff000010#32 ∧
    v &&& 0x7e000000#32 = w &&& 0x7e000000#32 ∧
    v &&& 0x3f000000#32 = w &&& 0x3f000000#32 ∧
    v.getLsbD 31 = w.getLsbD 31 ∧
    v.getLsbD 24 = w.getLsbD 24 ∧
    v.extractLsb' 30 2 = w.extractLsb' 30 2 ∧
    v.extractLsb' 0 5 = w.extractLsb' 0 5 ∧
    v.extractLsb' 0 4 = w.extractLsb' 0 4 := by
  bv_slice

theorem imm19Word_imm {w : BitVec 32} {place target : BitVec 64}
    (hr : Imm19InRange place target) :
    (((imm19Word w place target).extractLsb' 5 19).signExtend 64) <<< 2 = target - place := by
  obtain ⟨h4, hfit1, hfit2⟩ := hr
  unfold imm19Word
  rw [imm19WordOff_extract]
  generalize target - place = d at h4 hfit1 hfit2 ⊢
  have hlt : d + 0x100000#64 < 0x200000#64 := by
    rw [BitVec.toInt_eq_toNat_cond] at hfit1 hfit2
    rw [BitVec.lt_def, BitVec.toNat_add]
    have := d.isLt
    simp only [BitVec.toNat_ofNat]
    split at hfit1 <;> omega
  have hal : d &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (3#64).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h4
  bv_bits

set_option linter.deprecated false in
theorem decode_bcond {v : BitVec 32} (hv : v &&& 0xff000010#32 = 0x54000000#32) :
    decode v = some (.bCond (CondCode.ofBits (v.extractLsb' 0 4))
      (((v.extractLsb' 5 19).signExtend 64) <<< 2)) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = false := by bv_bits
  have h11 : (v &&& 0x7e000000#32 == 0x34000000#32) = false := by bv_bits
  have h12 : (v &&& 0x7e000000#32 == 0x36000000#32) = false := by bv_bits
  have h13 : (v &&& 0xff000010#32 == 0x54000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]),
    if_neg (by simp [h7]), if_neg (by simp [h8]), if_neg (by simp [h9]),
    if_neg (by simp [h10]), if_neg (by simp [h11]), if_neg (by simp [h12]),
    if_pos (by simp [h13])]

/-- Symbolic decoder for `R_AARCH64_CONDBR19` on `B.<cond>`. -/
theorem decode_imm19Word_bcond {w : BitVec 32} (hw : w &&& 0xff000010#32 = 0x54000000#32)
    {place target : BitVec 64} (hr : Imm19InRange place target) :
    decode (imm19Word w place target) =
      some (.bCond (CondCode.ofBits (w.extractLsb' 0 4)) (target - place)) := by
  have himm := imm19Word_imm (w := w) hr
  have ⟨hm1, _, _, _, _, _, _, hc⟩ := imm19_mask_preserve (imm19WordOff_mask w (target - place))
  have hv : imm19Word w place target &&& 0xff000010#32 = 0x54000000#32 := hm1.trans hw
  change (imm19Word w place target).extractLsb' 0 4 = w.extractLsb' 0 4 at hc
  rw [decode_bcond hv, himm, hc]

set_option linter.deprecated false in
theorem decode_cbz {v : BitVec 32} (hv : v &&& 0x7e000000#32 = 0x34000000#32) :
    decode v =
      let sf : RegWidth := if v.getLsbD 31 then .W64 else .W32
      let target : BitVec 64 := ((v.extractLsb' 5 19).signExtend 64) <<< 2
      let rt := Reg.fromZRBits (v.extractLsb' 0 5)
      some (.cbz sf (v.getLsbD 24) rt target) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = false := by bv_bits
  have h11 : (v &&& 0x7e000000#32 == 0x34000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]),
    if_neg (by simp [h7]), if_neg (by simp [h8]), if_neg (by simp [h9]),
    if_neg (by simp [h10]), if_pos (by simp [h11])]
  rfl

/-- Symbolic decoder for `R_AARCH64_CONDBR19` on `CBZ`/`CBNZ`. -/
theorem decode_imm19Word_cbz {w : BitVec 32} (hw : w &&& 0x7e000000#32 = 0x34000000#32)
    {place target : BitVec 64} (hr : Imm19InRange place target) :
    decode (imm19Word w place target) =
      let sf : RegWidth := if w.getLsbD 31 then .W64 else .W32
      let disp : BitVec 64 := target - place
      let rt := Reg.fromZRBits (w.extractLsb' 0 5)
      some (.cbz sf (w.getLsbD 24) rt disp) := by
  have himm := imm19Word_imm (w := w) hr
  have ⟨_, hm2, _, h31, h24, _, hrt, _⟩ := imm19_mask_preserve (imm19WordOff_mask w (target - place))
  have hv : imm19Word w place target &&& 0x7e000000#32 = 0x34000000#32 := hm2.trans hw
  change (imm19Word w place target).getLsbD 31 = w.getLsbD 31 at h31
  change (imm19Word w place target).getLsbD 24 = w.getLsbD 24 at h24
  change (imm19Word w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrt
  rw [decode_cbz hv]
  dsimp only
  rw [h31, h24, hrt, himm]

set_option linter.deprecated false in
theorem decode_ldrLit {v : BitVec 32} (hv : v &&& 0x3f000000#32 = 0x18000000#32) :
    decode v =
      (let opc := (v.extractLsb' 30 2).toNat
       let imm19 : BitVec 19 := v.extractLsb' 5 19
       let offset : BitVec 64 := (imm19.signExtend 64) <<< 2
       let rtBits := v.extractLsb' 0 5
       let rt := Reg.fromZRBits rtBits
       match opc with
       | 0 => some (.ldrLit .W32 false rt offset)
       | 1 => some (.ldrLit .W64 false rt offset)
       | 2 => some (.ldrLit .W64 true rt offset)
       | _ => some (.prfmLit rtBits offset)) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = false := by bv_bits
  have h11 : (v &&& 0x7e000000#32 == 0x34000000#32) = false := by bv_bits
  have h12 : (v &&& 0x7e000000#32 == 0x36000000#32) = false := by bv_bits
  have h13 : (v &&& 0xff000010#32 == 0x54000000#32) = false := by bv_bits
  have h14 : (v &&& 0xff9ffc1f#32 == 0xd61f0000#32) = false := by bv_bits
  have h15 : (v &&& 0x1f000000#32 == 0x0a000000#32) = false := by bv_bits
  have h16 : (v &&& 0x1f200000#32 == 0x0b000000#32) = false := by bv_bits
  have h17 : (v &&& 0x1fe00000#32 == 0x0b200000#32) = false := by bv_bits
  have h18 : (v &&& 0x1fe0fc00#32 == 0x1a000000#32) = false := by bv_bits
  have h19 : (v &&& 0x3fe00410#32 == 0x3a400000#32) = false := by bv_bits
  have h20 : (v &&& 0x3fe00800#32 == 0x1a800000#32) = false := by bv_bits
  have h21 : (v &&& 0x7fff0000#32 == 0x5ac00000#32) = false := by bv_bits
  have h21b : (v &&& 0x7fe0e000#32 == 0x1ac04000#32) = false := by bv_bits
  have h22 : (v &&& 0x7fe00000#32 == 0x1ac00000#32) = false := by bv_bits
  have h23 : (v &&& 0x7f000000#32 == 0x1b000000#32) = false := by bv_bits
  have h24 : (v &&& 0x7f800000#32 == 0x28000000#32) = false := by bv_bits
  have h25 : (v &&& 0x3e000000#32 == 0x28000000#32) = false := by bv_bits
  have h25b : (v &&& 0xffc00000#32 == 0xf9800000#32) = false := by bv_bits
  have h26 : (v &&& 0xffe00c00#32 == 0xf8800000#32) = false := by bv_bits
  have h27 : (v &&& 0xffe00c00#32 == 0xf8a00800#32) = false := by bv_bits
  have h28 : (v &&& 0x3f200c00#32 == 0x38200000#32) = false := by bv_bits
  have h29 : (v &&& 0x3f200c00#32 == 0x19000000#32) = false := by bv_bits
  have h30 : (v &&& 0x3f000000#32 == 0x39000000#32) = false := by bv_bits
  have h31 : (v &&& 0x3f000000#32 == 0x38000000#32) = false := by bv_bits
  have h32 : (v &&& 0x3f000000#32 == 0x18000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]),
    if_neg (by simp [h7]), if_neg (by simp [h8]), if_neg (by simp [h9]),
    if_neg (by simp [h10]), if_neg (by simp [h11]), if_neg (by simp [h12]),
    if_neg (by simp [h13]), if_neg (by simp [h14]), if_neg (by simp [h15]),
    if_neg (by simp [h16]), if_neg (by simp [h17]), if_neg (by simp [h18]),
    if_neg (by simp [h19]), if_neg (by simp [h20]), if_neg (by simp [h21]),
    if_neg (by simp [h21b]), if_neg (by simp [h22]), if_neg (by simp [h23]),
    if_neg (by simp [h24]), if_neg (by simp [h25]), if_neg (by simp [h25b]),
    if_neg (by simp [h26]), if_neg (by simp [h27]), if_neg (by simp [h28]),
    if_neg (by simp [h29]), if_neg (by simp [h30]), if_neg (by simp [h31]),
    if_pos (by simp [h32])]
  rfl

/-- Symbolic decoder for `R_AARCH64_LD_PREL_LO19` on `LDR`/`LDRSW` (literal). -/
theorem decode_imm19Word_ldrLit {w : BitVec 32} (hw : w &&& 0x3f000000#32 = 0x18000000#32)
    {place target : BitVec 64} (hr : Imm19InRange place target) :
    decode (imm19Word w place target) =
      (let opc := (w.extractLsb' 30 2).toNat
       let offset : BitVec 64 := target - place
       let rtBits := w.extractLsb' 0 5
       let rt := Reg.fromZRBits rtBits
       match opc with
       | 0 => some (.ldrLit .W32 false rt offset)
       | 1 => some (.ldrLit .W64 false rt offset)
       | 2 => some (.ldrLit .W64 true rt offset)
       | _ => some (.prfmLit rtBits offset)) := by
  have himm := imm19Word_imm (w := w) hr
  have ⟨_, _, hm3, _, _, hopc, hrt, _⟩ := imm19_mask_preserve (imm19WordOff_mask w (target - place))
  have hv : imm19Word w place target &&& 0x3f000000#32 = 0x18000000#32 := hm3.trans hw
  change (imm19Word w place target).extractLsb' 30 2 = w.extractLsb' 30 2 at hopc
  change (imm19Word w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrt
  rw [decode_ldrLit hv]
  dsimp only
  rw [hopc, hrt, himm]

theorem tstbr14WordOff_extract (w : BitVec 32) (d : BitVec 64) :
    (tstbr14WordOff w d).extractLsb' 5 14 = (d >>> 2).extractLsb' 0 14 := by
  unfold tstbr14WordOff
  bv_slice

theorem tstbr14WordOff_mask (w : BitVec 32) (d : BitVec 64) :
    tstbr14WordOff w d &&& 0xfff8001f#32 = w &&& 0xfff8001f#32 := by
  unfold tstbr14WordOff
  bv_slice

theorem tstbr14_mask_preserve {v w : BitVec 32} (hmask : v &&& 0xfff8001f#32 = w &&& 0xfff8001f#32) :
    v &&& 0x7e000000#32 = w &&& 0x7e000000#32 ∧
    v.getLsbD 31 = w.getLsbD 31 ∧
    v.getLsbD 24 = w.getLsbD 24 ∧
    v.extractLsb' 19 5 = w.extractLsb' 19 5 ∧
    v.extractLsb' 0 5 = w.extractLsb' 0 5 := by
  bv_slice

theorem tstbr14Word_imm {w : BitVec 32} {place target : BitVec 64}
    (hr : TstBr14InRange place target) :
    (((tstbr14Word w place target).extractLsb' 5 14).signExtend 64) <<< 2 = target - place := by
  obtain ⟨h4, hfit1, hfit2⟩ := hr
  unfold tstbr14Word
  rw [tstbr14WordOff_extract]
  generalize target - place = d at h4 hfit1 hfit2 ⊢
  have hlt : d + 0x8000#64 < 0x10000#64 := by
    rw [BitVec.toInt_eq_toNat_cond] at hfit1 hfit2
    rw [BitVec.lt_def, BitVec.toNat_add]
    have := d.isLt
    simp only [BitVec.toNat_ofNat]
    split at hfit1 <;> omega
  have hal : d &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (3#64).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h4
  bv_bits

set_option linter.deprecated false in
theorem decode_tbz {v : BitVec 32} (hv : v &&& 0x7e000000#32 = 0x36000000#32) :
    decode v =
      let sf : RegWidth := if v.getLsbD 31 then .W64 else .W32
      let bitPos := (if v.getLsbD 31 then 32 else 0) + (v.extractLsb' 19 5).toNat
      let target : BitVec 64 := ((v.extractLsb' 5 14).signExtend 64) <<< 2
      let rt := Reg.fromZRBits (v.extractLsb' 0 5)
      some (.tbz sf (v.getLsbD 24) rt bitPos target) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = false := by bv_bits
  have h11 : (v &&& 0x7e000000#32 == 0x34000000#32) = false := by bv_bits
  have h12 : (v &&& 0x7e000000#32 == 0x36000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]),
    if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]),
    if_neg (by simp [h7]), if_neg (by simp [h8]), if_neg (by simp [h9]),
    if_neg (by simp [h10]), if_neg (by simp [h11]), if_pos (by simp [h12])]

/-- Symbolic decoder for `R_AARCH64_TSTBR14` on `TBZ`/`TBNZ`. -/
theorem decode_tstbr14Word {w : BitVec 32} (hw : w &&& 0x7e000000#32 = 0x36000000#32)
    {place target : BitVec 64} (hr : TstBr14InRange place target) :
    decode (tstbr14Word w place target) =
      let sf : RegWidth := if w.getLsbD 31 then .W64 else .W32
      let bitPos := (if w.getLsbD 31 then 32 else 0) + (w.extractLsb' 19 5).toNat
      let disp : BitVec 64 := target - place
      let rt := Reg.fromZRBits (w.extractLsb' 0 5)
      some (.tbz sf (w.getLsbD 24) rt bitPos disp) := by
  have himm := tstbr14Word_imm (w := w) hr
  have ⟨hm, h31, h24, hb40, hrt⟩ := tstbr14_mask_preserve (tstbr14WordOff_mask w (target - place))
  have hv : tstbr14Word w place target &&& 0x7e000000#32 = 0x36000000#32 := hm.trans hw
  change (tstbr14Word w place target).getLsbD 31 = w.getLsbD 31 at h31
  change (tstbr14Word w place target).getLsbD 24 = w.getLsbD 24 at h24
  change (tstbr14Word w place target).extractLsb' 19 5 = w.extractLsb' 19 5 at hb40
  change (tstbr14Word w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrt
  rw [decode_tbz hv]
  dsimp only
  rw [h31, h24, hb40, hrt, himm]

/-! ### `TLSDESC -> TLSLE` and `TLSLE` Relocation Word Decoders -/

theorem decode_moveWide64 {v : BitVec 32}
    (hv : v &&& 0x9f800000#32 = 0x92800000#32) :
    decode v =
      let opc := (v.extractLsb' 29 2).toNat
      let hw := (v.extractLsb' 21 2).toNat * 16
      let imm16 : BitVec 16 := v.extractLsb' 5 16
      let rd := Reg.fromZRBits (v.extractLsb' 0 5)
      match opc with
      | 0 => some (.moveWide .W64 .MOVN rd imm16 hw)
      | 2 => some (.moveWide .W64 .MOVZ rd imm16 hw)
      | 3 => some (.moveWide .W64 .MOVK rd imm16 hw)
      | _ => none := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = true := by bv_bits
  have hsf : v.getLsbD 31 = true := by bv_bits
  unfold decode
  simp only [h1, h2, h3, h3a, h3b, h3c, h4, h5, h6, h7, hsf, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Symbolic decoder for `R_AARCH64_TLSDESC_ADR_PAGE21` relaxed to Local-Exec (`TLSLE`):
    `tlsdescAdrPage21Word target` decodes to `movz x0, #((target >> 16) & 0xffff), lsl #16`. -/
theorem decode_tlsdescAdrPage21Word (target : BitVec 64) :
    decode (tlsdescAdrPage21Word target) =
      some (.moveWide .W64 .MOVZ .x0 (target.extractLsb' 16 16) 16) := by
  have hv : tlsdescAdrPage21Word target &&& 0x9f800000#32 = 0x92800000#32 := by
    unfold tlsdescAdrPage21Word; bv_bits
  have hopc : (tlsdescAdrPage21Word target).extractLsb' 29 2 = 2#2 := by
    unfold tlsdescAdrPage21Word; bv_bits
  have hhw : (tlsdescAdrPage21Word target).extractLsb' 21 2 = 1#2 := by
    unfold tlsdescAdrPage21Word; bv_bits
  have hrd : (tlsdescAdrPage21Word target).extractLsb' 0 5 = 0#5 := by
    unfold tlsdescAdrPage21Word; bv_bits
  have himm : (tlsdescAdrPage21Word target).extractLsb' 5 16 = target.extractLsb' 16 16 := by
    unfold tlsdescAdrPage21Word; bv_bits
  rw [decode_moveWide64 hv]
  dsimp only
  rw [hopc, hhw, hrd, himm]
  rfl

/-- Symbolic decoder for `R_AARCH64_TLSDESC_LD64_LO12` relaxed to Local-Exec (`TLSLE`):
    `tlsdescLd64Lo12Word target` decodes to `movk x0, #(target & 0xffff)`. -/
theorem decode_tlsdescLd64Lo12Word (target : BitVec 64) :
    decode (tlsdescLd64Lo12Word target) =
      some (.moveWide .W64 .MOVK .x0 (target.extractLsb' 0 16) 0) := by
  have hv : tlsdescLd64Lo12Word target &&& 0x9f800000#32 = 0x92800000#32 := by
    unfold tlsdescLd64Lo12Word; bv_bits
  have hopc : (tlsdescLd64Lo12Word target).extractLsb' 29 2 = 3#2 := by
    unfold tlsdescLd64Lo12Word; bv_bits
  have hhw : (tlsdescLd64Lo12Word target).extractLsb' 21 2 = 0#2 := by
    unfold tlsdescLd64Lo12Word; bv_bits
  have hrd : (tlsdescLd64Lo12Word target).extractLsb' 0 5 = 0#5 := by
    unfold tlsdescLd64Lo12Word; bv_bits
  have himm : (tlsdescLd64Lo12Word target).extractLsb' 5 16 = target.extractLsb' 0 16 := by
    unfold tlsdescLd64Lo12Word; bv_bits
  rw [decode_moveWide64 hv]
  dsimp only
  rw [hopc, hhw, hrd, himm]
  rfl

theorem decode_addHi12 {v : BitVec 32}
    (hv : v &&& 0xffc00000#32 = 0x91400000#32) :
    decode v = some (.addSubImm .W64 .ADD
      (Reg.fromSPBits (v.extractLsb' 0 5))
      (Reg.fromSPBits (v.extractLsb' 5 5))
      (v.extractLsb' 10 12) true) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = true := by bv_bits
  have hsf : v.getLsbD 31 = true := by bv_bits
  have h30 : v.getLsbD 30 = false := by bv_bits
  have h29 : v.getLsbD 29 = false := by bv_bits
  have h22 : v.getLsbD 22 = true := by bv_bits
  unfold decode
  simp only [h1, h2, h3, h3a, h3b, h3c, h4, h5, hsf, h30, h29, h22, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Symbolic decoder for `R_AARCH64_TLSLE_ADD_TPREL_HI12`. -/
theorem decode_tprelHi12Word {w : BitVec 32} (hw : w &&& 0xffc00000#32 = 0x91400000#32)
    (target : BitVec 64) :
    decode (tprelHi12Word w target) =
      some (.addSubImm .W64 .ADD
        (Reg.fromSPBits (w.extractLsb' 0 5))
        (Reg.fromSPBits (w.extractLsb' 5 5))
        (target.extractLsb' 12 12) true) := by
  have hm : tprelHi12Word w target &&& 0xffc003ff#32 = w &&& 0xffc003ff#32 := by
    unfold tprelHi12Word; bv_slice
  have ⟨hm1, _, _, _, hrn, hrd⟩ := lo12_mask_preserve hm
  have hv : tprelHi12Word w target &&& 0xffc00000#32 = 0x91400000#32 := hm1.trans hw
  have himm : (tprelHi12Word w target).extractLsb' 10 12 = target.extractLsb' 12 12 := by
    unfold tprelHi12Word; bv_slice
  rw [decode_addHi12 hv, himm, hrd, hrn]

/-! ## Fetch Rules for `Program.hasWords` -/

section RelocFetchRules
set_option linter.literalFetch false

/-- Fetch rule for an `ADRP` relocated slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_adrpAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {rd : Reg}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (adrpWord w P target))
    (hw : (w &&& 0x9f000000#32 == 0x90000000#32) = true)
    (hrd : Reg.fromZRBits (w.extractLsb' 0 5) = rd)
    (hrange : AdrpInRange P target) :
    prog.fetch pc =
      some (.adr true rd (pageOf target - pageOf pc)) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_adrpWord (beq_iff_eq.mp hw) hrange, hrd, h_P, ← h_pc]

/-- Fetch rule for an `ADD :lo12:` relocated slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_addLo12At {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {target : BitVec 64}
    {rd rn : Reg}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_get : words[i]? = some (lo12Word 0 w target))
    (hw : (w &&& 0xffc00000#32 == 0x91000000#32) = true)
    (hrd : Reg.fromSPBits (w.extractLsb' 0 5) = rd)
    (hrn : Reg.fromSPBits (w.extractLsb' 5 5) = rn) :
    prog.fetch pc =
      some (.addSubImm .W64 .ADD rd rn ((lo12Of target).truncate 12) false) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_addLo12Word (beq_iff_eq.mp hw) target, hrd, hrn]

/-- Fetch rule for a GPR `:lo12:` load/store slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_ldstGprLo12At {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {scale : Nat} {w : BitVec 32} {target : BitVec 64}
    {inst : Instr}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_get : words[i]? = some (lo12Word scale w target))
    (h_scale : (w.extractLsb' 30 2).toNat = scale)
    (hw1 : (w &&& 0x3f000000#32 == 0x39000000#32) = true)
    (hw2 : (w &&& 0xffc00000#32 == 0xf9800000#32) = false)
    (h_inst : mkLoadStoreInst scale (w.extractLsb' 22 2).toNat (Reg.fromZRBits (w.extractLsb' 0 5))
      (.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of target)) = some inst)
    (hal : Lo12Aligned scale target) :
    prog.fetch pc = some inst := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_ldstGprLo12Word h_scale (beq_iff_eq.mp hw1) hw2 hal, h_inst]

/-- Fetch rule for a SIMD/FP `:lo12:` load/store slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_ldstSimdLo12At {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {scale : Nat} {w : BitVec 32} {target : BitVec 64}
    {isLoad : Bool} {sz : SimdMemSize} {inst : Instr}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_get : words[i]? = some (lo12Word scale w target))
    (htype : decodeSimdLoadStoreType (w.extractLsb' 30 2).toNat (w.extractLsb' 22 2).toNat =
      some (isLoad, sz, scale))
    (hw1 : (w &&& 0x3f000000#32 == 0x3d000000#32) = true)
    (h_inst : (let addr := AddrMode.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of target)
      if isLoad then some (.ldrSimd sz (w.extractLsb' 0 5) addr)
      else some (.strSimd sz (w.extractLsb' 0 5) addr)) = some inst)
    (hal : Lo12Aligned scale target) :
    prog.fetch pc = some inst := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_ldstSimdLo12Word htype (beq_iff_eq.mp hw1) hal, h_inst]

/-- Fetch rule for an unchecked `ADRP` (`R_AARCH64_ADR_PREL_PG_HI21_NC`) slot at index `i`. -/
theorem fetch_of_hasWords_adrpNcAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {rd : Reg}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (adrpWord w P target))
    (hw : (w &&& 0x9f000000#32 == 0x90000000#32) = true)
    (hrd : Reg.fromZRBits (w.extractLsb' 0 5) = rd) :
    prog.fetch pc =
      some (.adr true rd (((pageOf target - pageOf pc).extractLsb' 12 21).signExtend 64 <<< 12)) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_adrpWord_nc (beq_iff_eq.mp hw) P target, hrd, h_P, ← h_pc]

/-- Fetch rule for an `ADR` (`R_AARCH64_ADR_PREL_LO21`) slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_adrAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {rd : Reg}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (adrWord w P target))
    (hw : (w &&& 0x9f000000#32 == 0x10000000#32) = true)
    (hrd : Reg.fromZRBits (w.extractLsb' 0 5) = rd)
    (hrange : AdrInRange P target) :
    prog.fetch pc =
      some (.adr false rd (target - pc)) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_adrWord (beq_iff_eq.mp hw) hrange, hrd, h_P, ← h_pc]

theorem lo12Aligned_zero (target : BitVec 64) : Lo12Aligned 0 target :=
  BitVec.and_zero

/-- Fetch rule for a `BL` relocated slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_blAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (branchWord w P target))
    (hw : (w &&& 0xfc000000#32 == 0x94000000#32) = true)
    (hrange : BranchInRange P target) :
    prog.fetch pc =
      some (.bl (target - pc)) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_branchWord_bl (beq_iff_eq.mp hw) hrange, h_P, ← h_pc]

/-- Fetch rule for a `B` relocated slot at index `i` in `hasWords`. -/
theorem fetch_of_hasWords_bAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (branchWord w P target))
    (hw : (w &&& 0xfc000000#32 == 0x14000000#32) = true)
    (hrange : BranchInRange P target) :
    prog.fetch pc =
      some (.b (target - pc)) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_branchWord_b (beq_iff_eq.mp hw) hrange, h_P, ← h_pc]

/-- Fetch rule for a `B.cond` relocated slot (`R_AARCH64_CONDBR19`). -/
theorem fetch_of_hasWords_bcondAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {cc : CondCode}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (imm19Word w P target))
    (hw : (w &&& 0xff000010#32 == 0x54000000#32) = true)
    (hcc : CondCode.ofBits (w.extractLsb' 0 4) = cc)
    (hrange : Imm19InRange P target) :
    prog.fetch pc =
      some (.bCond cc (target - pc)) := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_imm19Word_bcond (beq_iff_eq.mp hw) hrange, hcc, h_P, ← h_pc]

/-- Fetch rule for a `CBZ`/`CBNZ` relocated slot (`R_AARCH64_CONDBR19`). -/
theorem fetch_of_hasWords_cbzAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {inst : Instr}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (imm19Word w P target))
    (hw : (w &&& 0x7e000000#32 == 0x34000000#32) = true)
    (h_inst : (let sf : RegWidth := if w.getLsbD 31 then .W64 else .W32
      let disp : BitVec 64 := target - pc
      let rt := Reg.fromZRBits (w.extractLsb' 0 5)
      some (.cbz sf (w.getLsbD 24) rt disp)) = some inst)
    (hrange : Imm19InRange P target) :
    prog.fetch pc = some inst := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_imm19Word_cbz (beq_iff_eq.mp hw) hrange]
  dsimp only
  rw [h_P]
  exact h_inst

/-- Fetch rule for an `LDR`/`LDRSW` (literal) relocated slot (`R_AARCH64_LD_PREL_LO19`). -/
theorem fetch_of_hasWords_ldrLitAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {inst : Instr}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (imm19Word w P target))
    (hw : (w &&& 0x3f000000#32 == 0x18000000#32) = true)
    (h_inst : (let opc := (w.extractLsb' 30 2).toNat
      let offset : BitVec 64 := target - pc
      let rtBits := w.extractLsb' 0 5
      let rt := Reg.fromZRBits rtBits
      match opc with
      | 0 => some (.ldrLit .W32 false rt offset)
      | 1 => some (.ldrLit .W64 false rt offset)
      | 2 => some (.ldrLit .W64 true rt offset)
      | _ => some (.prfmLit rtBits offset)) = some inst)
    (hrange : Imm19InRange P target) :
    prog.fetch pc = some inst := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_imm19Word_ldrLit (beq_iff_eq.mp hw) hrange]
  dsimp only
  rw [h_P]
  exact h_inst

/-- Fetch rule for a `TBZ`/`TBNZ` relocated slot (`R_AARCH64_TSTBR14`). -/
theorem fetch_of_hasWords_tstbr14At {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {w : BitVec 32} {P target : BitVec 64} {inst : Instr}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_P : P = pc)
    (h_get : words[i]? = some (tstbr14Word w P target))
    (hw : (w &&& 0x7e000000#32 == 0x36000000#32) = true)
    (h_inst : (let sf : RegWidth := if w.getLsbD 31 then .W64 else .W32
      let bitPos := (if w.getLsbD 31 then 32 else 0) + (w.extractLsb' 19 5).toNat
      let disp : BitVec 64 := target - pc
      let rt := Reg.fromZRBits (w.extractLsb' 0 5)
      some (.tbz sf (w.getLsbD 24) rt bitPos disp)) = some inst)
    (hrange : TstBr14InRange P target) :
    prog.fetch pc = some inst := by
  rw [List.getElem?_eq_some_iff] at h_get
  rcases h_get with ⟨hi, h_eq⟩
  rw [h_pc, Program.fetch_of_hasWords h i hi, h_eq,
      decode_tstbr14Word (beq_iff_eq.mp hw) hrange]
  dsimp only
  rw [h_P]
  exact h_inst

/-! ## Linker Veneers -/

/-- Standard 3-instruction AArch64 ADRP range-extension veneer (`__AArch64ADRPThunk_<sym>`)
    at address `vAddr` jumping to `target` via intra-procedure-call scratch register `x16`. -/
def VeneerAt (prog : Program) (vAddr target : BitVec 64) : Prop :=
  AdrpInRange vAddr target ∧
  prog.hasWords vAddr
    [ adrpWord 0x90000010#32 vAddr target
    , lo12Word 0 0x91000210#32 target
    , 0xd61f0200#32 ]

theorem fetch_veneer_0 {prog : Program} {vAddr target : BitVec 64}
    (h : VeneerAt prog vAddr target) :
    prog.fetch vAddr =
      some (.adr true .x16 (pageOf target - pageOf vAddr)) :=
  fetch_of_hasWords_adrpAt 0 h.2 (BitVec.add_zero vAddr).symm rfl rfl rfl rfl h.1

theorem fetch_veneer_1 {prog : Program} {vAddr target : BitVec 64}
    (h : VeneerAt prog vAddr target) :
    prog.fetch (vAddr + 4#64) =
      some (.addSubImm .W64 .ADD .x16 .x16 ((lo12Of target).truncate 12) false) :=
  fetch_of_hasWords_addLo12At 1 h.2 rfl rfl rfl rfl rfl

theorem fetch_veneer_2 {prog : Program} {vAddr target : BitVec 64}
    (h : VeneerAt prog vAddr target) :
    prog.fetch (vAddr + 8#64) = some (.br .x16) :=
  Program.fetch_of_hasWords_decodeAt 2 h.2 rfl rfl

end RelocFetchRules

/-- Executing a 3-instruction AArch64 veneer at `vAddr` reaches `target` in 3 steps, modifying
    only `X16` (to `target`) and `pc` (to `target`). -/
theorem reaches_pc_of_veneerAt {prog : Program} {vAddr target : BitVec 64} {s0 : State}
    (h : VeneerAt prog vAddr target)
    (hpc : s0.pc = vAddr) (hrun : s0.status = .Running) :
    reaches_pc prog target s0
      (fun sm => sm = (s0.writeReg64 (.gpr 16#5) target).setPC target) := by
  have hs1 : execInst (.adr true .x16 (pageOf target - pageOf vAddr)) s0 =
      (s0.writeReg64 (.gpr 16#5) (pageOf target)).setPC (vAddr + 4#64) := by
    cases s0
    subst hpc
    dsimp [execInst, execInstWithSvc, Reg.x16, State.writeReg, State.writeReg64,
      State.advancePC, State.setPC]
    rw [adrp_pageOf_cancel]
  have hs2 : execInst (.addSubImm .W64 .ADD .x16 .x16 ((lo12Of target).truncate 12) false)
      ((s0.writeReg64 (.gpr 16#5) (pageOf target)).setPC (vAddr + 4#64)) =
      (s0.writeReg64 (.gpr 16#5) target).setPC (vAddr + 8#64) := by
    have hawc (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
      simp only [AddWithCarry64, Bool.false_eq_true, ↓reduceIte]
      bv_bits
    cases s0
    dsimp [execInst, execInstWithSvc, execAddSubImm, Reg.x16, evalAddSub, State.readReg,
      State.readReg64, State.writeReg, State.writeReg64, State.advancePC, State.setPC,
      RegFile.read, RegFile.write]
    congr 1
    · congr 1
      funext i
      by_cases hi : i = 16#5 <;>
        simp [hi, hawc, zeroExtend_truncate_lo12Of, pageOf_add_lo12Of]
    · bv_lin
  have hs3 : execInst (.br .x16)
      ((s0.writeReg64 (.gpr 16#5) target).setPC (vAddr + 8#64)) =
      (s0.writeReg64 (.gpr 16#5) target).setPC target := by
    cases s0; rfl
  have hf0 : prog.fetch s0.pc =
      some (.adr true .x16 (pageOf target - pageOf vAddr)) := by
    rw [hpc]; exact fetch_veneer_0 h
  have hrun1 : ((s0.writeReg64 (.gpr 16#5) (pageOf target)).setPC (vAddr + 4#64)).status = .Running := by
    cases s0; exact hrun
  have hf1 : prog.fetch ((s0.writeReg64 (.gpr 16#5) (pageOf target)).setPC (vAddr + 4#64)).pc =
      some (.addSubImm .W64 .ADD .x16 .x16 ((lo12Of target).truncate 12) false) := by
    have hpc1 : ((s0.writeReg64 (.gpr 16#5) (pageOf target)).setPC (vAddr + 4#64)).pc = vAddr + 4#64 := by
      cases s0; rfl
    rw [hpc1]; exact fetch_veneer_1 h
  have hrun2 : ((s0.writeReg64 (.gpr 16#5) target).setPC (vAddr + 8#64)).status = .Running := by
    cases s0; exact hrun
  have hf2 : prog.fetch ((s0.writeReg64 (.gpr 16#5) target).setPC (vAddr + 8#64)).pc =
      some (.br .x16) := by
    have hpc2 : ((s0.writeReg64 (.gpr 16#5) target).setPC (vAddr + 8#64)).pc = vAddr + 8#64 := by
      cases s0; rfl
    rw [hpc2]; exact fetch_veneer_2 h
  have hrun3 : ((s0.writeReg64 (.gpr 16#5) target).setPC target).status = .Running := by
    cases s0; exact hrun
  have hpc3 : ((s0.writeReg64 (.gpr 16#5) target).setPC target).pc = target := by
    cases s0; rfl
  apply reaches_pc_step hrun hf0
  change reaches_pc prog target
    (execInst (.adr true .x16 (pageOf target - pageOf vAddr)) s0) _ _
  rw [hs1]
  apply reaches_pc_step hrun1 hf1
  change reaches_pc prog target
    (execInst (.addSubImm .W64 .ADD .x16 .x16 ((lo12Of target).truncate 12) false) _) _ _
  rw [hs2]
  apply reaches_pc_step hrun2 hf2
  change reaches_pc prog target (execInst (.br .x16) _) _ _
  rw [hs3]
  exact reaches_pc_refl hpc3 hrun3 rfl

/-- Any `subroutine_ok` contract at `target` whose precondition and postconditions do not depend on
    `X16` or entry `pc` transfers across a range-extension veneer `VeneerAt prog vAddr target`. -/
theorem subroutine_ok_of_veneerAt {α : Type} {prog : Program} {vAddr target : BitVec 64}
    {spec : Spec α} (h : VeneerAt prog vAddr target)
    (hok : subroutine_ok prog target spec)
    (hpre : ∀ x s, spec.pre x ((s.writeReg64 (.gpr 16#5) target).setPC target) = spec.pre x s)
    (hpost : ∀ x s sf, spec.post x ((s.writeReg64 (.gpr 16#5) target).setPC target) sf = spec.post x s sf)
    (hpanic : ∀ x s sf, spec.onPanic x ((s.writeReg64 (.gpr 16#5) target).setPC target) sf = spec.onPanic x s sf)
    (hexit : ∀ x c s sf, spec.onExit x c ((s.writeReg64 (.gpr 16#5) target).setPC target) sf = spec.onExit x c s sf)
    (hoom_eq : ∀ x s sf, spec.onOom x ((s.writeReg64 (.gpr 16#5) target).setPC target) sf = spec.onOom x s sf := by
      intros; rfl) :
    subroutine_ok prog vAddr spec := by
  refine subroutine_ok_iff.mpr fun x R s0 hpc hrun hsat hsp => reaches_outcome_iff.mpr fun hcode => ?_
  let sm : State := (s0.writeReg64 (.gpr 16#5) target).setPC target
  have hreach := reaches_pc_of_veneerAt h hpc hrun hcode
  rcases hreach with ⟨s1, hsteps1, ⟨_, _, rfl⟩ | ⟨_, hoom⟩⟩
  · have hmem : sm.mem = s0.mem := by cases s0; rfl
    have hsp' : sm.sp = s0.sp := by cases s0; rfl
    have hspAl : sm.spAligned = s0.spAligned := by cases s0; rfl
    have hrun' : sm.status = .Running := by cases s0; exact hrun
    have hsat' : sm.mem ⊨ spec.pre x sm ∗ R := by rw [hmem, hpre]; exact hsat
    obtain ⟨sf, hsteps2, hout⟩ :=
      reaches_outcome_iff.mp (subroutine_ok_iff.mp hok x R sm rfl hrun' hsat' (hspAl.trans hsp)) (hmem ▸ hcode)
    refine ⟨sf, hsteps1.trans hsteps2, ?_⟩
    unfold SubroutineOutcome Returned CallingConventionPreserved CalleeSavedPreserved at hout ⊢
    have hlr : sm.readReg64 Reg.lr = s0.readReg64 Reg.lr := by cases s0; rfl
    have h19 : sm.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := by cases s0; rfl
    have h20 : sm.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := by cases s0; rfl
    have h21 : sm.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) := by cases s0; rfl
    have h22 : sm.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) := by cases s0; rfl
    have h23 : sm.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) := by cases s0; rfl
    have h24 : sm.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) := by cases s0; rfl
    have h25 : sm.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) := by cases s0; rfl
    have h26 : sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) := by cases s0; rfl
    have h27 : sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) := by cases s0; rfl
    have h28 : sm.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) := by cases s0; rfl
    have hfp : sm.readReg64 Reg.fp = s0.readReg64 Reg.fp := by cases s0; rfl
    have hvregs : calleeSavedVRegs sm = calleeSavedVRegs s0 := by cases s0; rfl
    have hpost' : spec.post x sm sf = spec.post x s0 sf := hpost x s0 sf
    have hpanic' : spec.onPanic x sm sf = spec.onPanic x s0 sf := hpanic x s0 sf
    have hexit' : ∀ c, spec.onExit x c sm sf = spec.onExit x c s0 sf := fun c => hexit x c s0 sf
    have hoom' : spec.onOom x sm sf = spec.onOom x s0 sf := hoom_eq x s0 sf
    simp only [hlr, hsp', h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hvregs,
      hpost', hpanic', hexit', hoom'] at hout
    exact hout
  · exact False.elim hoom

/-! ## Code and Data Relocation Linking -/

@[simp, arm64_norm, wp_norm]
theorem addSignedAddr_zero (symAddr : BitVec 64) :
    addSignedAddr symAddr 0 = symAddr := rfl

theorem CodeRelocInRange.of_find?_eq_some {relocs : List RelocEntry} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : ∀ r ∈ relocs,
      CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off) (addSignedAddr (resolve r.sym) r.addend))
    (off : Nat) {r : RelocEntry}
    (hfind : relocs.find? (·.off == off) = some r) :
    CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off) (addSignedAddr (resolve r.sym) r.addend) :=
  hrange r (List.mem_of_find?_eq_some hfind)

theorem BranchInRange.of_find?_eq_some {calls : List (Nat × String)} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : ∀ r ∈ calls, BranchInRange (a + BitVec.ofNat 64 r.1) (resolve r.2))
    (off : Nat) {r : Nat × String}
    (hfind : calls.find? (·.1 == off) = some r) :
    BranchInRange (a + BitVec.ofNat 64 r.1) (resolve r.2) :=
  hrange r (List.mem_of_find?_eq_some hfind)

/-- Patch a list of 32-bit template words `words` at base address `a` according to `relocs`,
    using `resolve` to map each symbol name to its 64-bit runtime address. -/
def patchRelocs (relocs : List RelocEntry) (words : List (BitVec 32)) (a : BitVec 64)
    (resolve : String → BitVec 64) : List (BitVec 32) :=
  words.zipIdx.map fun (w, j) =>
    match relocs.find? (·.off == 4 * j) with
    | some r =>
      let place := a + BitVec.ofNat 64 (4 * j)
      let target := addSignedAddr (resolve r.sym) r.addend
      patchRelocWord r.kind w place target
    | none => w

/-- What `li.honours o` establishes for a relocated function `fn ∈ o.relocFns`. -/
theorem LinkedImage.honours_relocFn {li : LinkedImage} {o : ObjectInfo}
    (h : li.honours o = true) {fn : SymCodeInfo} (hfn : fn ∈ o.relocFns) :
    ∃ syms off, lookup o.name li.objSymbols = some syms ∧
      lookupUnique fn.sym syms = some off ∧
      lookup fn.sym li.symbols = some off ∧
      off % 4 = 0 ∧ fn.code.length % 4 = 0 ∧ off + fn.code.length ≤ li.code.length ∧
      (∀ r ∈ fn.relocs, ∃ t, li.resolveRelocTarget o.name r = some t ∧
        codeRelocInRange r.kind (off + r.off) t = true) ∧
      (∀ j < fn.code.length / 4,
        (li.code.drop (off + 4 * j)).take 4 =
          let w := wordOfBytesLE fn.code (4 * j)
          match fn.relocs.find? (·.off == 4 * j) with
          | some r =>
            let t := (li.resolveRelocTarget o.name r).getD 0
            bytesOfWordLE (patchCodeRelocWord r.kind w (off + 4 * j) t)
          | none => (fn.code.drop (4 * j)).take 4) ∧
      ∀ s ∈ li.stubs, ¬(off ≤ s.2 ∧ s.2 < off + fn.code.length) := by
  unfold LinkedImage.honours at h
  split at h
  · contradiction
  rename_i syms hsyms
  simp only [Bool.and_eq_true] at h
  have hf := List.all_eq_true.1 h.1.2 fn hfn
  split at hf
  · contradiction
  rename_i off hoff
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hf
  obtain ⟨⟨⟨⟨⟨⟨hsym, hal⟩, hbmod⟩, hlen⟩, hrels⟩, hwords⟩, hstubs⟩ := hf
  refine ⟨syms, off, hsyms, hoff, hsym, hal, hbmod, hlen, ?_, hwords, ?_⟩
  · intro r hr
    have hc := hrels r hr
    split at hc
    · rename_i t ht
      exact ⟨t, ht, hc⟩
    · contradiction
  · intro s hs
    have := hstubs s hs
    simp at this
    omega

/-- What `li.honours o` establishes for a data symbol `d ∈ o.dataSyms`. -/
theorem LinkedImage.honours_dataSym {li : LinkedImage} {o : ObjectInfo}
    (h : li.honours o = true) {d : SymDataInfo} (hd : d ∈ o.dataSyms) :
    ∃ syms off, lookup o.name li.objSymbols = some syms ∧
      lookupUnique d.sym syms = some off ∧
      lookup d.sym li.symbols = some off ∧
      0 < d.align ∧ off % d.align = 0 ∧
      li.dataOff ≤ off ∧
      (d.bytes.length = 0 ∨ (off - li.dataOff) + d.bytes.length ≤ li.data.length) ∧
      (off - li.dataOff) + (d.bytes.length + d.zeroTail) ≤ li.data.length + li.bss := by
  unfold LinkedImage.honours at h
  split at h
  · contradiction
  rename_i syms hsyms
  simp only [Bool.and_eq_true] at h
  have hdf := List.all_eq_true.1 h.2 d hd
  split at hdf
  · contradiction
  rename_i off hoff
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hdf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsym, hal_pos⟩, hal⟩, hdo⟩, hblen⟩, htot⟩, _⟩, _⟩, _⟩, _⟩ := hdf
  exact ⟨syms, off, hsyms, hoff, hsym, hal_pos, hal, hdo, hblen, htot⟩

theorem lo12Aligned_to_prop {scale : Nat} (hscale : scale ≤ 4) {base : BitVec 64} {t : Nat}
    (hb : base &&& 0xfff#64 = 0#64) (h : lo12Aligned scale t = true) :
    Lo12Aligned scale (base + BitVec.ofNat 64 t) := by
  unfold lo12Aligned at h
  rw [beq_iff_eq] at h
  unfold Lo12Aligned
  have hmask : (base + BitVec.ofNat 64 t) &&& lo12AlignMask scale =
      BitVec.ofNat 64 t &&& lo12AlignMask scale := by
    match scale with
    | 0 => dsimp only [lo12AlignMask]; bv_bits
    | 1 => dsimp only [lo12AlignMask]; bv_bits
    | 2 => dsimp only [lo12AlignMask]; bv_bits
    | 3 => dsimp only [lo12AlignMask]; bv_bits
    | 4 => dsimp only [lo12AlignMask]; bv_bits
    | n + 5 => omega
  rw [hmask, h]

theorem adrpInRange_to_prop {base : BitVec 64} {off roff t : Nat}
    (hb : base &&& 0xfff#64 = 0#64) (h : adrpInRange (off + roff) t = true) :
    AdrpInRange (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff) (base + BitVec.ofNat 64 t) := by
  unfold adrpInRange at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold AdrpInRange
  rw [pageOf_diff_base_add3 hb]
  exact h

theorem imm19InRange_to_prop {base : BitVec 64} {off roff t : Nat}
    (h : imm19InRange (off + roff) t = true) :
    Imm19InRange (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff) (base + BitVec.ofNat 64 t) := by
  unfold imm19InRange at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold Imm19InRange
  rw [disp_sub_eq]
  exact ⟨h1, h2, h3⟩

theorem tstbr14InRange_to_prop {base : BitVec 64} {off roff t : Nat}
    (h : tstbr14InRange (off + roff) t = true) :
    TstBr14InRange (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff) (base + BitVec.ofNat 64 t) := by
  unfold tstbr14InRange at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold TstBr14InRange
  rw [disp_sub_eq]
  exact ⟨h1, h2, h3⟩

theorem adrInRange_to_prop {base : BitVec 64} {off roff t : Nat}
    (h : adrInRange (off + roff) t = true) :
    AdrInRange (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff) (base + BitVec.ofNat 64 t) := by
  unfold adrInRange at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold AdrInRange
  rw [disp_sub_eq]
  exact h

theorem prel32InRange_to_prop {base : BitVec 64} {off roff t : Nat}
    (h : prel32InRange (off + roff) t = true) :
    Prel32InRange (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff) (base + BitVec.ofNat 64 t) := by
  unfold prel32InRange at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold Prel32InRange
  rw [disp_sub_eq]
  exact h

theorem codeRelocInRange_to_prop {kind : RelocKind} {base : BitVec 64} {off roff t : Nat}
    (hb : base &&& 0xfff#64 = 0#64) (h : codeRelocInRange kind (off + roff) t = true) :
    CodeRelocInRange kind (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff)
      (base + BitVec.ofNat 64 t) := by
  cases kind with
  | call26 | jump26 => exact branchInRange_to_prop h
  | adrpHi21 | adrGotPage | tlsieAdrGottprelPage21 => exact adrpInRange_to_prop hb h
  | adrpHi21Nc | addLo12 | ldst8Lo12 => trivial
  | ldst16Lo12 => exact lo12Aligned_to_prop (by omega) hb h
  | ldst32Lo12 => exact lo12Aligned_to_prop (by omega) hb h
  | ldst64Lo12 | ld64GotLo12Nc | tlsieLd64GottprelLo12Nc => exact lo12Aligned_to_prop (by omega) hb h
  | ldst128Lo12 => exact lo12Aligned_to_prop (by omega) hb h
  | condbr19 | ldPrelLo19 => exact imm19InRange_to_prop h
  | tstbr14 => exact tstbr14InRange_to_prop h
  | adrPrelLo21 => exact adrInRange_to_prop h
  | prel32 => exact prel32InRange_to_prop h
  | abs64 | abs32 => contradiction
  | _ => contradiction

theorem patchRelocWord_base_add {kind : RelocKind} {w : BitVec 32}
    {base : BitVec 64} {off roff t : Nat} (hb : base &&& 0xfff#64 = 0#64)
    (hcr : codeRelocInRange kind (off + roff) t = true) :
    patchRelocWord kind w (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff)
      (base + BitVec.ofNat 64 t) =
    patchCodeRelocWord kind w (off + roff) t := by
  have hlo : (base + BitVec.ofNat 64 t) &&& 0xfff#64 = BitVec.ofNat 64 t &&& 0xfff#64 :=
    lo12Of_base_add hb
  cases kind with
  | call26 | jump26 =>
    simp only [patchRelocWord, patchCodeRelocWord, branchWord, disp_sub_eq]
  | adrpHi21 | adrpHi21Nc | adrGotPage | tlsieAdrGottprelPage21 =>
    simp only [patchRelocWord, patchCodeRelocWord, adrpWord, pageOf_diff_base_add3 hb]
  | addLo12 | ldst8Lo12 | ldst16Lo12 | ldst32Lo12 | ldst64Lo12 | ldst128Lo12
  | ld64GotLo12Nc | tlsieLd64GottprelLo12Nc =>
    simp only [patchRelocWord, patchCodeRelocWord, lo12Word, hlo]
  | condbr19 | ldPrelLo19 =>
    simp only [patchRelocWord, patchCodeRelocWord, imm19Word, disp_sub_eq]
  | tstbr14 =>
    simp only [patchRelocWord, patchCodeRelocWord, tstbr14Word, disp_sub_eq]
  | adrPrelLo21 =>
    simp only [patchRelocWord, patchCodeRelocWord, adrWord, disp_sub_eq]
  | prel32 =>
    simp only [patchRelocWord, patchCodeRelocWord, disp_sub_eq]
  | abs64 | abs32 => rfl
  | _ => contradiction

theorem LinkedImage.resolveObjSym_eq_false {li : LinkedImage} {objName sym : String}
    {localOnly : Bool} {off : Nat}
    (h : li.resolveObjSym objName sym localOnly = some off) :
    li.resolveObjSym objName sym false = some off := by
  unfold LinkedImage.resolveObjSym at h ⊢
  cases localOnly
  · exact h
  · simp only [↓reduceIte] at h ⊢
    rw [h]
    rfl

theorem addSignedAddr_eq_of_addSignedOff (base : BitVec 64) {symOff t : Nat} {addend : Int}
    (h : addSignedOff symOff addend = some t) :
    addSignedAddr (base + BitVec.ofNat 64 symOff) addend = base + BitVec.ofNat 64 t := by
  unfold addSignedOff at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  split at h <;> try contradiction
  rename_i ht
  injection h with ht_eq
  subst ht_eq
  unfold addSignedAddr
  split
  · rename_i h0
    rw [beq_iff_eq] at h0
    subst h0
    simp
  · have h1 : BitVec.ofInt 64 addend =
        BitVec.ofInt 64 ((symOff : Int) + addend) - BitVec.ofNat 64 symOff := by
      rw [← BitVec.ofInt_natCast, BitVec.ofInt_add]
      bv_lin
    have h2 : BitVec.ofInt 64 ((symOff : Int) + addend) =
        BitVec.ofNat 64 ((symOff : Int) + addend).toNat := by
      rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg ht.1]
    rw [h1, h2]
    bv_lin

theorem getD_eq_drop_getD (bs : List (BitVec 8)) (k i : Nat) :
    bs.getD (k + i) 0#8 = (bs.drop k).getD i 0#8 := by
  simp [List.getD, List.getElem?_drop]

theorem wordOfBytesLE_eq_of_readWordOff {bs : List (BitVec 8)} {k : Nat} {w : BitVec 32}
    (h : ({ code := bs } : Program).readWordOff k = some w) :
    wordOfBytesLE bs k = w := by
  unfold Program.readWordOff at h
  split at h <;> try contradiction
  unfold wordOfBytesLE
  rw [show bs.getD k 0#8 = (bs.drop k).getD 0 0#8 by simp [List.getD],
    getD_eq_drop_getD bs k 1, getD_eq_drop_getD bs k 2, getD_eq_drop_getD bs k 3]
  rcases hbs : bs.drop k with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _⟩⟩⟩⟩ <;>
    simp only [hbs, List.getD, Option.some.injEq, reduceCtorEq] at h ⊢
  subst h
  bv_robdd

theorem readWordOff_of_take4_bytesOfWordLE {prog : Program} {k : Nat} {v : BitVec 32}
    (hk : k % 4 = 0) (htake : (prog.code.drop k).take 4 = bytesOfWordLE v) :
    prog.readWordOff k = some v := by
  simp only [Program.readWordOff, hk, ne_eq, not_true_eq_false, ↓reduceIte]
  rcases hprog : prog.code.drop k with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _⟩⟩⟩⟩ <;>
    simp [hprog, bytesOfWordLE, bytesLE, List.range_succ, List.range_zero] at htake
  obtain ⟨rfl, rfl, rfl, rfl⟩ := htake
  simp only [Option.some.injEq]
  bv_bits

theorem base_aligned_and_fff {b : BitVec 64} (h : b.toNat % pageSize = 0) :
    b &&& 0xfff#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xfff#64).toNat = 2 ^ 12 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact h

theorem LinkedImage.resolveRelocTarget_eq_some {li : LinkedImage} {objName : String}
    {r : RelocEntry} {t : Nat}
    (h : li.resolveRelocTarget objName r = some t) :
    ∃ symOff, li.resolveObjSym objName r.sym false = some symOff ∧
      addSignedOff symOff r.addend = some t := by
  unfold LinkedImage.resolveRelocTarget at h
  cases hs : li.resolveObjSym objName r.sym r.localSym with
  | none => simp [hs] at h
  | some symOff =>
    rw [hs] at h
    exact ⟨symOff, LinkedImage.resolveObjSym_eq_false hs, h⟩

theorem LinkedImage.resolveObjSym_of_lookupUnique {li : LinkedImage} {objName sym : String}
    {syms : List (String × Nat)} {off : Nat}
    (hsyms : lookup objName li.objSymbols = some syms)
    (hoff : lookupUnique sym syms = some off) :
    li.resolveObjSym objName sym false = some off := by
  simp [LinkedImage.resolveObjSym, hsyms, hoff]

theorem drop_take_eq_of_getD {xs ys : List (BitVec 8)} {relOff : Nat}
    (hlen : relOff + ys.length ≤ xs.length)
    (hget : ∀ i < ys.length, xs.getD (relOff + i) 0#8 = ys.getD i 0#8) :
    (xs.drop relOff).take ys.length = ys := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro i h1 h2
    rw [List.getElem_take, List.getElem_drop]
    have hi := hget i h2
    have hx : xs.getD (relOff + i) 0#8 = xs[relOff + i]'(by omega) := by
      rw [List.getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hy : ys.getD i 0#8 = ys[i] := by
      rw [List.getD, List.getElem?_eq_getElem h2, Option.getD_some]
    exact hx.symm.trans (hi.trans hy)

/-- For a read-only relocation-free data symbol `d ∈ o.dataSyms`, `li.honours o = true` and
    `Obj.Loads li img` and `img.FrozenLoaded s` yield
    `Obj.HoldsBytes s.mem (img.base + off) d.bytes (fun _ => .ro)`. -/
theorem LinkedImage.loads_dataSym_ro_holdsBytes {li : LinkedImage} {o : ObjectInfo}
    {img : Image} {s : State} {d : SymDataInfo}
    (hhon : li.honours o = true) (hl : Loads li img) (hF : img.FrozenLoaded s)
    (hd : d ∈ o.dataSyms) (hro : d.readOnly = true) (hrel : d.relocs = []) :
    ∃ syms off, lookup o.name li.objSymbols = some syms ∧
      lookupUnique d.sym syms = some off ∧
      0 < d.align ∧ off % d.align = 0 ∧
      HoldsBytes s.mem (img.base + BitVec.ofNat 64 off) d.bytes (fun _ => .ro) := by
  unfold LinkedImage.honours at hhon
  split at hhon
  · contradiction
  rename_i syms hsyms
  simp only [Bool.and_eq_true] at hhon
  have hdf := List.all_eq_true.1 hhon.2 d hd
  split at hdf
  · contradiction
  rename_i off hoff
  simp only [hro, hrel, ↓reduceIte, List.all_nil, List.filterMap_nil, List.any_nil,
    Bool.false_eq_true] at hdf
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, List.filter_eq_nil_iff] at hdf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_hsym, hal_pos⟩, hal⟩, hdo⟩, hblen⟩, _htot⟩, hro_any⟩, _hrel_all⟩, hwin⟩, hbytes⟩ := hdf
  refine ⟨syms, off, hsyms, hoff, hal_pos, hal, ?_⟩
  rcases hblen with h0 | hle
  · intro j hj
    omega
  · obtain ⟨_, _, _, hwf, _, _⟩ := ProofLib.ObjectLoad.load_eq_ok hl
    simp only [LinkedImage.wellFormed, Bool.and_eq_true] at hwf
    have hrel_wf := List.all_eq_true.mp hwf.1.1.2
    have hno : ProofLib.ObjectLoad.noRelocInRange li.relocs (li.data.length + li.bss)
        (off - li.dataOff) d.bytes.length = true := by
      simp only [ProofLib.ObjectLoad.noRelocInRange, List.all_eq_true, decide_eq_true_eq]
      intro lr hlr
      have hw1 := hrel_wf lr hlr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw1
      have hw2 := hwin lr hlr
      have hw2' : off - li.dataOff < lr.off + lr.width →
          off - li.dataOff + (d.bytes.length + d.zeroTail) ≤ lr.off := by
        simpa using hw2
      omega
    have hinRo : ProofLib.ObjectLoad.inLiRoData li off d.bytes.length = true := by
      obtain ⟨⟨rOff, rLen⟩, hrmem, hr⟩ := List.any_eq_true.1 hro_any
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      simp only [ProofLib.ObjectLoad.inLiRoData, List.any_eq_true, decide_eq_true_eq]
      exact ⟨(rOff, rLen), hrmem, by omega, by omega, by omega⟩
    have hget : ∀ i < d.bytes.length,
        li.data.getD (off - li.dataOff + i) 0#8 = d.bytes.getD i 0#8 := by
      intro i hi
      have hbi := hbytes i (by omega)
      simp only [hi, ↓reduceIte, beq_iff_eq] at hbi
      exact hbi
    have hslice := drop_take_eq_of_getD hle hget
    exact ProofLib.ObjectLoad.loads_rodata_holdsBytes hl hF hdo hle hno hinRo rfl hslice

def Image.ResolvesObj (img : Image) (li : LinkedImage) (objName : String)
    (names : List String) (resolve : String → BitVec 64) : Prop :=
  Loads li img ∧
  ∀ n ∈ names, ∃ off, li.resolveObjSym objName n false = some off ∧
    resolve n = img.base + BitVec.ofNat 64 off

end Obj

def Obj.Image.RelocCtx (img : Obj.Image) (libs trusted : List LibrarySpec) (objName : String)
    (names : List String) (resolve : String → BitVec 64) : Prop :=
  ∃ li : Obj.LinkedImage,
    (∀ D ∈ libs, D.ObjectLoaded li ∨ (D ∈ trusted ∧ D.ProvidedAsExterns li)) ∧
    img.ResolvesObj li objName names resolve

/-- From `img.RelocCtx libs trusted o.name names resolve` and `img.FrozenLoaded s`, any read-only
    relocation-free data symbol `d ∈ o.dataSyms` whose name is in `names` holds `d.bytes` read-only
    at `resolve d.sym`. -/
theorem Obj.Image.RelocCtx.holdsBytes_dataSym_ro {libs trusted : List LibrarySpec}
    {img : Obj.Image} {D : LibrarySpec} {o : Obj.ObjectInfo} {names : List String}
    {resolve : String → BitVec 64} {s : State} {d : Obj.SymDataInfo}
    (hctx : img.RelocCtx libs trusted o.name names resolve)
    (hF : img.FrozenLoaded s) (hD : D ∈ libs) (hDT : D ∉ trusted) (ho : D.obj = some o)
    (hd : d ∈ o.dataSyms) (hmem : d.sym ∈ names)
    (hro : d.readOnly = true) (hrel : d.relocs = []) :
    Obj.HoldsBytes s.mem (resolve d.sym) d.bytes (fun _ => .ro) := by
  obtain ⟨li, hobjs, hl, hres⟩ := hctx
  have ho_mem : o ∈ li.objects := LinksIn.objectLoaded hobjs hD hDT ho
  obtain ⟨_, _, _, hwf, _, _⟩ := ProofLib.ObjectLoad.load_eq_ok hl
  have hhon := Obj.LinkedImage.wellFormed_objects hwf o ho_mem
  obtain ⟨syms, off, hsyms, hoff, _, _, hbytes⟩ :=
    Obj.LinkedImage.loads_dataSym_ro_holdsBytes hhon hl hF hd hro hrel
  have hres_d := Obj.LinkedImage.resolveObjSym_of_lookupUnique hsyms hoff
  obtain ⟨off', hoff', hres_eq⟩ := hres d.sym hmem
  rw [hres_d] at hoff'
  injection hoff' with hoff_eq
  subst hoff_eq
  rw [hres_eq]
  exact hbytes

theorem Obj.Image.RelocCtx.symtab_self_of_dataSym {libs trusted : List LibrarySpec}
    {img : Obj.Image} {D : LibrarySpec} {o : Obj.ObjectInfo} {names : List String}
    {resolve : String → BitVec 64} {d : Obj.SymDataInfo}
    (hctx : img.RelocCtx libs trusted o.name names resolve)
    (hD : D ∈ libs) (hDT : D ∉ trusted) (ho : D.obj = some o)
    (hd : d ∈ o.dataSyms) (hmem : d.sym ∈ names) :
    img.symtab o.name d.sym = some (resolve d.sym) := by
  obtain ⟨li, hobjs, hl, hres⟩ := hctx
  have ho_mem : o ∈ li.objects := LinksIn.objectLoaded hobjs hD hDT ho
  obtain ⟨_, _, _, hwf, _, _⟩ := ProofLib.ObjectLoad.load_eq_ok hl
  obtain ⟨_, _, _, _, hobjSyms, _, _⟩ := ProofLib.ObjectLoad.load_ok hl
  have hhon := Obj.LinkedImage.wellFormed_objects hwf o ho_mem
  obtain ⟨syms, off, hsyms, hoff, _⟩ := Obj.LinkedImage.honours_dataSym hhon hd
  have hres_d := Obj.LinkedImage.resolveObjSym_of_lookupUnique hsyms hoff
  obtain ⟨off', hoff', hres_eq⟩ := hres d.sym hmem
  rw [hres_d] at hoff'
  injection hoff' with hoff_eq
  subst hoff_eq
  simp [Obj.Image.symtab, hobjSyms, hsyms, hoff, hres_eq]

theorem Obj.Image.RelocCtx.sym_self_of_dataSym {libs trusted : List LibrarySpec}
    {img : Obj.Image} {D : LibrarySpec} {o : Obj.ObjectInfo} {names : List String}
    {resolve : String → BitVec 64} {s : State} {d : Obj.SymDataInfo}
    (hctx : img.RelocCtx libs trusted o.name names resolve)
    (hsym : s.symtab = img.symtab)
    (hD : D ∈ libs) (hDT : D ∉ trusted) (ho : D.obj = some o)
    (hd : d ∈ o.dataSyms) (hmem : d.sym ∈ names) :
    s.sym o.name d.sym = resolve d.sym := by
  simp [State.sym, hsym, hctx.symtab_self_of_dataSym hD hDT ho hd hmem]

/-- Opcode/register bitmask preserved by `patchCodeRelocWord` and `patchRelocWord` for relocation
    `kind`. Two template words `w'` and `w` agreeing on `relocOpcodeMask kind` produce identical
    patched instruction words for any `(place, target)`. -/
def Obj.relocOpcodeMask : Obj.RelocKind → BitVec 32
  | .call26 | .jump26 => 0xfc000000#32
  | .adrpHi21 | .adrpHi21Nc | .adrPrelLo21
  | .adrGotPage | .tlsieAdrGottprelPage21 => 0x9f00001f#32
  | .addLo12 | .ldst8Lo12 | .ldst16Lo12 | .ldst32Lo12 | .ldst64Lo12 | .ldst128Lo12
  | .ld64GotLo12Nc | .tlsieLd64GottprelLo12Nc
  | .tlsleAddTprelHi12 | .tlsleAddTprelLo12 | .tlsleAddTprelLo12Nc
  | .tlsleLdst8TprelLo12Nc | .tlsleLdst16TprelLo12Nc | .tlsleLdst32TprelLo12Nc
  | .tlsleLdst64TprelLo12Nc | .tlsleLdst128TprelLo12Nc => 0xffc003ff#32
  | .condbr19 | .ldPrelLo19 => 0xff00001f#32
  | .tstbr14 => 0xfff8001f#32
  | .prel32 | .tlsdescAdrPage21 | .tlsdescLd64Lo12 | .tlsdescAddLo12 | .tlsdescCall => 0#32
  | .tlsleMovwTprelG1 | .tlsleMovwTprelG0 => 0xbfe0001f#32
  | .tlsleMovwTprelG1Nc | .tlsleMovwTprelG0Nc => 0xffe0001f#32
  | .abs64 | .abs32 => 0xffffffff#32

theorem Obj.patchCodeRelocWord_eq_of_mask {kind : Obj.RelocKind} {w' w : BitVec 32}
    {placeOff targetOff : Nat}
    (hm : w' &&& Obj.relocOpcodeMask kind = w &&& Obj.relocOpcodeMask kind) :
    Obj.patchCodeRelocWord kind w' placeOff targetOff =
      Obj.patchCodeRelocWord kind w placeOff targetOff := by
  cases kind <;>
    simp only [Obj.relocOpcodeMask, Obj.patchCodeRelocWord, Obj.branchWord,
      Obj.adrpWord, Obj.adrpWordOff, Obj.adrWord, Obj.adrWordOff,
      Obj.lo12Word, Obj.imm19Word, Obj.imm19WordOff, Obj.tstbr14Word, Obj.tstbr14WordOff] at hm ⊢ <;>
    first | rfl | rw [hm] | bv_bits

open ProofLib.ProgramReflection

/-- Pack four little-endian bytes into a `Nat < 2 ^ 32` using primitive shift and bitwise-or
    operations. -/
def packRelocWordNat (b0 b1 b2 b3 : BitVec 8) : Nat :=
  Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft
    (Nat.lor (Nat.shiftLeft b3.toNat 8) b2.toNat) 8) b1.toNat) 8) b0.toNat

private theorem packRelocWordNat_eq_toNat (b0 b1 b2 b3 : BitVec 8) :
    packRelocWordNat b0 b1 b2 b3 = (b3 ++ b2 ++ b1 ++ b0 : BitVec 32).toNat := by
  simp only [packRelocWordNat, BitVec.toNat_append]
  rfl

/-- Single-pass linear-time scanner over `(code, words, relocs)` starting at byte offset `off`.
    Consumes four bytes and one word per step, checking byte length `4 * words.length` and
    strictly ascending, 4-byte-aligned, in-bounds relocation offsets. -/
def checkRelocWordsStream :
    List (BitVec 8) → List (BitVec 32) → List Obj.RelocEntry → Nat → Bool
  | [], [], [], _ => true
  | b0 :: b1 :: b2 :: b3 :: rest, w :: ws, [], off =>
    Nat.beq (packRelocWordNat b0 b1 b2 b3) w.toNat &&
    checkRelocWordsStream rest ws [] (off + 4)
  | b0 :: b1 :: b2 :: b3 :: rest, w :: ws, rs@(r :: rs'), off =>
    let w' := packRelocWordNat b0 b1 b2 b3
    if Nat.beq r.off off then
      let m := (Obj.relocOpcodeMask r.kind).toNat
      Nat.beq (Nat.land w' m) (Nat.land w.toNat m) &&
      checkRelocWordsStream rest ws rs' (off + 4)
    else
      Nat.blt off r.off &&
      Nat.beq w' w.toNat &&
      checkRelocWordsStream rest ws rs (off + 4)
  | _, _, _, _ => false

theorem checkRelocWordsStream_spec {code : List (BitVec 8)} {words : List (BitVec 32)}
    {relocs : List Obj.RelocEntry} {off : Nat}
    (h : checkRelocWordsStream code words relocs off = true) :
    4 * words.length = code.length ∧
    (∀ r ∈ relocs, off ≤ r.off) ∧
    (∀ j (hj : j < words.length),
      ∃ w' : BitVec 32,
        ({ code := code } : Program).readWordOff (4 * j) = some w' ∧
        match relocs.find? (·.off == off + 4 * j) with
        | some r =>
          (w' &&& Obj.relocOpcodeMask r.kind) = (words[j] &&& Obj.relocOpcodeMask r.kind)
        | none => w' = words[j]) := by
  induction words generalizing code relocs off with
  | nil =>
    cases code with
    | nil =>
      cases relocs with
      | nil =>
        exact ⟨rfl, fun _ h => absurd h (List.not_mem_nil), fun _ h => absurd h (Nat.not_lt_zero _)⟩
      | cons _ _ => simp [checkRelocWordsStream] at h
    | cons _ _ => simp [checkRelocWordsStream] at h
  | cons w ws ih =>
    match code with
    | [] | [_] | [_, _] | [_, _, _] => simp [checkRelocWordsStream] at h
    | b0 :: b1 :: b2 :: b3 :: rest =>
      have hread_succ (k : Nat) :
          ({ code := b0 :: b1 :: b2 :: b3 :: rest } : Program).readWordOff (4 * (k + 1)) =
            ({ code := rest } : Program).readWordOff (4 * k) := by
        have hk : 4 * (k + 1) = 4 + 4 * k := by omega
        simp [Program.readWordOff, hk, ← List.drop_drop]
      cases relocs with
      | nil =>
        simp only [checkRelocWordsStream, Bool.and_eq_true, Nat.beq_eq] at h
        obtain ⟨hw, hrest⟩ := h
        obtain ⟨hlen, _, hj_ih⟩ := ih hrest
        refine ⟨by simp only [List.length_cons]; omega, fun _ hm => absurd hm (List.not_mem_nil), ?_⟩
        intro j hj
        cases j with
        | zero =>
          refine ⟨b3 ++ b2 ++ b1 ++ b0, rfl, BitVec.eq_of_toNat_eq ?_⟩
          rwa [← packRelocWordNat_eq_toNat]
        | succ k =>
          have hk : k < ws.length := by simp at hj; omega
          obtain ⟨w', hrw, hmw⟩ := hj_ih k hk
          exact ⟨w', (hread_succ k).trans hrw, by simpa using hmw⟩
      | cons r rs' =>
        simp only [checkRelocWordsStream] at h
        cases hoff : Nat.beq r.off off with
        | true =>
          simp only [hoff, ↓reduceIte, Bool.and_eq_true, Nat.beq_eq] at h
          have hroff : r.off = off := Nat.eq_of_beq_eq_true hoff
          obtain ⟨hmask, hrest⟩ := h
          obtain ⟨hlen, hge, hj_ih⟩ := ih hrest
          refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
          · intro r' hr'
            rcases List.mem_cons.mp hr' with rfl | hr'
            · omega
            · have := hge r' hr'; omega
          · intro j hj
            cases j with
            | zero =>
              refine ⟨b3 ++ b2 ++ b1 ++ b0, rfl, ?_⟩
              have hbeq0 : (r.off == off + 4 * 0) = true := by simp [hroff]
              simp only [List.find?_cons, hbeq0]
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_and, ← packRelocWordNat_eq_toNat]
              exact hmask
            | succ k =>
              have hk : k < ws.length := by simp at hj; omega
              obtain ⟨w', hrw, hmw⟩ := hj_ih k hk
              refine ⟨w', (hread_succ k).trans hrw, ?_⟩
              have hadd : off + 4 * (k + 1) = off + 4 + 4 * k := by omega
              have hne : (r.off == off + 4 + 4 * k) = false :=
                beq_false_of_ne (by omega)
              rw [hadd]
              simp only [List.find?_cons, hne]
              exact hmw
        | false =>
          simp only [hoff, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
            Nat.blt_eq, Nat.beq_eq] at h
          obtain ⟨⟨_hlt, hw⟩, hrest⟩ := h
          obtain ⟨hlen, hge, hj_ih⟩ := ih hrest
          refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
          · intro r' hr'
            have := hge r' hr'; omega
          · intro j hj
            cases j with
            | zero =>
              refine ⟨b3 ++ b2 ++ b1 ++ b0, rfl, ?_⟩
              have hnone : ((r :: rs').find? fun x => x.off == off + 4 * 0) = none := by
                rw [List.find?_eq_none]
                intro x hx
                have := hge x hx
                simp only [beq_iff_eq]; omega
              rw [hnone]
              apply BitVec.eq_of_toNat_eq
              rwa [← packRelocWordNat_eq_toNat]
            | succ k =>
              have hk : k < ws.length := by simp at hj; omega
              obtain ⟨w', hrw, hmw⟩ := hj_ih k hk
              refine ⟨w', (hread_succ k).trans hrw, ?_⟩
              have hadd : off + 4 * (k + 1) = off + 4 + 4 * k := by omega
              rw [hadd]
              simpa using hmw

/-- Decidable single-pass check that `words` is non-empty and `code` decodes word-by-word to
    `words` (up to relocation immediate masks at the strictly sorted 4-byte-aligned offsets
    recorded in `relocs`). -/
def checkRelocCodeWords (code : List (BitVec 8)) (words : List (BitVec 32))
    (relocs : List Obj.RelocEntry) : Bool :=
  !words.isEmpty && checkRelocWordsStream code words relocs 0

/-- Decidable check that `o.relocFns` records `{ sym := symName, code := bs, relocs := relocs }`
    where `bs` decodes word-by-word to `words` (up to relocation immediate bits at relocated
    offsets). -/
def checkRelocFn (o : Obj.ObjectInfo) (symName : String) (relocs : List Obj.RelocEntry)
    (words : List (BitVec 32)) : Bool :=
  match o.relocFns.find? (·.sym == symName) with
  | some fn => (fn.relocs == relocs) && checkRelocCodeWords fn.code words relocs
  | none => false

/-- Decidable check that entry `idx` of `o.relocFns` has symbol `symName`, relocation table
    `relocs`, and bytes decoding word-by-word to `words` (up to relocation immediate bits).
    Avoids scanning symbols prior to `idx`. -/
def checkRelocFnAt (o : Obj.ObjectInfo) (idx : Nat) (symName : String)
    (relocs : List Obj.RelocEntry) (words : List (BitVec 32)) : Bool :=
  match o.relocFns[idx]? with
  | some fn =>
    (fn.sym == symName) &&
    (fn.relocs == relocs) &&
    checkRelocCodeWords fn.code words relocs
  | none => false

/-- Decidable check on only the code words of entry `idx` of `o.relocFns` against its own
    recorded `fn.relocs` (pair with a `rfl_kernel` check on `(fn.sym, fn.relocs)` to avoid
    comparing relocation symbol strings via `Bool` `BEq` inside `decide`). -/
def checkRelocWordsAt (o : Obj.ObjectInfo) (idx : Nat) (words : List (BitVec 32)) : Bool :=
  match o.relocFns[idx]? with
  | some fn => checkRelocCodeWords fn.code words fn.relocs
  | none => false

/-- Check that none of the first `idx` entries of `fns` has symbol `symName`. -/
def noRelocSymBefore : List Obj.SymCodeInfo → Nat → String → Bool
  | _, 0, _ => true
  | [], _ + 1, _ => false
  | fn :: rest, k + 1, symName => !(fn.sym == symName) && noRelocSymBefore rest k symName

private theorem find?_eq_getElem?_of_noRelocSymBefore :
    ∀ (fns : List Obj.SymCodeInfo) (idx : Nat) (symName : String) (fn : Obj.SymCodeInfo),
      noRelocSymBefore fns idx symName = true →
      fns[idx]? = some fn →
      fn.sym = symName →
      fns.find? (·.sym == symName) = some fn
  | [], 0, _, _, _, hget, _ => by simp at hget
  | [], _ + 1, _, _, hno, _, _ => by simp [noRelocSymBefore] at hno
  | f0 :: rest, 0, symName, fn, _, hget, hsym => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget hsym
    simp
  | f0 :: rest, k + 1, symName, fn, hno, hget, hsym => by
    simp only [noRelocSymBefore, Bool.and_eq_true, Bool.not_eq_true'] at hno
    simp only [List.getElem?_cons_succ] at hget
    simp only [List.find?_cons, hno.1]
    exact find?_eq_getElem?_of_noRelocSymBefore rest k symName fn hno.2 hget hsym

/-- Prove `checkRelocFn o symName relocs words = true` by pointing at the first matching entry
    `idx`, pairing `(fn.sym, fn.relocs)` equality with `noRelocSymBefore` and `checkRelocWordsAt`. -/
theorem checkRelocFn_of_firstAt {o : Obj.ObjectInfo} {idx : Nat}
    {symName : String} {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (hmeta : (o.relocFns[idx]?).map (fun f => (f.sym, f.relocs)) = some (symName, relocs))
    (hcheck : (noRelocSymBefore o.relocFns idx symName &&
      checkRelocWordsAt o idx words) = true) :
    checkRelocFn o symName relocs words = true := by
  simp only [Bool.and_eq_true] at hcheck
  unfold checkRelocWordsAt at hcheck
  cases hfn : o.relocFns[idx]? with
  | none => simp [hfn] at hmeta
  | some fn =>
    simp only [hfn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmeta hcheck
    rcases hmeta with ⟨hsym, hrel⟩
    have hfind := find?_eq_getElem?_of_noRelocSymBefore o.relocFns idx symName fn
      hcheck.1 hfn hsym
    unfold checkRelocFn
    simp only [hfind, Bool.and_eq_true, beq_iff_eq]
    exact ⟨hrel, hrel ▸ hcheck.2⟩

/-- Proposition witnessing that `o.relocFns` contains an entry matching `(symName, relocs)` whose
    bytes decode word-by-word to `words` up to relocation immediate masks. Discharged via
    `checkRelocFn`, `checkRelocFnAt`, or `Obj.RelocFnIndex`. -/
def Obj.ObjectInfo.RelocFnChecked (o : Obj.ObjectInfo) (symName : String)
    (relocs : List Obj.RelocEntry) (words : List (BitVec 32)) : Prop :=
  ∃ fn ∈ o.relocFns,
    fn.sym = symName ∧
    fn.relocs = relocs ∧
    checkRelocCodeWords fn.code words relocs = true

theorem Obj.ObjectInfo.RelocFnChecked.of_checkRelocFn {o : Obj.ObjectInfo} {symName : String}
    {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (h : checkRelocFn o symName relocs words = true) :
    o.RelocFnChecked symName relocs words := by
  unfold checkRelocFn at h
  split at h <;> try contradiction
  rename_i fn hfn_find
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hfn_sym : fn.sym = symName := by
    have hs := List.find?_some hfn_find
    exact beq_iff_eq.mp hs
  exact ⟨fn, List.mem_of_find?_eq_some hfn_find, hfn_sym, h.1, h.2⟩

theorem Obj.ObjectInfo.RelocFnChecked.of_checkRelocFnAt {o : Obj.ObjectInfo} {idx : Nat}
    {symName : String} {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (h : checkRelocFnAt o idx symName relocs words = true) :
    o.RelocFnChecked symName relocs words := by
  unfold checkRelocFnAt at h
  split at h <;> try contradiction
  rename_i fn hfn
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨fn, List.mem_of_getElem? hfn, h.1.1, h.1.2, h.2⟩

theorem Obj.ObjectInfo.RelocFnChecked.of_at_rfl {o : Obj.ObjectInfo} {idx : Nat}
    {symName : String} {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (hmeta : (o.relocFns[idx]?).map (fun f => (f.sym, f.relocs)) = some (symName, relocs))
    (hwords : checkRelocWordsAt o idx words = true) :
    o.RelocFnChecked symName relocs words := by
  unfold checkRelocWordsAt at hwords
  cases hfn : o.relocFns[idx]? with
  | none => simp [hfn] at hmeta
  | some fn =>
    simp only [hfn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmeta hwords
    rcases hmeta with ⟨rfl, rfl⟩
    exact ⟨fn, List.mem_of_getElem? hfn, rfl, rfl, hwords⟩

private theorem eq_of_mem_of_nodup_map {α β : Type _} {f : α → β} {l : List α}
    (hn : (l.map f).Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (heq : f a = f b) :
    a = b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hx, hxs⟩ := hn
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (heq ▸ List.mem_map_of_mem hb') hx
    · exact absurd (heq.symm ▸ List.mem_map_of_mem ha') hx
    · exact ih hxs ha' hb'

/-- Convert `o.RelocFnChecked symName relocs words` to `checkRelocFn o symName relocs words = true`
    when `o.relocFns` has distinct symbol names. -/
theorem checkRelocFn_of_checked {o : Obj.ObjectInfo} {symName : String}
    {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (hnodup : (o.relocFns.map (·.sym)).Nodup)
    (h : o.RelocFnChecked symName relocs words) :
    checkRelocFn o symName relocs words = true := by
  obtain ⟨fn, hfn_mem, hfn_sym, hr_eq, hcw⟩ := h
  unfold checkRelocFn
  cases hfind : o.relocFns.find? (·.sym == symName) with
  | none =>
    have hnone := (List.find?_eq_none.mp hfind) fn hfn_mem
    simp [hfn_sym] at hnone
  | some fn' =>
    have hfn'_mem : fn' ∈ o.relocFns := List.mem_of_find?_eq_some hfind
    have hbsym := List.find?_some hfind
    have hfn'_sym : fn'.sym = symName := by simpa using hbsym
    have heq : fn' = fn :=
      eq_of_mem_of_nodup_map hnodup hfn'_mem hfn_mem (hfn'_sym.trans hfn_sym.symm)
    subst heq
    simp [hr_eq, hcw]

/-- Precomputed `O(log F)` balanced tree and 1024-bucket character hash index over `o.relocFns`
    for `O(log F)` per-function symbol lookup. -/
structure Obj.RelocFnIndex (o : Obj.ObjectInfo) where
  /-- Balanced binary tree over `o.relocFns`. -/
  fnsTree : IdxTree Obj.SymCodeInfo
  /-- 1024-bucket hash table mapping `hashChars1024 fn.sym.toList` to `(fn.sym.toList, idx)`. -/
  symBuckets : IdxTree (List (List Char × Nat))
  /-- Tree leaves match `o.relocFns` in order. -/
  toList_eq : fnsTree.toList = o.relocFns
  /-- Function symbol names in `o.relocFns` are pairwise distinct. -/
  syms_nodup : (o.relocFns.map (·.sym)).Nodup

namespace Obj.RelocFnIndex

/-- Resolve character list `cs` to its entry index in `o.relocFns` via the 1024-bucket hash
    tree, cross-checking the retrieved `Obj.SymCodeInfo` leaf via `String.ofList cs`. -/
def lookupIdxChars {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o) (cs : List Char) :
    Option Nat :=
  match idx.symBuckets.get? (hashChars1024 cs) with
  | some bucket =>
    match bucket.find? (fun p => charListBeq p.1 cs) with
    | some (_, fnIdx) =>
      match idx.fnsTree.get? fnIdx with
      | some fn => if fn.sym == String.ofList cs then some fnIdx else none
      | none => none
    | none => none
  | none => none

/-- Resolve symbol `symName` to its entry index in `o.relocFns` in `O(log F)` kernel steps. -/
def lookupIdx {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o) (symName : String) : Option Nat :=
  idx.lookupIdxChars symName.toList

/-- Look up the `Obj.SymCodeInfo` for `String.ofList cs` in `O(log F)` kernel steps without
    evaluating `String.toList`. -/
def findFn?Chars {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o) (cs : List Char) :
    Option Obj.SymCodeInfo :=
  match idx.lookupIdxChars cs with
  | some i => idx.fnsTree.get? i
  | none => none

/-- Look up the `Obj.SymCodeInfo` for `symName` in `O(log F)` kernel steps. -/
def findFn? {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o) (symName : String) :
    Option Obj.SymCodeInfo :=
  idx.findFn?Chars symName.toList

/-- Decidable `O(log F + N + R)` check by symbol name against `idx`. -/
def check {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o) (symName : String)
    (relocs : List Obj.RelocEntry) (words : List (BitVec 32)) : Bool :=
  match idx.findFn? symName with
  | some fn => (fn.relocs == relocs) && checkRelocCodeWords fn.code words relocs
  | none => false

/-- Decidable `O(log F + N + R)` check on only the code words at tree index `i` (pair with
    `rfl_kernel` on `(idx.fnsTree.get? i).map (fun f => (f.sym, f.relocs))`). -/
def checkWordsAt {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o) (i : Nat)
    (words : List (BitVec 32)) : Bool :=
  match idx.fnsTree.get? i with
  | some fn => checkRelocCodeWords fn.code words fn.relocs
  | none => false

theorem mem_relocFns_of_get? {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o)
    {i : Nat} {fn : Obj.SymCodeInfo} (h : idx.fnsTree.get? i = some fn) :
    fn ∈ o.relocFns :=
  idx.toList_eq ▸ IdxTree.mem_toList_of_get? h

theorem findFn?Chars_spec {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o)
    {cs : List Char} {fn : Obj.SymCodeInfo}
    (h : idx.findFn?Chars cs = some fn) :
    fn ∈ o.relocFns ∧ fn.sym = String.ofList cs := by
  unfold findFn?Chars lookupIdxChars at h
  cases hb : idx.symBuckets.get? (hashChars1024 cs) with
  | none => simp [hb] at h
  | some bucket =>
    simp only [hb] at h
    cases hf : bucket.find? (fun p => charListBeq p.1 cs) with
    | none => simp [hf] at h
    | some p =>
      rcases p with ⟨_, fnIdx⟩
      simp only [hf] at h
      cases hg : idx.fnsTree.get? fnIdx with
      | none => simp [hg] at h
      | some fn0 =>
        simp only [hg] at h
        cases hc : (fn0.sym == String.ofList cs) with
        | false => simp [hc] at h
        | true =>
          simp only [hc, ↓reduceIte, hg, Option.some.injEq] at h
          subst h
          exact ⟨idx.mem_relocFns_of_get? hg, beq_iff_eq.mp hc⟩

theorem findFn?_spec {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o)
    {symName : String} {fn : Obj.SymCodeInfo}
    (h : idx.findFn? symName = some fn) :
    fn ∈ o.relocFns ∧ fn.sym = symName := by
  obtain ⟨hm, hs⟩ := idx.findFn?Chars_spec h
  exact ⟨hm, hs.trans String.ofList_toList⟩

theorem checked_of_check {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o)
    {symName : String} {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (h : idx.check symName relocs words = true) :
    o.RelocFnChecked symName relocs words := by
  unfold check at h
  cases hf : idx.findFn? symName with
  | none => simp [hf] at h
  | some fn =>
    simp only [hf, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hmem, hsym⟩ := idx.findFn?_spec hf
    exact ⟨fn, hmem, hsym, h.1, h.2⟩

theorem checkRelocFn_of_check {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o)
    {symName : String} {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (h : idx.check symName relocs words = true) :
    checkRelocFn o symName relocs words = true :=
  checkRelocFn_of_checked idx.syms_nodup (idx.checked_of_check h)

theorem checked_of_at {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o)
    {i : Nat} {symName : String} {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (hmeta : (idx.fnsTree.get? i).map (fun f => (f.sym, f.relocs)) = some (symName, relocs))
    (hwords : idx.checkWordsAt i words = true) :
    o.RelocFnChecked symName relocs words := by
  unfold checkWordsAt at hwords
  cases hfn : idx.fnsTree.get? i with
  | none => simp [hfn] at hmeta
  | some fn =>
    simp only [hfn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmeta hwords
    rcases hmeta with ⟨rfl, rfl⟩
    exact ⟨fn, idx.mem_relocFns_of_get? hfn, rfl, rfl, hwords⟩

theorem checkRelocFn_of_at {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o)
    {i : Nat} {symName : String} {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (hmeta : (idx.fnsTree.get? i).map (fun f => (f.sym, f.relocs)) = some (symName, relocs))
    (hwords : idx.checkWordsAt i words = true) :
    checkRelocFn o symName relocs words = true :=
  checkRelocFn_of_checked idx.syms_nodup (idx.checked_of_at hmeta hwords)

end Obj.RelocFnIndex

/-- From `Obj.Loads li img`, `o ∈ li.objects`, and `o.RelocFnChecked fnName relocs words`,
    extracts the relocated function's symbol offset `off`, resolver `resolve`, range predicates,
    and `hasWords` over `Obj.patchRelocs relocs words a resolve`. -/
theorem Obj.Loads.relocFn_hasWords_of_checked {li : Obj.LinkedImage} {img : Obj.Image}
    {externs : String → Option (State → State)} {o : Obj.ObjectInfo}
    {fnName : String} {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (hl : Obj.Loads li img) (ho_mem : o ∈ li.objects)
    (hcheck : o.RelocFnChecked fnName relocs words) :
    ∃ syms off,
      Obj.lookup o.name li.objSymbols = some syms ∧
      Obj.lookupUnique fnName syms = some off ∧
      Obj.lookup fnName li.symbols = some off ∧
      let a : BitVec 64 := img.base + BitVec.ofNat 64 off
      let resolve : String → BitVec 64 := fun n =>
        img.base + BitVec.ofNat 64 ((li.resolveObjSym o.name n false).getD 0)
      img.ResolvesObj li o.name (relocs.map (·.sym)) resolve ∧
      (∀ r ∈ relocs,
        Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
          (Obj.addSignedAddr (resolve r.sym) r.addend)) ∧
      (Program.ofImage img externs).hasWords a
        (Obj.patchRelocs relocs words a resolve) := by
  obtain ⟨fn, hfn_mem, hfn_sym, hr_eq, hcw⟩ := hcheck
  unfold checkRelocCodeWords at hcw
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hcw
  obtain ⟨hw_ne, hstream⟩ := hcw
  have hwpos : 0 < words.length := List.length_pos_iff.mpr hw_ne
  obtain ⟨hlen, _hge, hwordsStream⟩ := checkRelocWordsStream_spec hstream
  have hwordsCheck : ∀ j (hj : j < words.length),
      ∃ w', ({ code := fn.code } : Program).readWordOff (4 * j) = some w' ∧
        match relocs.find? (·.off == 4 * j) with
        | some r => w' &&& Obj.relocOpcodeMask r.kind = words[j] &&& Obj.relocOpcodeMask r.kind
        | none => w' = words[j] := by
    intro j hj
    simpa [Nat.zero_add] using hwordsStream j hj
  obtain ⟨_, _, _, hwf, _, _⟩ := ProofLib.ObjectLoad.load_eq_ok hl
  obtain ⟨_, hcode, _, hstubsEq, _, hb_mod, _⟩ := ProofLib.ObjectLoad.load_ok hl
  have hb_fff : img.base &&& 0xfff#64 = 0#64 := Obj.base_aligned_and_fff hb_mod
  have hcodeLe := Obj.LinkedImage.wellFormed_code_le hwf
  obtain ⟨syms, off, hsyms, hoff, hsym, hal, _hbmod, hend, hrels, hwords_li, hstubs⟩ :=
    Obj.LinkedImage.honours_relocFn (Obj.LinkedImage.wellFormed_objects hwf o ho_mem) hfn_mem
  rw [hfn_sym] at hoff hsym
  let a : BitVec 64 := img.base + BitVec.ofNat 64 off
  let resolve : String → BitVec 64 := fun n =>
    img.base + BitVec.ofNat 64 ((li.resolveObjSym o.name n false).getD 0)
  have hres_obj : img.ResolvesObj li o.name (relocs.map (·.sym)) resolve := by
    refine ⟨hl, ?_⟩
    intro n hn
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hn
    rw [← hr_eq] at hr
    obtain ⟨t, ht, -⟩ := hrels r hr
    obtain ⟨symOff, hsymOff, -⟩ := Obj.LinkedImage.resolveRelocTarget_eq_some ht
    exact ⟨symOff, hsymOff, by simp [resolve, hsymOff]⟩
  have hrange : ∀ r ∈ relocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend) := by
    intro r hr
    have hr' : r ∈ fn.relocs := hr_eq ▸ hr
    obtain ⟨t, ht, hcr⟩ := hrels r hr'
    obtain ⟨symOff, hsymOff, hadd⟩ := Obj.LinkedImage.resolveRelocTarget_eq_some ht
    have hres_eq : resolve r.sym = img.base + BitVec.ofNat 64 symOff := by
      simp [resolve, hsymOff]
    rw [hres_eq, Obj.addSignedAddr_eq_of_addSignedOff img.base hadd]
    exact Obj.codeRelocInRange_to_prop hb_fff hcr
  have hoff_sub : (a - (Program.ofImage img externs).base).toNat = off := by
    have : a - (Program.ofImage img externs).base = BitVec.ofNat 64 off := by
      show img.base + BitVec.ofNat 64 off - img.base = _
      bv_arith
    rw [this, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hwords : (Program.ofImage img externs).hasWords a
      (Obj.patchRelocs relocs words a resolve) := by
    unfold Program.hasWords Program.hasWordsOff
    rw [hoff_sub]
    have hp_len : (Obj.patchRelocs relocs words a resolve).length = words.length := by
      simp [Obj.patchRelocs]
    refine ⟨by omega, fun j hj => ?_, ?_⟩
    · have hj' : j < words.length := by omega
      have hj_bs : j < fn.code.length / 4 := by omega
      have htake_li := hwords_li j hj_bs
      have htake_prog : ((Program.ofImage img externs).code.drop (off + 4 * j)).take 4 =
          (li.code.drop (off + 4 * j)).take 4 := by
        show (img.code.drop (off + 4 * j)).take 4 = _
        rw [hcode]
      rw [htake_li, hr_eq] at htake_prog
      obtain ⟨w', hw', hwc⟩ := hwordsCheck j hj'
      have hw_le : Obj.wordOfBytesLE fn.code (4 * j) = w' :=
        Obj.wordOfBytesLE_eq_of_readWordOff hw'
      simp only [Obj.patchRelocs, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
      cases hfind : relocs.find? (·.off == 4 * j) with
      | none =>
        simp only [hfind] at hwc htake_prog ⊢
        rw [Obj.readWordOff_eq_of_take4 (prog2 := { code := fn.code }) (k2 := 4 * j) (by omega) (by omega) htake_prog, hw', hwc]
      | some r =>
        simp only [hfind] at hwc htake_prog ⊢
        have hroff : r.off = 4 * j := by
          have := List.find?_some hfind
          simpa [beq_iff_eq] using this
        have hr_mem : r ∈ fn.relocs := hr_eq ▸ List.mem_of_find?_eq_some hfind
        obtain ⟨t, ht, hcr⟩ := hrels r hr_mem
        rw [hroff] at hcr
        obtain ⟨symOff, hsymOff, hadd⟩ := Obj.LinkedImage.resolveRelocTarget_eq_some ht
        have hres_eq : resolve r.sym = img.base + BitVec.ofNat 64 symOff := by
          simp [resolve, hsymOff]
        have hread := Obj.readWordOff_of_take4_bytesOfWordLE (by omega) htake_prog
        rw [hread]
        congr 1
        rw [hw_le, Obj.patchCodeRelocWord_eq_of_mask hwc, ht, Option.getD_some, hres_eq,
          Obj.addSignedAddr_eq_of_addSignedOff img.base hadd,
          Obj.patchRelocWord_base_add hb_fff hcr]
    · unfold Program.hookFree
      rw [List.all_eq_true, List.all_eq_true]
      refine ⟨?_, ?_⟩
      · rintro ⟨n, stubOff⟩ hstub
        rw [Bool.or_eq_true]
        left
        have hge := hstubs (n, stubOff) (by
          have hstub' : (n, stubOff) ∈ img.stubs := hstub
          rwa [hstubsEq] at hstub')
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq,
          decide_eq_false_iff_not]
        intro _
        simp only at hge
        omega
      · rintro ⟨n, symOff⟩ _
        rw [Bool.or_eq_true]
        right
        rfl
  exact ⟨syms, off, hsyms, hoff, hsym, hres_obj, hrange, hwords⟩

/-- From `Obj.Loads li img`, `o ∈ li.objects`, and `checkRelocFn o fnName relocs words = true`,
    extracts the relocated function's symbol offset `off`, resolver `resolve`, range predicates,
    and `hasWords` over `Obj.patchRelocs relocs words a resolve`. -/
theorem Obj.Loads.relocFn_hasWords {li : Obj.LinkedImage} {img : Obj.Image}
    {externs : String → Option (State → State)} {o : Obj.ObjectInfo}
    {fnName : String} {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (hl : Obj.Loads li img) (ho_mem : o ∈ li.objects)
    (hcheck : checkRelocFn o fnName relocs words = true) :
    ∃ syms off,
      Obj.lookup o.name li.objSymbols = some syms ∧
      Obj.lookupUnique fnName syms = some off ∧
      Obj.lookup fnName li.symbols = some off ∧
      let a : BitVec 64 := img.base + BitVec.ofNat 64 off
      let resolve : String → BitVec 64 := fun n =>
        img.base + BitVec.ofNat 64 ((li.resolveObjSym o.name n false).getD 0)
      img.ResolvesObj li o.name (relocs.map (·.sym)) resolve ∧
      (∀ r ∈ relocs,
        Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
          (Obj.addSignedAddr (resolve r.sym) r.addend)) ∧
      (Program.ofImage img externs).hasWords a
        (Obj.patchRelocs relocs words a resolve) :=
  Obj.Loads.relocFn_hasWords_of_checked hl ho_mem (Obj.ObjectInfo.RelocFnChecked.of_checkRelocFn hcheck)

/-- Layout-generic contract verification for a function recorded in `o.relocFns` with arbitrary
    relocations (`ADRP`, `:lo12:`, `B`/`BL`, `B.cond`/`CBZ`/`TBZ`, `ADR`, `PREL32`). -/
theorem Contract.holds_of_relocFn {libs trusted : List LibrarySpec} {img : Obj.Image}
    {X : String → Option (State → State)} {D : LibrarySpec} {c : Contract}
    {o : Obj.ObjectInfo} {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (hLinks : LinksIn libs img trusted) (hD : D ∈ libs) (hDT : D ∉ trusted)
    (ho : D.obj = some o)
    (hcheck : checkRelocFn o c.sym relocs words = true)
    (habs : ∀ a resolve,
      img.RelocCtx libs trusted o.name (relocs.map (·.sym)) resolve →
      (∀ r ∈ relocs,
        Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
          (Obj.addSignedAddr (resolve r.sym) r.addend)) →
      (Program.ofImage img (Rust.withPanics X)).hasWords a
        (Obj.patchRelocs relocs words a resolve) →
      subroutine_ok (Program.ofImage img (Rust.withPanics X)) a (c.spec.inImage img)) :
    Contract.Holds D img X c := by
  obtain ⟨li, hobjs, hl⟩ := hLinks
  have ho_mem : o ∈ li.objects := LinksIn.objectLoaded hobjs hD hDT ho
  obtain ⟨_, _, _, _, hobjSyms, _, _⟩ := ProofLib.ObjectLoad.load_ok hl
  obtain ⟨syms, off, hsyms, hoff, _hsym, hres_obj, hrange, hwords⟩ :=
    Obj.Loads.relocFn_hasWords (externs := Rust.withPanics X) hl ho_mem hcheck
  let a : BitVec 64 := img.base + BitVec.ofNat 64 off
  let resolve : String → BitVec 64 := fun n =>
    img.base + BitVec.ofNat 64 ((li.resolveObjSym o.name n false).getD 0)
  have haddr : D.addr? img c.sym = some a := by
    simp [LibrarySpec.addr?, ho, hobjSyms, hsyms, hoff, a]
  exact ⟨a, haddr, habs a resolve ⟨li, hobjs, hres_obj⟩ hrange hwords⟩

theorem Obj.findSymbol?_ofImage_eq_resolveSym {li : Obj.LinkedImage} {img : Obj.Image}
    {externs overrides : String → Option (State → State)}
    (hl : Obj.Loads li img) (name : String) :
    (Program.ofImage img externs overrides).findSymbol? name = li.resolveSym name := by
  obtain ⟨_, _, hsyms, hstubs, _, _, _⟩ := ProofLib.ObjectLoad.load_ok hl
  unfold Program.findSymbol? Program.ofImage Obj.LinkedImage.resolveSym Obj.lookup
  simp only [hsyms, hstubs]
  cases li.symbols.find? (·.1 == name) <;> rfl

theorem Obj.fnAddr_ofImage_eq_of_resolveSym {li : Obj.LinkedImage} {img : Obj.Image}
    {externs overrides : String → Option (State → State)}
    {name : String} {off : Nat}
    (hl : Obj.Loads li img) (hres : li.resolveSym name = some off) :
    (Program.ofImage img externs overrides).fnAddr name = img.base + BitVec.ofNat 64 off := by
  unfold Program.fnAddr Program.fnOff
  rw [Obj.findSymbol?_ofImage_eq_resolveSym hl name, hres]
  rfl

theorem Obj.Image.ResolvesObj.resolve_eq {img : Obj.Image} {li : Obj.LinkedImage}
    {objName : String} {names : List String} {resolve : String → BitVec 64}
    {n : String} {off : Nat}
    (hctx : img.ResolvesObj li objName names resolve)
    (hmem : n ∈ names)
    (hres : li.resolveObjSym objName n false = some off) :
    resolve n = img.base + BitVec.ofNat 64 off := by
  obtain ⟨_, h⟩ := hctx
  obtain ⟨off', hoff', heq⟩ := h n hmem
  rw [hres] at hoff'
  injection hoff' with h_eq
  subst h_eq
  exact heq

theorem Obj.Image.ResolvesObj.resolve_eq_fnAddr {img : Obj.Image} {li : Obj.LinkedImage}
    {externs overrides : String → Option (State → State)}
    {objName : String} {names : List String} {resolve : String → BitVec 64}
    {n : String}
    (hctx : img.ResolvesObj li objName names resolve)
    (hmem : n ∈ names)
    (heq : li.resolveObjSym objName n false = li.resolveSym n) :
    resolve n = (Program.ofImage img externs overrides).fnAddr n := by
  obtain ⟨hl, h⟩ := hctx
  obtain ⟨off, hoff, hres⟩ := h n hmem
  rw [heq] at hoff
  rw [hres, Obj.fnAddr_ofImage_eq_of_resolveSym hl hoff]

/-- Layout-generic subroutine verification for a function witnessed by `o.RelocFnChecked`. -/
theorem Obj.Loads.subroutineOk_of_relocFnChecked {S α : Type} [ToBaseSpec S α]
    {li : Obj.LinkedImage} {img : Obj.Image}
    {externs : String → Option (State → State)}
    {o : Obj.ObjectInfo} {fnName : String} {spec : S}
    {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (hl : Obj.Loads li img) (ho_mem : o ∈ li.objects)
    (hcheck : o.RelocFnChecked fnName relocs words)
    (habs : ∀ a resolve,
      img.ResolvesObj li o.name (relocs.map (·.sym)) resolve →
      (∀ r ∈ relocs,
        Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
          (Obj.addSignedAddr (resolve r.sym) r.addend)) →
      (Program.ofImage img externs).hasWords a
        (Obj.patchRelocs relocs words a resolve) →
      subroutine_ok (Program.ofImage img externs) a (ToBaseSpec.toSpec spec img.base)) :
    (Program.ofImage img externs).subroutineOk fnName spec := by
  obtain ⟨_syms, off, _hsyms, _hoff, hsym, hres_obj, hrange, hwords⟩ :=
    Obj.Loads.relocFn_hasWords_of_checked (externs := externs) hl ho_mem hcheck
  have hres : li.resolveSym fnName = some off := by
    simp [Obj.LinkedImage.resolveSym, hsym]
  unfold Program.subroutineOk
  rw [Obj.fnAddr_ofImage_eq_of_resolveSym hl hres]
  exact habs (img.base + BitVec.ofNat 64 off) _ hres_obj hrange hwords

/-- Layout-generic subroutine verification for a function recorded in `o.relocFns` of a loaded
    `LinkedImage` `li` (`Obj.Loads li img`, `o ∈ li.objects`). -/
theorem Obj.Loads.subroutineOk_of_relocFn {S α : Type} [ToBaseSpec S α]
    {li : Obj.LinkedImage} {img : Obj.Image}
    {externs : String → Option (State → State)}
    {o : Obj.ObjectInfo} {fnName : String} {spec : S}
    {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (hl : Obj.Loads li img) (ho_mem : o ∈ li.objects)
    (hcheck : checkRelocFn o fnName relocs words = true)
    (habs : ∀ a resolve,
      img.ResolvesObj li o.name (relocs.map (·.sym)) resolve →
      (∀ r ∈ relocs,
        Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
          (Obj.addSignedAddr (resolve r.sym) r.addend)) →
      (Program.ofImage img externs).hasWords a
        (Obj.patchRelocs relocs words a resolve) →
      subroutine_ok (Program.ofImage img externs) a (ToBaseSpec.toSpec spec img.base)) :
    (Program.ofImage img externs).subroutineOk fnName spec :=
  Obj.Loads.subroutineOk_of_relocFnChecked hl ho_mem
    (Obj.ObjectInfo.RelocFnChecked.of_checkRelocFn hcheck) habs

/-- Layout-generic subroutine verification for a relocation-free function recorded in `o.fns`
    of a loaded `LinkedImage` `li`: from `checkRelocFreeFn o fnName words = true` (with `words`
    non-empty) and a proof over every address `a` holding `words`, conclude `subroutineOk`. -/
theorem Obj.Loads.subroutineOk_of_relocFreeFn {S α : Type} [ToBaseSpec S α]
    {li : Obj.LinkedImage} {img : Obj.Image} {externs : String → Option (State → State)}
    {o : Obj.ObjectInfo} {fnName : String} {spec : S} {words : List (BitVec 32)}
    (hl : Obj.Loads li img) (ho : o ∈ li.objects)
    (hcheck : checkRelocFreeFn o fnName words = true) (hne : 0 < words.length)
    (habs : ∀ a, (Program.ofImage img externs).hasWords a words →
      subroutine_ok (Program.ofImage img externs) a (ToBaseSpec.toSpec spec img.base)) :
    (Program.ofImage img externs).subroutineOk fnName spec := by
  unfold checkRelocFreeFn at hcheck
  split at hcheck
  case h_2 => contradiction
  rename_i bs hbs
  obtain ⟨hlen, hw⟩ := checkBytesWordsBound_hasWordsOff_zero hcheck
  obtain ⟨_, _, _, hwf, _hwrap, _⟩ := ProofLib.ObjectLoad.load_eq_ok hl
  obtain ⟨_, hcode, _, hstubsEq, _, _, _⟩ := ProofLib.ObjectLoad.load_ok hl
  have hhon := Obj.LinkedImage.wellFormed_objects hwf o ho
  obtain ⟨syms, off, hsyms, hoff, hal, hend, hslice, hstubs⟩ :=
    Obj.LinkedImage.honours_fn hhon (Obj.lookup_mem hbs)
  obtain ⟨syms', off', hsyms', hoff', hsym⟩ :=
    Obj.LinkedImage.honours_fn_sym hhon (Obj.lookup_mem hbs)
  rw [hsyms] at hsyms'
  cases hsyms'
  rw [hoff] at hoff'
  cases hoff'
  have hcodeLe := Obj.LinkedImage.wellFormed_code_le hwf
  have hres : li.resolveSym fnName = some off := by
    simp [Obj.LinkedImage.resolveSym, hsym]
  unfold Program.subroutineOk
  rw [Obj.fnAddr_ofImage_eq_of_resolveSym hl hres]
  apply habs
  have hoff_sub : (img.base + BitVec.ofNat 64 off - (Program.ofImage img externs).base).toNat
      = off := by
    have : img.base + BitVec.ofNat 64 off - (Program.ofImage img externs).base =
        BitVec.ofNat 64 off := by
      show img.base + BitVec.ofNat 64 off - img.base = _
      bv_arith
    rw [this, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  unfold Program.hasWords Program.hasWordsOff
  rw [hoff_sub]
  refine ⟨by omega, fun i hi => ?_, ?_⟩
  · have hslice' : ((Program.ofImage img externs).code.drop off).take bs.length = bs := by
      show (img.code.drop off).take bs.length = bs
      rw [hcode]; exact hslice
    rw [Obj.readWordOff_of_slice hslice' hal (by omega) (by omega)]
    have := hw.2.1 i hi
    rwa [Nat.zero_add] at this
  · unfold Program.hookFree
    rw [List.all_eq_true, List.all_eq_true]
    refine ⟨?_, ?_⟩
    · rintro ⟨n, stubOff⟩ hstub
      rw [Bool.or_eq_true]
      left
      have hge := hstubs (n, stubOff) (by
        have hstub' : (n, stubOff) ∈ img.stubs := hstub
        rwa [hstubsEq] at hstub')
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq,
        decide_eq_false_iff_not]
      intro _
      simp only at hge
      omega
    · rintro ⟨n, symOff⟩ _
      rw [Bool.or_eq_true]
      right
      rfl

/-- Layout-generic `LinkedImage.subroutineOk` verification from a `o.RelocFnChecked` witness. -/
theorem Obj.LinkedImage.subroutineOk_of_relocFnChecked {S α : Type} [ToBaseSpec S α]
    {li : Obj.LinkedImage}
    {externs : String → Option (State → State)}
    {o : Obj.ObjectInfo} {fnName : String} {spec : S}
    {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (ho_mem : o ∈ li.objects)
    (hcheck : o.RelocFnChecked fnName relocs words)
    (habs : ∀ img a resolve,
      img.ResolvesObj li o.name (relocs.map (·.sym)) resolve →
      (∀ r ∈ relocs,
        Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
          (Obj.addSignedAddr (resolve r.sym) r.addend)) →
      (Program.ofImage img externs).hasWords a
        (Obj.patchRelocs relocs words a resolve) →
      subroutine_ok (Program.ofImage img externs) a (ToBaseSpec.toSpec spec img.base)) :
    li.subroutineOk fnName spec externs := by
  intro img hl
  exact Obj.Loads.subroutineOk_of_relocFnChecked hl ho_mem hcheck (habs img)

/-- Layout-generic `LinkedImage.subroutineOk` verification for a function recorded in `o.relocFns`. -/
theorem Obj.LinkedImage.subroutineOk_of_relocFn {S α : Type} [ToBaseSpec S α]
    {li : Obj.LinkedImage}
    {externs : String → Option (State → State)}
    {o : Obj.ObjectInfo} {fnName : String} {spec : S}
    {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (ho_mem : o ∈ li.objects)
    (hcheck : checkRelocFn o fnName relocs words = true)
    (habs : ∀ img a resolve,
      img.ResolvesObj li o.name (relocs.map (·.sym)) resolve →
      (∀ r ∈ relocs,
        Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
          (Obj.addSignedAddr (resolve r.sym) r.addend)) →
      (Program.ofImage img externs).hasWords a
        (Obj.patchRelocs relocs words a resolve) →
      subroutine_ok (Program.ofImage img externs) a (ToBaseSpec.toSpec spec img.base)) :
    li.subroutineOk fnName spec externs :=
  Obj.LinkedImage.subroutineOk_of_relocFnChecked ho_mem
    (Obj.ObjectInfo.RelocFnChecked.of_checkRelocFn hcheck) habs

/-- Layout-generic `LinkedImage.subroutineOk` verification resolved via an `O(log F)`
    `Obj.RelocFnIndex`. -/
theorem Obj.RelocFnIndex.subroutineOk_of_relocFn {S α : Type} [ToBaseSpec S α]
    {li : Obj.LinkedImage}
    {externs : String → Option (State → State)}
    {o : Obj.ObjectInfo} (idx : Obj.RelocFnIndex o) {fnName : String} {spec : S}
    {relocs : List Obj.RelocEntry} {words : List (BitVec 32)}
    (ho_mem : o ∈ li.objects)
    (hcheck : idx.check fnName relocs words = true)
    (habs : ∀ img a resolve,
      img.ResolvesObj li o.name (relocs.map (·.sym)) resolve →
      (∀ r ∈ relocs,
        Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
          (Obj.addSignedAddr (resolve r.sym) r.addend)) →
      (Program.ofImage img externs).hasWords a
        (Obj.patchRelocs relocs words a resolve) →
      subroutine_ok (Program.ofImage img externs) a (ToBaseSpec.toSpec spec img.base)) :
    li.subroutineOk fnName spec externs :=
  Obj.LinkedImage.subroutineOk_of_relocFnChecked ho_mem (idx.checked_of_check hcheck) habs

end Arm64

