/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `<Poly>::lagrange_interpolate_prepare`: Inner Loop and Helpers

Bit-extraction (`sbfx`), inline carryless `GF(2^16)` multiplication, and inner trailing-multiply
loop verification for `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare`
(`0x61c1c`, Block `372`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.LagrangePrepare

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

attribute [local wp_norm] zeroExtend_16_truncate_32_64

theorem aligned_86bd8 (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64) :
    MemWidth.isAligned .W32 (b + bv% (ls_xref% 0x5e628 0x5e62c)) = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  revert hb; bv_bits

theorem truncate16_zext64 (u : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 u) = u := by
  bv_bits

theorem zext64_zext32_zext64 (u : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u)) =
      BitVec.zeroExtend 64 u := by
  bv_bits

theorem and_one_of_mod_two {p : BitVec 64} (h : p.toNat % 2 = 0) :
    p &&& 1#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change p.toNat &&& 1 = 0
  rw [Nat.and_one_is_mod, h]

theorem ofNat_mul_two_and_one (k : Nat) :
    (BitVec.ofNat 64 (2 * k)) &&& 1#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  change ((2 * k) % 2 ^ 64) &&& 1 = 0
  rw [Nat.and_one_is_mod]
  omega

theorem add_and_one_zero {a b : BitVec 64} (ha : a &&& 1#64 = 0#64) (hb : b &&& 1#64 = 0#64) :
    (a + b) &&& 1#64 = 0#64 := by
  revert ha hb; bv_bits

theorem aligned16_add_mul_two (p : BitVec 64) (hp : p &&& 1#64 = 0#64) (k : Nat) :
    MemWidth.isAligned .W16 (p + BitVec.ofNat 64 (2 * k)) = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  exact add_and_one_zero hp (ofNat_mul_two_and_one k)

theorem ofNat_mul_four_and_one (k : Nat) :
    (BitVec.ofNat 64 (4 * k)) &&& 1#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  change ((4 * k) % 2 ^ 64) &&& 1 = 0
  rw [Nat.and_one_is_mod]
  omega

theorem aligned16_add_mul_four (p : BitVec 64) (hp : p &&& 1#64 = 0#64) (k : Nat) :
    MemWidth.isAligned .W16 (p + BitVec.ofNat 64 (4 * k)) = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  exact add_and_one_zero hp (ofNat_mul_four_and_one k)

theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

theorem memRegion_two (a : BitVec 64) :
    memRegion a 2 = ∃∗ v : BitVec 16, a ↦₁₆ v :=
  IsBlock.eq (IsBlock.memRegion a 2)
    (IsBlock.sepExists fun v => IsBlock.pointsTo16 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem memRegion_alloc_split (ptr : BitVec 64) (n : Nat) (hn : 2 * (n + 1) ≤ 2 ^ 64) :
    memRegion ptr (2 * (n + 1)) =
      memRegion ptr (2 * n) ∗ (∃∗ v : BitVec 16, (ptr + BitVec.ofNat 64 (2 * n)) ↦₁₆ v) := by
  rw [show 2 * (n + 1) = 2 * n + 2 by omega, memRegion_split ptr (2 * n) 2 hn, memRegion_two]

/-- Result of `sbfx w_dst, w25, #bit, #1` as a 32-bit word (`readReg32`). -/
abbrev sbfxBit32 (w25 : BitVec 32) (bit : Nat) : BitVec 32 :=
  BitVec.truncate 32
    (BitVec.zeroExtend 64 w25 >>> bit &&& 1#64 |||
      (if (BitVec.zeroExtend 64 w25).getLsbD bit = true then
          18446744073709551615#64
        else 0#64) &&&
        18446744073709551614#64)

/-- Result of `sbfx w_dst, w25, #bit, #1` as a 64-bit register (`readReg64`). -/
abbrev sbfxBit64 (w25 : BitVec 32) (bit : Nat) : BitVec 64 :=
  BitVec.zeroExtend 64 (sbfxBit32 w25 bit)

theorem fnAddr_adrp_61c90 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr lagrangePrepareName + 116#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, lagrangePrepare_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_61cf0 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr lagrangePrepareName + 212#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, lagrangePrepare_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_61d04 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr lagrangePrepareName + 232#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, lagrangePrepare_fnOff]
  revert hb; bv_bits

theorem cmn_k_prev_ne_zero {k : Nat} (hk1 : 1 ≤ k) (hk_lt : k < 2 ^ 63) :
    (BitVec.ofNat 64 (k - 1) + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h1 : BitVec.ofNat 64 (k - 1) + 1#64 = BitVec.ofNat 64 k := by
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  rw [h1] at h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change k = 0 at ht
  omega

theorem add_neg_rem_eq_k_prev {n k rem' : Nat} (hk1 : 1 ≤ k) (hk_rem : k + rem' = n) :
    BitVec.ofNat 64 n + (0#64 - BitVec.ofNat 64 (rem' + 1)) = BitVec.ofNat 64 (k - 1) := by
  have hn : n = (k - 1) + (rem' + 1) := by omega
  rw [hn, BitVec.ofNat_add]
  bv_omega

theorem adds_neg_one_carry :
    (AddWithCarry64 (0#64 - 1#64) 1#64 false).2.c = true := by
  decide +kernel

theorem neg_succ_add_one (r : Nat) :
    -BitVec.ofNat 64 (r + 1) + 1#64 = -BitVec.ofNat 64 r := by
  rw [BitVec.ofNat_add]
  bv_omega

theorem neg_succ_ule_add_one {r : Nat} (hr_lt : r + 2 < 2 ^ 63) :
    (-BitVec.ofNat 64 (r + 1 + 1)).ule (-BitVec.ofNat 64 (r + 1 + 1) + 1#64) = true := by
  rw [neg_succ_add_one (r + 1), BitVec.ule_iff_toNat_le]
  simp only [BitVec.toNat_neg, BitVec.toNat_ofNat]
  omega

@[local arm64_norm, local wp_norm]
theorem ofNat_shl_two (i : Nat) :
    BitVec.ofNat 64 i <<< 2 = BitVec.ofNat 64 (4 * i) := by
  bv_omega

theorem ptr_sub_two_succ (ptr : BitVec 64) (r : Nat) :
    ptr + BitVec.ofNat 64 (2 * (r + 1)) - 2#64 = ptr + BitVec.ofNat 64 (2 * r) := by
  rw [show 2 * (r + 1) = 2 * r + 2 by omega, BitVec.ofNat_add]
  bv_omega

theorem neg_sub_one (m : Nat) :
    -BitVec.ofNat 64 m - 1#64 = -BitVec.ofNat 64 (m + 1) := by
  rw [BitVec.ofNat_add]
  bv_omega

theorem ofNat_bne_true_of_lt {a b : Nat} (hlt : a < b) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = true := by
  rw [bne_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
  omega

@[local arm64_norm, local wp_norm]
theorem truncate32_sext64_16 (yv : BitVec 16) :
    BitVec.truncate 32 (BitVec.signExtend 64 yv) = BitVec.signExtend 32 yv := by
  bv_bits

theorem sbfx64_helper (w : BitVec 64) :
    (w &&& 1#64 |||
      (if w.getLsbD 0 = true then 18446744073709551615#64 else 0#64) &&&
        18446744073709551614#64) =
      if w.getLsbD 0 then 18446744073709551615#64 else 0#64 := by
  bv_bits

@[local arm64_norm, local wp_norm]
theorem sbfx64_one_eq (v : BitVec 64) (i : Nat) :
    (v >>> i &&& 1#64 |||
      (if v.getLsbD i = true then 18446744073709551615#64 else 0#64) &&&
        18446744073709551614#64) =
      if v.getLsbD i then 18446744073709551615#64 else 0#64 := by
  have h0 : (v >>> i).getLsbD 0 = v.getLsbD i := by simp
  rw [← h0, sbfx64_helper]

@[local arm64_norm, local wp_norm]
theorem truncate32_if_all_ones (b : Bool) :
    BitVec.truncate 32 (if b then 18446744073709551615#64 else 0#64) =
      if b then 0xffffffff#32 else 0#32 := by
  cases b <;> rfl

@[local arm64_norm, local wp_norm]
theorem truncate32_zext64 (x : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 x) = x := by
  bv_bits

@[local arm64_norm, local wp_norm]
theorem zext64_zext32_16 (v : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 v) = BitVec.zeroExtend 64 v := by
  bv_bits

@[local arm64_norm, local wp_norm]
theorem and_65535_zext64_16 (v : BitVec 16) :
    BitVec.zeroExtend 64 v &&& 65535#64 = BitVec.zeroExtend 64 v := by
  bv_bits

abbrev sxth32Zext64 (yv : BitVec 16) : BitVec 64 :=
  BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)

def sbfxMask32 (yv : BitVec 16) (i : Nat) : BitVec 32 :=
  if (sxth32Zext64 yv).getLsbD i then 0xffffffff#32 else 0#32

def sbfxMask64 (yv : BitVec 16) (i : Nat) : BitVec 64 :=
  BitVec.zeroExtend 64 (sbfxMask32 yv i)

theorem sbfxMask64_from_if (yv : BitVec 16) (bit : Nat) :
    (if (BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)).getLsbD bit = true then 4294967295#64 else 0#64) =
      sbfxMask64 yv bit := by
  dsimp only [sbfxMask64, sbfxMask32, sxth32Zext64]
  cases (BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)).getLsbD bit <;> rfl

theorem prepare_polyReduce_xor_helper (prev r2 : BitVec 16) (v1 : BitVec 32) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
          (BitVec.truncate 32
            (BitVec.zeroExtend 64 prev ^^^ BitVec.zeroExtend 64 v1)) ^^^
        BitVec.zeroExtend 64 r2) =
      prev ^^^ BitVec.truncate 16 (v1 ^^^ BitVec.zeroExtend 32 r2) := by
  bv_slice

@[local arm64_norm, local wp_norm]
theorem prepare_polyReduce_xor_eq (prev cv yv : BitVec 16) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
          (BitVec.truncate 32
            (BitVec.zeroExtend 64 prev ^^^
              BitVec.zeroExtend 64
                (unaccelerated.polyMul cv yv ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul cv yv >>> 24))) <<<
                    8))) ^^^
        BitVec.zeroExtend 64
          (reduce.reduceByteEntry
            (BitVec.truncate 8
              ((unaccelerated.polyMul cv yv ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul cv yv >>> 24))) <<<
                    8) >>>
                16)))) =
      prev ^^^ unaccelerated.mul cv yv := by
  dsimp only [unaccelerated.mul, reduce.polyReduce]
  exact prepare_polyReduce_xor_helper prev _ _

theorem multXdiffLoopPure_succ (yv : BitVec 16) (k rem' : Nat) (cs : List GF16)
    (hk : k < cs.length) (hk_prev : k - 1 < cs.length) :
    multXdiffLoopPure ⟨yv⟩ k (rem' + 1) cs =
      multXdiffLoopPure ⟨yv⟩ (k + 1) rem'
        (cs.set (k - 1) ⟨(cs[k - 1]'hk_prev).value ^^^ unaccelerated.mul (cs[k]'hk).value yv⟩) := by
  have hci : cs[k]? = some (cs[k]'hk) := List.getElem?_eq_getElem hk
  have hciprev : cs[k - 1]? = some (cs[k - 1]'hk_prev) := List.getElem?_eq_getElem hk_prev
  simp only [multXdiffLoopPure, hci, hciprev, Option.getD_some, GF16.mul, GF16.sub, GF16.add]

theorem prepareLoopPure_succ (pts : List Pt) (i r_out : Nat) (p : Poly)
    (hi_rem : i + (r_out + 1) = pts.length)
    (hp_len : p.coefficients.length = pts.length + 1)
    (hi : i < pts.length) :
    prepareLoopPure pts pts.length i (r_out + 1) p =
      prepareLoopPure pts pts.length (i + 1) r_out
        ⟨multXdiffLoopPure (pts[i]'hi).x (r_out + 1) (i + 1) p.coefficients⟩ := by
  have hpi : pts[i]? = some (pts[i]'hi) := List.getElem?_eq_getElem hi
  have hsub : pts.length - i = r_out + 1 := by omega
  have hge : ¬ (r_out + 1 ≥ p.coefficients.length) := by omega
  have hl_sub : p.coefficients.length - (r_out + 1) = i + 1 := by omega
  have hpt : (pts[i]'hi).x = ⟨(pts[i]'hi).x.value⟩ := rfl
  simp only [prepareLoopPure, multXdiffPure, hpi, Option.getD_some, hsub, hge, ↓reduceIte, hl_sub]

theorem sxth32_trunc16 (yv : BitVec 16) :
    BitVec.truncate 16 (BitVec.signExtend 32 yv) = yv := by
  bv_bits

theorem sxth32Zext64_getLsbD (yv : BitVec 16) (i : Nat) (hi : i < 16) :
    (sxth32Zext64 yv).getLsbD i = yv.getLsbD i := by
  have h := congrArg (fun x => x.getLsbD i) (sxth32_trunc16 yv)
  have hi64 : i < 64 := by omega
  simpa [sxth32Zext64, hi, hi64] using h

theorem sbfxMask32_eq (yv : BitVec 16) (i : Nat) (hi : i < 16) :
    sbfxMask32 yv i = if yv.getLsbD i = true then 0xffff_ffff#32 else 0#32 := by
  dsimp only [sbfxMask32]
  rw [sxth32Zext64_getLsbD yv i hi]

theorem truncate32_sbfxMask64 (yv : BitVec 16) (i : Nat) (hi : i < 16) :
    BitVec.truncate 32 (sbfxMask64 yv i) =
      if yv.getLsbD i = true then 0xffff_ffff#32 else 0#32 := by
  dsimp only [sbfxMask64, sbfxMask32]
  rw [sxth32Zext64_getLsbD yv i hi]
  cases yv.getLsbD i <;> rfl

theorem sxth32_shr16 (yv : BitVec 16) :
    (BitVec.signExtend 32 yv) >>> 16 = if yv.getLsbD 15 then 0xffff#32 else 0#32 := by
  bv_bits

theorem sxth33_trunc16 (yv : BitVec 16) :
    BitVec.truncate 16 (BitVec.signExtend 33 (BitVec.signExtend 32 yv)) = yv := by
  bv_bits

theorem sxth33_shr16 (yv : BitVec 16) :
    (BitVec.signExtend 33 (BitVec.signExtend 32 yv)) >>> 16 =
      if yv.getLsbD 15 then 0x1ffff#33 else 0#33 := by
  bv_bits

theorem yv_shr15 (yv : BitVec 16) :
    yv >>> 15 = if yv.getLsbD 15 then 1#16 else 0#16 := by
  bv_bits

theorem beq_bne_self (a b : Bool) : (b == (a != b)) = !a := by
  cases a <;> cases b <;> rfl

theorem adds_sxth_one_gt (yv : BitVec 16) :
    ConditionHolds CondCode.GT (addsPState32 (BitVec.signExtend 32 yv) 1#32) = !yv.getLsbD 15 := by
  have hlo32 := congrArg BitVec.toNat (sxth32_trunc16 yv)
  have hhi32 := congrArg BitVec.toNat (sxth32_shr16 yv)
  have hlo33 := congrArg BitVec.toNat (sxth33_trunc16 yv)
  have hhi33 := congrArg BitVec.toNat (sxth33_shr16 yv)
  have hb15 := congrArg BitVec.toNat (yv_shr15 yv)
  rw [BitVec.toNat_setWidth] at hlo32 hlo33
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hhi32 hhi33 hb15
  have hlt16 : yv.toNat < 2 ^ 16 := yv.isLt
  have hlt32 : (BitVec.signExtend 32 yv).toNat < 2 ^ 32 := (BitVec.signExtend 32 yv).isLt
  have hlt33 : (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).toNat < 2 ^ 33 :=
    (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).isLt
  unfold ConditionHolds addsPState32 AddWithCarry32
  dsimp only
  rw [beq_bne_self]
  cases hb : yv.getLsbD 15 <;>
    simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] at hhi32 hhi33 hb15 ⊢
  · rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', beq_eq_false_iff_ne]
    change (BitVec.signExtend 32 yv).toNat / 65536 = 0 at hhi32
    change (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).toNat / 65536 = 0 at hhi33
    change yv.toNat / 32768 = 0 at hb15
    refine ⟨?_, ?_⟩
    · intro h
      have ht := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat] at ht
      omega
    · rw [BitVec.msb_eq_false_iff_two_mul_lt]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hs1 : (BitVec.signExtend 33 1#32).toNat = 1 := rfl
      rw [hs1]
      omega
  · rw [Bool.and_eq_false_iff, Bool.not_eq_false', Bool.not_eq_false', beq_iff_eq]
    change (BitVec.signExtend 32 yv).toNat / 65536 = 65535 at hhi32
    change (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).toNat / 65536 = 131071 at hhi33
    change yv.toNat / 32768 = 1 at hb15
    by_cases hy : yv.toNat = 65535
    · left
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · right
      rw [BitVec.msb_eq_true_iff_two_mul_ge]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hs1 : (BitVec.signExtend 33 1#32).toNat = 1 := rfl
      rw [hs1]
      omega

def pmTerm (cv yv : BitVec 16) (i : Nat) : BitVec 32 :=
  (BitVec.zeroExtend 32 cv <<< i) &&& (if yv.getLsbD i = true then 0xffff_ffff#32 else 0#32)

theorem ite_xor_eq_xor_and_mask (b : Bool) (acc x : BitVec 32) :
    (if b = true then acc ^^^ x else acc) =
      acc ^^^ (x &&& (if b = true then 0xffff_ffff#32 else 0#32)) := by
  cases b <;> bv_slice

theorem test_bit16_eq_getLsbD (yv : BitVec 16) (i : Nat) (hi : i < 16) :
    (0#16 != yv &&& (1#16 <<< i)) = yv.getLsbD i := by
  match i, hi with
  | 0, _ => bv_slice
  | 1, _ => bv_slice
  | 2, _ => bv_slice
  | 3, _ => bv_slice
  | 4, _ => bv_slice
  | 5, _ => bv_slice
  | 6, _ => bv_slice
  | 7, _ => bv_slice
  | 8, _ => bv_slice
  | 9, _ => bv_slice
  | 10, _ => bv_slice
  | 11, _ => bv_slice
  | 12, _ => bv_slice
  | 13, _ => bv_slice
  | 14, _ => bv_slice
  | 15, _ => bv_slice
  | n + 16, hi => omega

theorem pmTerm_rhs_0 (cv yv : BitVec 16) :
    (if (0#16 != yv &&& (1#16 <<< 0)) = true then BitVec.zeroExtend 32 cv <<< 0 else 0#32) =
      pmTerm cv yv 0 := by
  dsimp only [pmTerm]
  rw [test_bit16_eq_getLsbD yv 0 (by decide)]
  generalize yv.getLsbD 0 = b
  cases b <;> bv_slice

theorem pmTerm_rhs (cv yv : BitVec 16) (i : Nat) (hi : i < 16) :
    (BitVec.zeroExtend 32 cv <<< i) &&&
      (if (0#16 != yv &&& (1#16 <<< i)) = true then 0xffff_ffff#32 else 0#32) =
      pmTerm cv yv i := by
  dsimp only [pmTerm]
  rw [test_bit16_eq_getLsbD yv i hi]

theorem truncate32_xor (a b : BitVec 64) :
    BitVec.truncate 32 (a ^^^ b) = BitVec.truncate 32 a ^^^ BitVec.truncate 32 b := by
  bv_slice

theorem polyMul_term_15 (cv yv : BitVec 16) :
    BitVec.truncate 32
      (if ConditionHolds CondCode.GT (addsPState32 (BitVec.signExtend 32 yv) 1#32) = true then 0#64
       else BitVec.truncate 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 cv <<< 15))) =
    pmTerm cv yv 15 := by
  dsimp only [pmTerm]
  rw [adds_sxth_one_gt]
  generalize yv.getLsbD 15 = b
  cases b <;> bv_slice

theorem polyMul_term_0_aux (cv yv : BitVec 16) :
    BitVec.truncate 32
      ((if yv.getLsbD 0 = true then 4294967295#64 else 0#64) &&& BitVec.zeroExtend 64 cv) =
    pmTerm cv yv 0 := by
  dsimp only [pmTerm]
  generalize yv.getLsbD 0 = b
  cases b <;> bv_slice

theorem polyMul_term_low_aux (cv yv : BitVec 16) (i : Nat) :
    BitVec.truncate 32
      ((if yv.getLsbD i = true then 4294967295#64 else 0#64) &&&
        BitVec.zeroExtend 64 (BitVec.zeroExtend 32 cv <<< i)) =
    pmTerm cv yv i := by
  dsimp only [pmTerm]
  generalize yv.getLsbD i = b
  cases b <;> bv_slice

theorem polyMul_term_6_9 (cv yv : BitVec 16) (i : Nat) (hi : i < 16) :
    BitVec.truncate 32 (sbfxMask64 yv i) &&& (BitVec.zeroExtend 32 cv <<< i) =
      pmTerm cv yv i := by
  dsimp only [pmTerm]
  rw [truncate32_sbfxMask64 yv i hi, BitVec.and_comm]

theorem polyMul_term_10_14 (cv yv : BitVec 16) (i : Nat) (hi : i < 16) :
    sbfxMask32 yv i &&& (BitVec.zeroExtend 32 cv <<< i) =
      pmTerm cv yv i := by
  dsimp only [pmTerm]
  rw [sbfxMask32_eq yv i hi, BitVec.and_comm]

attribute [local irreducible] pmTerm in
theorem unaccelerated_polyMul_eq_pmTerms (cv yv : BitVec 16) :
    unaccelerated.polyMul cv yv =
      pmTerm cv yv 0 ^^^ pmTerm cv yv 1 ^^^ pmTerm cv yv 2 ^^^ pmTerm cv yv 3 ^^^
      pmTerm cv yv 4 ^^^ pmTerm cv yv 5 ^^^ pmTerm cv yv 6 ^^^ pmTerm cv yv 7 ^^^
      pmTerm cv yv 8 ^^^ pmTerm cv yv 9 ^^^ pmTerm cv yv 10 ^^^ pmTerm cv yv 11 ^^^
      pmTerm cv yv 12 ^^^ pmTerm cv yv 13 ^^^ pmTerm cv yv 14 ^^^ pmTerm cv yv 15 := by
  simp only [unaccelerated.polyMul, unaccelerated.polyMulLoop,
    ite_xor_eq_xor_and_mask, Nat.reduceAdd, BitVec.zero_xor,
    pmTerm_rhs_0 cv yv, pmTerm_rhs cv yv 1 (by decide),
    pmTerm_rhs cv yv 2 (by decide), pmTerm_rhs cv yv 3 (by decide),
    pmTerm_rhs cv yv 4 (by decide), pmTerm_rhs cv yv 5 (by decide),
    pmTerm_rhs cv yv 6 (by decide), pmTerm_rhs cv yv 7 (by decide),
    pmTerm_rhs cv yv 8 (by decide), pmTerm_rhs cv yv 9 (by decide),
    pmTerm_rhs cv yv 10 (by decide), pmTerm_rhs cv yv 11 (by decide),
    pmTerm_rhs cv yv 12 (by decide), pmTerm_rhs cv yv 13 (by decide),
    pmTerm_rhs cv yv 14 (by decide), pmTerm_rhs cv yv 15 (by decide)]

attribute [local irreducible] pmTerm in
theorem prepare_polyMul_asm_eq (cv yv : BitVec 16) :
    BitVec.zeroExtend 64
      (BitVec.truncate 32
                ((if ConditionHolds CondCode.GT (addsPState32 (BitVec.signExtend 32 yv) 1#32) = true then 0#64
                  else BitVec.truncate 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 cv <<< 15))) ^^^
                  BitVec.zeroExtend 64
                    (BitVec.truncate 32
                        ((if (BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)).getLsbD 0 = true then
                            4294967295#64
                          else 0#64) &&&
                          BitVec.zeroExtend 64 cv) ^^^
                      BitVec.truncate 32
                        ((if (BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)).getLsbD 1 = true then
                            4294967295#64
                          else 0#64) &&&
                          BitVec.zeroExtend 64 (BitVec.zeroExtend 32 cv <<< 1)))) ^^^
              (BitVec.truncate 32
                    ((if (BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)).getLsbD 2 = true then 4294967295#64
                      else 0#64) &&&
                      BitVec.zeroExtend 64 (BitVec.zeroExtend 32 cv <<< 2)) ^^^
                  BitVec.truncate 32
                    ((if (BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)).getLsbD 3 = true then 4294967295#64
                      else 0#64) &&&
                      BitVec.zeroExtend 64 (BitVec.zeroExtend 32 cv <<< 3)) ^^^
                BitVec.truncate 32
                  ((if (BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)).getLsbD 4 = true then 4294967295#64
                    else 0#64) &&&
                    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 cv <<< 4))) ^^^
            (BitVec.truncate 32
                    ((if (BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)).getLsbD 5 = true then 4294967295#64
                      else 0#64) &&&
                      BitVec.zeroExtend 64 (BitVec.zeroExtend 32 cv <<< 5)) ^^^
                  BitVec.truncate 32 (sbfxMask64 yv 6) &&& BitVec.zeroExtend 32 cv <<< 6 ^^^
                BitVec.truncate 32 (sbfxMask64 yv 7) &&& BitVec.zeroExtend 32 cv <<< 7 ^^^
              BitVec.truncate 32 (sbfxMask64 yv 8) &&& BitVec.zeroExtend 32 cv <<< 8) ^^^
          (BitVec.truncate 32 (sbfxMask64 yv 9) &&& BitVec.zeroExtend 32 cv <<< 9 ^^^
                  sbfxMask32 yv 10 &&& BitVec.zeroExtend 32 cv <<< 10 ^^^
                sbfxMask32 yv 11 &&& BitVec.zeroExtend 32 cv <<< 11 ^^^
              sbfxMask32 yv 12 &&& BitVec.zeroExtend 32 cv <<< 12 ^^^
            sbfxMask32 yv 13 &&& BitVec.zeroExtend 32 cv <<< 13) ^^^
        sbfxMask32 yv 14 &&& BitVec.zeroExtend 32 cv <<< 14) =
      BitVec.zeroExtend 64 (unaccelerated.polyMul cv yv) := by
  have hget : ∀ i, i < 16 → (BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)).getLsbD i = yv.getLsbD i :=
    sxth32Zext64_getLsbD yv
  rw [unaccelerated_polyMul_eq_pmTerms]
  simp only [truncate32_xor, truncate32_zext64,
    hget 0 (by decide), hget 1 (by decide), hget 2 (by decide),
    hget 3 (by decide), hget 4 (by decide), hget 5 (by decide),
    polyMul_term_15, polyMul_term_0_aux, polyMul_term_low_aux,
    polyMul_term_6_9 cv yv 6 (by decide), polyMul_term_6_9 cv yv 7 (by decide),
    polyMul_term_6_9 cv yv 8 (by decide), polyMul_term_6_9 cv yv 9 (by decide),
    polyMul_term_10_14 cv yv 10 (by decide), polyMul_term_10_14 cv yv 11 (by decide),
    polyMul_term_10_14 cv yv 12 (by decide), polyMul_term_10_14 cv yv 13 (by decide),
    polyMul_term_10_14 cv yv 14 (by decide)]
  congr 1
  ac_rfl

theorem ptr_add_two_of_pos (ptr : BitVec 64) {k : Nat} (hk : 1 ≤ k) :
    ptr + BitVec.ofNat 64 (2 * (k - 1)) + 2#64 = ptr + BitVec.ofNat 64 (2 * k) := by
  rw [BitVec.add_assoc, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add]
  congr 2; omega

set_option maxHeartbeats 1600000 in
theorem innerPolyMul_sepWP
    (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (sp0 ptr : BitVec 64) (hptr_al : ptr &&& 1#64 = 0#64)
    (k : Nat) (hk1 : 1 ≤ k)
    (cv yv : BitVec 16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName + 212#64)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = sbfxMask64 yv 6)
    (hx22 : s.readReg64 .x22 = sbfxMask64 yv 7)
    (hx24 : s.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * (k - 1)))
    (hx25 : s.readReg64 .x25 = sxth32Zext64 yv)
    (hx26 : s.readReg64 .x26 = sbfxMask64 yv 8)
    (hx28 : s.readReg64 .x28 = sbfxMask64 yv 9)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName + 508#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x8 = BitVec.zeroExtend 64 (unaccelerated.polyMul cv yv) →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = sbfxMask64 yv 6 →
      sf.readReg64 .x22 = sbfxMask64 yv 7 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x25 = sxth32Zext64 yv →
      sf.readReg64 .x26 = sbfxMask64 yv 8 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = sbfxMask64 yv 9 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc sf
        (tokenInitAt b ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
         ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ cv) ∗ F) Q) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc s
      (tokenInitAt b ∗
       ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
       ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
       ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
       ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
       ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
       ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ cv) ∗ F) Q := by
  have hfn : libsignalSessionCode.fnOff lagrangePrepareName = 0x5c824 := lagrangePrepare_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode lagrangePrepareBin b
    (Rust.withPanics ext) hfn 0x5c824 0xd4 296
  clear hfn
  have hadrp1 := fnAddr_adrp_61cf0 (H := Rust.withPanics ext) hb
  have hadrp2 := fnAddr_adrp_61d04 (H := Rust.withPanics ext) hb
  have halign_bd8 := aligned_86bd8 b hb
  have hptr_step := ptr_add_two_of_pos ptr hk1
  have hal_k := aligned16_add_mul_two ptr hptr_al k
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName = entry
  examples_hide_fetches
  wp_simp_pre [tokenInitAt]
  wp_steps 3
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_assumption
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign_bd8
  · wp_sep_access
  · wp_norm_lhs
  wp_steps 5
  apply SepWP.fold (tokenInitAt_fold b) (by sep_focus)
  wp_steps 42
  apply hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
  · simp only [arm64_norm, wp_norm]
    exact prepare_polyMul_asm_eq cv yv
  · wp_norm_lhs
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hx21
  · simpa [arm64_norm, wp_norm] using hx22
  · wp_norm_lhs
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hx25
  · simpa [arm64_norm, wp_norm] using hx26
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hx28
  · simpa [arm64_norm, wp_norm] using hx29
  · wp_norm_lhs

set_option maxHeartbeats 1600000 in
theorem innerStep_sepWP
    (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (sp0 ptr : BitVec 64) (hptr_al : ptr &&& 1#64 = 0#64)
    (n : Nat) (hn_bound : n + 1 < 2 ^ 63)
    (yv : BitVec 16)
    (rem' k : Nat) (cs : List GF16)
    (hk1 : 1 ≤ k) (hk_rem : k + rem' = n) (hcs_len : cs.length = n + 1)
    (hk : k < cs.length) (hk_prev : k - 1 < cs.length)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName + 212#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * (k - 1)))
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx21 : s.readReg64 .x21 = sbfxMask64 yv 6)
    (hx22 : s.readReg64 .x22 = sbfxMask64 yv 7)
    (hx23 : s.readReg64 .x23 = b + bv% (ls_bytes% "00000b1016201d302c402750"))
    (hx24 : s.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * (k - 1)))
    (hx25 : s.readReg64 .x25 = sxth32Zext64 yv)
    (hx26 : s.readReg64 .x26 = sbfxMask64 yv 8)
    (hx27 : s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (rem' + 1))
    (hx28 : s.readReg64 .x28 = sbfxMask64 yv 9)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName + 564#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.pstate = addsPState64 (0#64 - BitVec.ofNat 64 (rem' + 1)) 1#64 →
      sf.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x20 = BitVec.ofNat 64 n →
      sf.readReg64 .x21 = sbfxMask64 yv 6 →
      sf.readReg64 .x22 = sbfxMask64 yv 7 →
      sf.readReg64 .x23 = b + bv% (ls_bytes% "00000b1016201d302c402750") →
      sf.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x25 = sxth32Zext64 yv →
      sf.readReg64 .x26 = sbfxMask64 yv 8 →
      sf.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (rem' + 1) + 1#64 →
      sf.readReg64 .x28 = sbfxMask64 yv 9 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc sf
        (tokenInitAt b ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
         gf16SliceAt ptr
           (cs.set (k - 1) ⟨(cs[k - 1]'hk_prev).value ^^^ unaccelerated.mul (cs[k]'hk).value yv⟩) ∗
         reduceTableAt b ∗ F) Q) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc s
      (tokenInitAt b ∗
       ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
       ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
       ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
       ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
       ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
       gf16SliceAt ptr cs ∗
       reduceTableAt b ∗ F) Q := by
  wp_conv_pre =>
    rw [gf16SliceAt_focus_assoc hk ptr]
  apply innerPolyMul_sepWP b ext hb sp0 ptr hptr_al k hk1 (cs[k]'hk).value yv ret_pc Q s
    (gf16SliceRest ptr cs k ∗ reduceTableAt b ∗ F)
    hpc hrun hx21 hx22 hx24 hx25 hx26 hx28 hx29
  intro s1 hpc1 hrun1 hsp1 htrace1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
  rw [hx19] at hx19_1
  rw [hx20] at hx20_1
  rw [hx23] at hx23_1
  rw [hx27] at hx27_1
  have hfn : libsignalSessionCode.fnOff lagrangePrepareName = 0x5c824 := lagrangePrepare_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode lagrangePrepareBin b
    (Rust.withPanics ext) hfn 0x5c824 0x1fc 56
  clear hfn
  have hadd_k := add_neg_rem_eq_k_prev hk1 hk_rem
  have hcmn := cmn_k_prev_ne_zero hk1 (by omega)
  have hal_prev := aligned16_add_mul_two ptr hptr_al (k - 1)
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [← gf16SliceAt_focus_assoc hk ptr, gf16SliceAt_focus_assoc hk_prev ptr]
  wp_steps 6
  wp_conv_pre =>
    rw [reduceTableAt_focus16 b (BitVec.truncate 8 (unaccelerated.polyMul (cs[k]'hk).value yv >>> 24)),
        uxtw1_idx1_eq (unaccelerated.polyMul (cs[k]'hk).value yv)]
  wp_steps 4
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (unaccelerated.polyMul (cs[k]'hk).value yv),
        ← reduceTableAt_focus16 b (BitVec.truncate 8 (unaccelerated.polyMul (cs[k]'hk).value yv >>> 24)),
        reduceTableAt_focus16 b
          (BitVec.truncate 8
            ((unaccelerated.polyMul (cs[k]'hk).value yv ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul (cs[k]'hk).value yv >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 4
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTableAt_focus16 b
          (BitVec.truncate 8
            ((unaccelerated.polyMul (cs[k]'hk).value yv ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul (cs[k]'hk).value yv >>> 24))) <<<
                  8) >>>
              16)),
        gf16SliceAt_update_assoc hk_prev ptr]
  apply hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
    (by simpa [arm64_norm, wp_norm] using htrace1) (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx20_1) (by simpa [arm64_norm, wp_norm] using hx21_1)
    (by simpa [arm64_norm, wp_norm] using hx22_1) (by simpa [arm64_norm, wp_norm] using hx23_1)
    (by simpa [arm64_norm, wp_norm] using hx24_1) (by simpa [arm64_norm, wp_norm] using hx25_1)
    (by simpa [arm64_norm, wp_norm] using hx26_1) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx28_1) (by simpa [arm64_norm, wp_norm] using hx29_1)
    (by simpa [arm64_norm, wp_norm] using hvregs1)

/-! ## Relocatable `[LibsignalPlacement]` Inner Loop Helpers (Block `372`) -/

set_option maxHeartbeats 1600000 in
theorem innerPolyMul_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (sp0 ptr : BitVec 64) (hptr_al : ptr &&& 1#64 = 0#64)
    (k : Nat) (hk1 : 1 ≤ k)
    (cv yv : BitVec 16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hpc : s.pc = (blkPl_372).base + 212#64)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = sbfxMask64 yv 6)
    (hx22 : s.readReg64 .x22 = sbfxMask64 yv 7)
    (hx24 : s.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * (k - 1)))
    (hx25 : s.readReg64 .x25 = sxth32Zext64 yv)
    (hx26 : s.readReg64 .x26 = sbfxMask64 yv 8)
    (hx28 : s.readReg64 .x28 = sbfxMask64 yv 9)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_372).base + 508#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x8 = BitVec.zeroExtend 64 (unaccelerated.polyMul cv yv) →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = sbfxMask64 yv 6 →
      sf.readReg64 .x22 = sbfxMask64 yv 7 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x25 = sxth32Zext64 yv →
      sf.readReg64 .x26 = sbfxMask64 yv 8 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = sbfxMask64 yv 9 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc sf
        (tokenInitPlacedAt ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
         ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ cv) ∗ F) Q) :
    SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc s
      (tokenInitPlacedAt ∗
       ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
       ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
       ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
       ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
       ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
       ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ cv) ∗ F) Q := by
  have halign_bd8 := aligned_tokenOnce_placed
  have hptr_step := ptr_add_two_of_pos ptr hk1
  have hal_k := aligned16_add_mul_two ptr hptr_al k
  wp_simp_pre [tokenInitPlacedAt]
  wp_steps 3
  apply step_ldar32 (by wp_norm_lhs) (by wp_norm_lhs)
    (blkPC_372_rebase_fetch_0xe0 (blkPl_372).base (Rust.withPanics ext))
    (by wp_norm_lhs) (by wp_norm_lhs) halign_bd8 (by wp_sep_access) (by wp_norm_lhs)
  wp_steps 6
  apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
  wp_steps 42
  apply hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
  · simp only [arm64_norm, wp_norm]; exact prepare_polyMul_asm_eq cv yv
  · wp_norm_lhs
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hx21
  · simpa [arm64_norm, wp_norm] using hx22
  · wp_norm_lhs
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hx25
  · simpa [arm64_norm, wp_norm] using hx26
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hx28
  · simpa [arm64_norm, wp_norm] using hx29
  · wp_norm_lhs

set_option maxHeartbeats 1600000 in
theorem innerStep_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (sp0 ptr : BitVec 64) (hptr_al : ptr &&& 1#64 = 0#64)
    (n : Nat) (hn_bound : n + 1 < 2 ^ 63)
    (yv : BitVec 16)
    (rem' k : Nat) (cs : List GF16)
    (hk1 : 1 ≤ k) (hk_rem : k + rem' = n) (hcs_len : cs.length = n + 1)
    (hk : k < cs.length) (hk_prev : k - 1 < cs.length)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hpc : s.pc = (blkPl_372).base + 212#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * (k - 1)))
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx21 : s.readReg64 .x21 = sbfxMask64 yv 6)
    (hx22 : s.readReg64 .x22 = sbfxMask64 yv 7)
    (hx23 : s.readReg64 .x23 = lsρ reduceTableSym)
    (hx24 : s.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * (k - 1)))
    (hx25 : s.readReg64 .x25 = sxth32Zext64 yv)
    (hx26 : s.readReg64 .x26 = sbfxMask64 yv 8)
    (hx27 : s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (rem' + 1))
    (hx28 : s.readReg64 .x28 = sbfxMask64 yv 9)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_372).base + 564#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.pstate = addsPState64 (0#64 - BitVec.ofNat 64 (rem' + 1)) 1#64 →
      sf.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x20 = BitVec.ofNat 64 n →
      sf.readReg64 .x21 = sbfxMask64 yv 6 →
      sf.readReg64 .x22 = sbfxMask64 yv 7 →
      sf.readReg64 .x23 = lsρ reduceTableSym →
      sf.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x25 = sxth32Zext64 yv →
      sf.readReg64 .x26 = sbfxMask64 yv 8 →
      sf.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (rem' + 1) + 1#64 →
      sf.readReg64 .x28 = sbfxMask64 yv 9 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc sf
        (tokenInitPlacedAt ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
         gf16SliceAt ptr
           (cs.set (k - 1) ⟨(cs[k - 1]'hk_prev).value ^^^ unaccelerated.mul (cs[k]'hk).value yv⟩) ∗
         reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc s
      (tokenInitPlacedAt ∗
       ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
       ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
       ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
       ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
       ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
       gf16SliceAt ptr cs ∗
       reduceTablePlacedAt ∗ F) Q := by
  wp_conv_pre => rw [gf16SliceAt_focus_assoc hk ptr]
  apply innerPolyMul_placed_sepWP ext sp0 ptr hptr_al k hk1 (cs[k]'hk).value yv ret_pc Q s
    (gf16SliceRest ptr cs k ∗ reduceTablePlacedAt ∗ F)
    hpc hrun hx21 hx22 hx24 hx25 hx26 hx28 hx29
  intro s1 hpc1 hrun1 hsp1 htrace1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx23] at hx23_1; rw [hx27] at hx27_1
  have hadd_k := add_neg_rem_eq_k_prev hk1 hk_rem
  have hcmn := cmn_k_prev_ne_zero hk1 (by omega)
  have hal_prev := aligned16_add_mul_two ptr hptr_al (k - 1)
  wp_conv_pre => rw [← gf16SliceAt_focus_assoc hk ptr, gf16SliceAt_focus_assoc hk_prev ptr]
  wp_steps 6
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul (cs[k]'hk).value yv >>> 24)),
        uxtw1_idx1_eq (unaccelerated.polyMul (cs[k]'hk).value yv)]
  wp_steps 4
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (unaccelerated.polyMul (cs[k]'hk).value yv),
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul (cs[k]'hk).value yv >>> 24)),
        reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul (cs[k]'hk).value yv ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul (cs[k]'hk).value yv >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 4
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul (cs[k]'hk).value yv ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul (cs[k]'hk).value yv >>> 24))) <<<
                  8) >>>
              16)),
        gf16SliceAt_update_assoc hk_prev ptr]
  apply hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
    (by simpa [arm64_norm, wp_norm] using htrace1) (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx20_1) (by simpa [arm64_norm, wp_norm] using hx21_1)
    (by simpa [arm64_norm, wp_norm] using hx22_1) (by simpa [arm64_norm, wp_norm] using hx23_1)
    (by simpa [arm64_norm, wp_norm] using hx24_1) (by simpa [arm64_norm, wp_norm] using hx25_1)
    (by simpa [arm64_norm, wp_norm] using hx26_1) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx28_1) (by simpa [arm64_norm, wp_norm] using hx29_1)
    (by simpa [arm64_norm, wp_norm] using hvregs1)

set_option maxHeartbeats 1600000 in
theorem innerLoop_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (sp0 ptr : BitVec 64) (hptr_al : ptr &&& 1#64 = 0#64)
    (n : Nat) (hn_bound : n + 1 < 2 ^ 63)
    (yv : BitVec 16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (rem' k : Nat) (cs : List GF16)
      (_hk1 : 1 ≤ k) (_hk_rem : k + rem' = n) (_hcs_len : cs.length = n + 1)
      (s : State) (F : SepProp),
      s.pc = (blkPl_372).base + 212#64 →
      s.status = .Running →
      s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * (k - 1)) →
      s.readReg64 .x20 = BitVec.ofNat 64 n →
      s.readReg64 .x21 = sbfxMask64 yv 6 →
      s.readReg64 .x22 = sbfxMask64 yv 7 →
      s.readReg64 .x23 = lsρ reduceTableSym →
      s.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * (k - 1)) →
      s.readReg64 .x25 = sxth32Zext64 yv →
      s.readReg64 .x26 = sbfxMask64 yv 8 →
      s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (rem' + 1) →
      s.readReg64 .x28 = sbfxMask64 yv 9 →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ sf : State,
        sf.pc = (blkPl_372).base + 568#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        sf.trace = s.trace →
        sf.readReg64 .x20 = BitVec.ofNat 64 n →
        sf.readReg64 .x23 = lsρ reduceTableSym →
        sf.readReg64 .x29 = sp0 - 96#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc sf
          (tokenInitPlacedAt ∗
           ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
           ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
           ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
           ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
           ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
           gf16SliceAt ptr (multXdiffLoopPure ⟨yv⟩ k (rem' + 1) cs) ∗
           reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc s
        (tokenInitPlacedAt ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
         gf16SliceAt ptr cs ∗
         reduceTablePlacedAt ∗ F) Q := by
  intro rem'
  induction rem' with
  | zero =>
    intro k cs hk1 hk_rem hcs_len s F hpc hrun hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hnext
    have hk : k < cs.length := by omega
    have hk_prev : k - 1 < cs.length := by omega
    apply innerStep_placed_sepWP ext sp0 ptr hptr_al n hn_bound yv 0 k cs hk1 hk_rem hcs_len hk hk_prev
      ret_pc Q s F hpc hrun hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    intro s1 hpc1 hrun1 hsp1 htrace1 hpstate1 _hx19_1 hx20_1 _hx21_1 _hx22_1 hx23_1 _hx24_1 _hx25_1 _hx26_1 _hx27_1 _hx28_1 hx29_1 hvregs1
    have hcarry := adds_neg_one_carry
    wp_steps 1
    rw [multXdiffLoopPure_succ yv k 0 cs hk hk_prev] at hnext
    exact hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htrace1) (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1) (by simpa [arm64_norm, wp_norm] using hx29_1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r ih =>
    intro k cs hk1 hk_rem hcs_len s F hpc hrun hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hnext
    have hk : k < cs.length := by omega
    have hk_prev : k - 1 < cs.length := by omega
    apply innerStep_placed_sepWP ext sp0 ptr hptr_al n hn_bound yv (r + 1) k cs hk1 hk_rem hcs_len hk hk_prev
      ret_pc Q s F hpc hrun hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    intro s1 hpc1 hrun1 hsp1 htrace1 hpstate1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
    have hcarry := neg_succ_ule_add_one (r := r) (by omega)
    wp_steps 1
    apply ih (k + 1)
      (cs.set (k - 1) ⟨(cs[k - 1]'hk_prev).value ^^^ unaccelerated.mul (cs[k]'hk).value yv⟩)
      (by omega) (by omega) (by simp [List.length_set, hcs_len]) _ F
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx21_1)
      (by simpa [arm64_norm, wp_norm] using hx22_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx24_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx26_1)
      (by simpa [arm64_norm, wp_norm, neg_succ_add_one (r + 1)] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx28_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
    intro sf hpc_f hrun_f hsp_f htrace_f hx20_f hx23_f hx29_f hvregs_f
    rw [multXdiffLoopPure_succ yv k (r + 1) cs hk hk_prev] at hnext
    exact hnext sf hpc_f hrun_f
      (by rw [hsp_f]; simpa [arm64_norm, wp_norm] using hsp1)
      (by rw [htrace_f]; simpa [arm64_norm, wp_norm] using htrace1)
      hx20_f hx23_f hx29_f
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)


end CryptoVerification.SpqrV1.Poly.LagrangePrepare
