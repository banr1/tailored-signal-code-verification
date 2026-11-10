/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFull
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof -- shake: keep

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: Main Loop

**Checked by Lean.**

Proves the evaluation and interpolation loop (`0x6bda4..0x6c0fc`, `+548..+1404`) of
`decoded_message` (`decodedMessageLoop_wpp`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecodedMessage

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (lagrangePrepareName lagrangePrepare_fnOff LagrangePrepareArgs lagrangePrepareSpec
   lagrangePreparePlacedSpec lagrangePreparePure lagrangePreparePure_length
   lagrangePrepareStack lagrangePrepare_ok lagrangePrepare_placed_ok polyOf_eq)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  AddChunkNorm.sp_setPC_pre AddChunkNorm.sp_setMem_setPC_pre
  AddChunkNorm.readReg64_setPC_pre AddChunkNorm.readReg64_setMem_setPC_pre
  AddChunkNorm.readReg32_setPC_pre AddChunkNorm.readReg32_setMem_setPC_pre
  AddChunkNorm.readReg_setPC_pre AddChunkNorm.readReg_setMem_setPC_pre

/-! ## Pure Characterizations of `decodedMessageLoopTotal` Steps -/

theorem collectedSlices_getD_eq_take (self : PolyDecoder) (hpts : self.pts.length = 16)
    {k : Nat} (hk : k < 16) :
    (collectedSlices self 0 16)[k]?.getD [] =
      (self.pts[k]'(by omega)).vec.take (self.necessaryPoints k) := by
  have hk_len : k < (collectedSlices self 0 16).length := by
    rw [collectedSlices_length]; exact hk
  have hk_pts : k < self.pts.length := by omega
  rw [List.getElem?_eq_getElem hk_len, Option.getD_some,
    collectedSlices_getElem self 16 0 k hk, Nat.zero_add,
    List.getElem?_eq_getElem hk_pts, Option.getD_some]

theorem decodedMessageLoopTotal_step_found (self : PolyDecoder) (hpts : self.pts.length = 16)
    (hsort : PolyDecoderStrictSorted self)
    {i rem : Nat} {polys : List (Option Poly)} {out : List (BitVec 8)}
    {bIdx : Nat}
    (hb_eq : bIdx = bsearchLoop (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec
      (BitVec.ofNat 16 (i / 16)) 0
      (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hb_lt : bIdx < (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hfound : (((self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec[bIdx]'hb_lt).x.value ==
      BitVec.ofNat 16 (i / 16)) = true) :
    decodedMessageLoopTotal self (collectedSlices self 0 16) i (rem + 1) polys out =
      decodedMessageLoopTotal self (collectedSlices self 0 16) (i + 1) rem polys
        (out ++ u16ToBeBytes
          ((self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec[bIdx]'hb_lt).y.value) := by
  have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
  have hpoly_pts : i % 16 < self.pts.length := by omega
  have hget_pts : self.pts[i % 16]?.getD SortedSetPt.new = self.pts[i % 16]'hpoly_pts := by
    rw [List.getElem?_eq_getElem hpoly_pts, Option.getD_some]
  have hs_sort : SortedSetPtStrictSorted (self.pts[i % 16]'hpoly_pts) :=
    hsort (self.pts[i % 16]'hpoly_pts) (List.getElem_mem hpoly_pts)
  have hs_ne : (self.pts[i % 16]'hpoly_pts).vec ≠ [] :=
    List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hb_lt)
  have hbs := bsearchLoop_eq_binarySearch (self.pts[i % 16]'hpoly_pts)
    { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO } hs_sort hs_ne hb_eq hb_lt
  change (if ((self.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt).x.value == BitVec.ofNat 16 (i / 16) then _ else _) at hbs
  simp only [hfound, ite_true] at hbs
  have hget_b : (self.pts[i % 16]'hpoly_pts).vec[bIdx]?.getD { x := GF16.ZERO, y := GF16.ZERO } =
      (self.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt := by
    rw [List.getElem?_eq_getElem hb_lt, Option.getD_some]
  conv_lhs => rw [decodedMessageLoopTotal]
  simp only [hget_pts, hbs, hget_b]

theorem decodedMessageLoopTotal_step_not_found (self : PolyDecoder) (hpts : self.pts.length = 16)
    (hsort : PolyDecoderStrictSorted self)
    {i rem : Nat} {polys : List (Option Poly)} {out : List (BitVec 8)}
    (hpolys : polys.length = 16)
    {bIdx : Nat}
    (hb_eq : bIdx = bsearchLoop (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec
      (BitVec.ofNat 16 (i / 16)) 0
      (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hb_lt : bIdx < (self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hnot_found : (((self.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec[bIdx]'hb_lt).x.value ==
      BitVec.ofNat 16 (i / 16)) = false) :
    let poly := i % 16
    let hpoly_pts : poly < self.pts.length := by have := Nat.mod_lt i (by decide : 0 < 16); omega
    let hpoly_p : poly < polys.length := by have := Nat.mod_lt i (by decide : 0 < 16); omega
    let ptsSlice := (self.pts[poly]'hpoly_pts).vec.take (self.necessaryPoints poly)
    let p := (polys[poly]'hpoly_p).getD (lagrangeInterpolateTotal ptsSlice)
    let y := computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))
    decodedMessageLoopTotal self (collectedSlices self 0 16) i (rem + 1) polys out =
      decodedMessageLoopTotal self (collectedSlices self 0 16) (i + 1) rem
        (polys.set poly (some p)) (out ++ u16ToBeBytes y.value) := by
  have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
  have hpoly_pts : i % 16 < self.pts.length := by omega
  have hpoly_p : i % 16 < polys.length := by omega
  have hget_pts : self.pts[i % 16]?.getD SortedSetPt.new = self.pts[i % 16]'hpoly_pts := by
    rw [List.getElem?_eq_getElem hpoly_pts, Option.getD_some]
  have hs_sort : SortedSetPtStrictSorted (self.pts[i % 16]'hpoly_pts) :=
    hsort (self.pts[i % 16]'hpoly_pts) (List.getElem_mem hpoly_pts)
  have hs_ne : (self.pts[i % 16]'hpoly_pts).vec ≠ [] :=
    List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hb_lt)
  have hbs := bsearchLoop_eq_binarySearch (self.pts[i % 16]'hpoly_pts)
    { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO } hs_sort hs_ne hb_eq hb_lt
  change (if ((self.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt).x.value == BitVec.ofNat 16 (i / 16) then _ else _) at hbs
  simp only [hnot_found, Bool.false_eq_true, ite_false] at hbs
  have hget_p : polys[i % 16]?.getD none = polys[i % 16]'hpoly_p := by
    rw [List.getElem?_eq_getElem hpoly_p, Option.getD_some]
  have hget_slice := collectedSlices_getD_eq_take self hpts hpoly_lt
  dsimp only
  conv_lhs => rw [decodedMessageLoopTotal]
  simp only [hget_pts, hbs, hget_p, hget_slice]
  cases hopt : polys[i % 16]'hpoly_p with
  | some p0 =>
    have hset_self : polys.set (i % 16) (some p0) = polys := by
      rw [← hopt, List.set_getElem_self]
    simp only [Option.getD_some, hset_self]
  | none =>
    simp only [Option.getD_none]

/-! ## Bitvector and Separation-Logic Helpers for the Main Loop -/

@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub120 (sp0 : BitVec 64) :
    sp0 - 96#64 + 18446744073709551496#64 = sp0 - 216#64 := by bv_omega

@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub112 (sp0 : BitVec 64) :
    sp0 - 96#64 + 18446744073709551504#64 = sp0 - 208#64 := by bv_omega

@[local wp_norm ↓, local arm64_norm ↓]
theorem sp96_sub104 (sp0 : BitVec 64) :
    sp0 - 96#64 + 18446744073709551512#64 = sp0 - 200#64 := by bv_omega

@[local wp_norm ↓, local arm64_norm ↓]
theorem bv64_and15_ofNat (i : Nat) :
    (BitVec.ofNat 64 i) &&& 15#64 = BitVec.ofNat 64 (i % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change (i % 18446744073709551616) &&& 15 = (i % 16) % 18446744073709551616
  have h1 : (i % 18446744073709551616) &&& 15 = (i % 18446744073709551616) % 16 :=
    Nat.and_two_pow_sub_one_eq_mod _ 4
  have h2 : (i % 18446744073709551616) % 16 = i % 16 :=
    Nat.mod_mod_of_dvd i (by decide)
  have h3 : (i % 16) % 18446744073709551616 = i % 16 :=
    Nat.mod_eq_of_lt (by have := Nat.mod_lt i (by decide : 0 < 16); omega)
  rw [h1, h2, h3]

@[local wp_norm ↓, local arm64_norm ↓]
theorem bv64_umaddl24_mod16 (base : BitVec 64) (i : Nat) :
    base + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (i % 16))) * 24#64 =
      base + BitVec.ofNat 64 (24 * (i % 16)) := by
  have hlt : i % 16 < 16 := Nat.mod_lt i (by decide)
  generalize i % 16 = m at hlt ⊢
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 m)) = BitVec.ofNat 64 m := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [h1, bv64_madd24_norm]

@[local wp_norm ↓, local arm64_norm ↓]
theorem bv64_ofNat_mul2_comm (n : Nat) :
    BitVec.ofNat 64 (n * 2) = BitVec.ofNat 64 (2 * n) := by
  rw [Nat.mul_comm]

@[local wp_norm ↓, local arm64_norm ↓]
theorem bv64_ofNat_one_add_mul2 (n : Nat) :
    BitVec.ofNat 64 (1 + 2 * n) = BitVec.ofNat 64 (2 * n + 1) := by
  rw [Nat.add_comm]

theorem bv64_lsr4_ofNat {i : Nat} (hi : i < 2 ^ 64) :
    (BitVec.ofNat 64 i) >>> 4 = BitVec.ofNat 64 (i / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem bv32_lsr4_zeroExtend_ofNat {i : Nat} (hi : i < 16 * 65536) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 i) >>> 4)) =
      BitVec.setWidth 64 (BitVec.ofNat 16 (i / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem bv64_lsr4_truncate16_ofNat {i : Nat} (hi : i < 16 * 65536) :
    BitVec.truncate 16 ((BitVec.ofNat 64 i) >>> 4) = BitVec.ofNat 16 (i / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem bv16_bne_zeroExtend32 (a b : BitVec 16) :
    (BitVec.zeroExtend 32 a != BitVec.zeroExtend 32 b) = !(a == b) := by
  by_cases h : a = b
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr h, Bool.not_false, bne_iff_ne]
    intro heq
    apply h
    apply BitVec.eq_of_toNat_eq
    have h1 := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_setWidth] at h1
    have ha := a.isLt
    have hb := b.isLt
    omega

theorem bv16_lsr8_zeroExtend64_truncate8 (y : BitVec 16) :
    BitVec.setWidth 8 (BitVec.setWidth 64 y >>> 8) =
      BitVec.setWidth 8 (y >>> 8) := by
  bv_bits

theorem bv16_zeroExtend64_truncate8 (y : BitVec 16) :
    BitVec.truncate 8 (BitVec.setWidth 64 y) = BitVec.truncate 8 y := by
  bv_bits

theorem bv64_ubfx_8_8_truncate8 {x0 : BitVec 64} {y : BitVec 16}
    (hy : BitVec.truncate 16 x0 = y) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) >>> 8 &&& 255#64) =
      BitVec.truncate 8 (y >>> 8) := by
  subst hy
  bv_bits

theorem bv64_orr_w0_truncate8 {x0 : BitVec 64} {y : BitVec 16}
    (hy : BitVec.truncate 16 x0 = y) :
    BitVec.zeroExtend 8 x0 = BitVec.truncate 8 y := by
  subst hy
  bv_bits

theorem bv64_bne_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, ne_eq, not_false_eq_true, decide_true, bne_iff_ne]
    intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hto
    exact h hto

theorem bv64_beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hto
    exact h hto

theorem stackAt_computeAt_eq_prepare (sp : BitVec 64) :
    stackAt sp computeAtStack =
      stackAt sp lagrangePrepareStack ∗ memRegion (sp - 4352#64) 48 := by
  unfold stackAt computeAtStack growOneStack finishGrowStack lagrangePrepareStack allocHookStack
  rw [show (144 + ((4128 + 16) + 64) : Nat) = 48 + (208 + 4096) from rfl,
    memRegion_split (sp - BitVec.ofNat 64 (48 + (208 + 4096))) 48 (208 + 4096) (by decide)]
  have haddr : sp - 4352#64 + 48#64 = sp - 4304#64 := by bv_omega
  rw [haddr, sepConj_comm]

theorem memRegion_two_eq_exists_bytes (a : BitVec 64) :
    memRegion a 2 =
      (∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1)) := by
  rw [show (2 : Nat) = 1 + 1 from rfl, memRegion_split a 1 1 (by decide),
    ProofLib.memRegion_one a, ProofLib.memRegion_one (a + 1#64)]
  apply sepProp_eq_of_entails
  · rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro b0
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro b1
    exact Entails.sepExists_right b0 (Entails.sepExists_right b1 (Entails.refl _))
  · apply Entails.sepExists_elim; intro b0
    apply Entails.sepExists_elim; intro b1
    exact sepConj_mono (Entails.sepExists_right b0 (Entails.refl _))
      (Entails.sepExists_right b1 (Entails.refl _))

theorem memRegion_out_split2 (out_ptr : BitVec 64) {i ptsNeeded : Nat}
    (hlt : i < ptsNeeded) (hbound : 2 * ptsNeeded < 2 ^ 64) :
    memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (ptsNeeded - i)) =
      (∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8,
        ((out_ptr + BitVec.ofNat 64 (2 * i)) ↦₈ b0) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i + 1)) ↦₈ b1)) ∗
      memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (2 * (ptsNeeded - (i + 1))) := by
  have hlen : 2 * (ptsNeeded - i) = 2 + 2 * (ptsNeeded - (i + 1)) := by omega
  have haddr1 : out_ptr + BitVec.ofNat 64 (2 * i) + 1#64 = out_ptr + BitVec.ofNat 64 (2 * i + 1) := by
    rw [BitVec.add_assoc, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have h2i2 : 2 * i + 2 = 2 * (i + 1) := by omega
  have haddr2 : out_ptr + BitVec.ofNat 64 (2 * i) + 2#64 = out_ptr + BitVec.ofNat 64 (2 * (i + 1)) := by
    rw [BitVec.add_assoc, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, h2i2]
  rw [hlen, memRegion_split (out_ptr + BitVec.ofNat 64 (2 * i)) 2 (2 * (ptsNeeded - (i + 1))) (by omega),
    haddr2, memRegion_two_eq_exists_bytes (out_ptr + BitVec.ofNat 64 (2 * i))]
  simp only [haddr1]

/-! ## Sub-Steps of One Iteration of `decodedMessageLoop` -/

/-- Step 1 of the main loop (`0x6bda4..0x6be10`, `entry + 548#64` to `entry + 1328#64` if found,
    or `entry + 660#64` if not found):
    Looks up `xVal = BitVec.ofNat 16 (i / 16)` in `dec.pts[i % 16]` via binary search. -/
theorem decodedMessage_bsearchStep_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (dec : PolyDecoder) (sp0 pts_base : BitVec 64) (pins : List VecPin) (i : Nat)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hi_lt : i < dec.ptsNeeded) (hneed_le : dec.ptsNeeded ≤ 16 * 65536)
    (hge_len : 1 ≤ (dec.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length)
    (hle_len : (dec.pts[i % 16]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).vec.length ≤ 65536)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 548#64)
    (hstat : s.status = .Running)
    (hx20 : s.readReg64 .x20 = pts_base)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (2 * i))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = sp0 - 600#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont_found :
      let poly := i % 16
      let hpoly_pts : poly < dec.pts.length := by have := Nat.mod_lt i (by decide : 0 < 16); omega
      let sPt := dec.pts[poly]'hpoly_pts
      let xVal := BitVec.ofNat 16 (i / 16)
      let bIdx := bsearchLoop sPt.vec xVal 0 sPt.vec.length
      ∀ (hb_lt : bIdx < sPt.vec.length),
        ((sPt.vec[bIdx]'hb_lt).x.value == xVal) = true →
        ∀ (sf : State),
          sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1328#64 →
          sf.status = .Running →
          sf.sp = s.sp →
          traceVRegs sf = traceVRegs s →
          BitVec.truncate 8 (sf.readReg64 .x19) = BitVec.truncate 8 ((sPt.vec[bIdx]'hb_lt).y.value >>> 8) →
          BitVec.truncate 8 (sf.readReg64 .x21) = BitVec.truncate 8 (sPt.vec[bIdx]'hb_lt).y.value →
          sf.readReg64 .x20 = pts_base →
          sf.readReg64 .x22 = BitVec.ofNat 64 i →
          sf.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
          sf.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded →
          sf.readReg64 .x25 = 24#64 →
          sf.readReg64 .x26 = sp0 - 600#64 →
          sf.readReg64 .x29 = sp0 - 96#64 →
          SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
            (sortedSetPtListPinAt A pts_base pins dec.pts ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P)
            post)
    (hcont_miss :
      let poly := i % 16
      let hpoly_pts : poly < dec.pts.length := by have := Nat.mod_lt i (by decide : 0 < 16); omega
      let sPt := dec.pts[poly]'hpoly_pts
      let xVal := BitVec.ofNat 16 (i / 16)
      let bIdx := bsearchLoop sPt.vec xVal 0 sPt.vec.length
      ∀ (hb_lt : bIdx < sPt.vec.length),
        ((sPt.vec[bIdx]'hb_lt).x.value == xVal) = false →
        ∀ (sf : State),
          sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 660#64 →
          sf.status = .Running →
          sf.sp = s.sp →
          traceVRegs sf = traceVRegs s →
          sf.readReg64 .x0 = BitVec.ofNat 64 poly →
          sf.readReg64 .x20 = pts_base →
          sf.readReg64 .x22 = BitVec.ofNat 64 i →
          sf.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded →
          sf.readReg64 .x25 = 24#64 →
          sf.readReg64 .x26 = sp0 - 600#64 →
          sf.readReg64 .x29 = sp0 - 96#64 →
          SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
            (sortedSetPtListPinAt A pts_base pins dec.pts ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P)
            post) :
    SepWP (tripleRatchetProgAtExt b ext) ret_pc s
      (sortedSetPtListPinAt A pts_base pins dec.pts ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P)
      post := by
  have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
  have hpoly_pts : i % 16 < dec.pts.length := by omega
  have hpoly_pins : i % 16 < pins.length := by omega
  have hbsearch := @bsearch_to_624_sepWP b ext ret_pc (pins[i % 16]'hpoly_pins).ptr
    (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) hge_len hle_len
  decodedMessageBin_fetches_range b (Rust.withPanics ext) 548 24
  decodedMessageBin_fetches_range b (Rust.withPanics ext) 624 36
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hbsearch hpc hcont_found hcont_miss ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  have hlen_ne0 : (BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length == 0#64) = false := by
    rw [bv64_beq_ofNat (by omega) (by decide), decide_eq_false_iff_not]; omega
  have hlsr4 := bv32_lsr4_zeroExtend_ofNat (show i < 16 * 65536 by omega)
  rw [sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
    sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
      (pts_base + BitVec.ofNat 64 (24 * (i % 16)))]
  wp_steps 6
  refine SepWP.weaken_pre
    (show _ ⊢
      ptSliceAt (pins[i % 16]'hpoly_pins).ptr (dec.pts[i % 16]'hpoly_pts).vec ∗
        (sortedSetPtListPinAt A pts_base (pins.take (i % 16)) (dec.pts.take (i % 16)) ∗
          ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
          ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄ (pins[i % 16]'hpoly_pins).ptr) ∗
          ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄
            BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
          sortedSetPtPinRest A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts) ∗
          sortedSetPtListPinAt A (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1)))
            (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P) by
      exact Entails.of_eq (by ac_rfl)) ?_
  refine hbsearch _ _ post
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hstat])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hlsr4])
    (by simp [wp_norm, arm64_norm])
    (fun s1 hpc1 hstat1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx29_1 _ => ?_)
  have ⟨_, hb_lt0⟩ := bsearchLoop_bounds (dec.pts[i % 16]'hpoly_pts).vec
    (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length hge_len (by omega)
  have hb_lt : bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0
      (dec.pts[i % 16]'hpoly_pts).vec.length < (dec.pts[i % 16]'hpoly_pts).vec.length := by
    omega
  have hx0_1' : s1.readReg64 .x0 = BitVec.ofNat 64 (i % 16) := by
    simpa [wp_norm, arm64_norm, hx22] using hx0_1
  have hx9_32 : s1.readReg32 .x9 = BitVec.zeroExtend 32 (BitVec.ofNat 16 (i / 16)) := by
    rw [State.readReg32, hx9_1]
    bv_bits
  have hx20_1' : s1.readReg64 .x20 = pts_base := by simpa [wp_norm, arm64_norm, hx20] using hx20_1
  have hx22_1' : s1.readReg64 .x22 = BitVec.ofNat 64 i := by simpa [wp_norm, arm64_norm, hx22] using hx22_1
  have hx23_1' : s1.readReg64 .x23 = BitVec.ofNat 64 (2 * i) := by simpa [wp_norm, arm64_norm, hx23] using hx23_1
  have hx24_1' : s1.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded := by simpa [wp_norm, arm64_norm, hx24] using hx24_1
  have hx25_1' : s1.readReg64 .x25 = 24#64 := by simpa [wp_norm, arm64_norm, hx25] using hx25_1
  have hx26_1' : s1.readReg64 .x26 = sp0 - 600#64 := by simpa [wp_norm, arm64_norm, hx26] using hx26_1
  have hx29_1' : s1.readReg64 .x29 = sp0 - 96#64 := by simpa [wp_norm, arm64_norm, hx29] using hx29_1
  let bIdx := bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0
    (dec.pts[i % 16]'hpoly_pts).vec.length
  rw [ptSliceAt_focus (dec.pts[i % 16]'hpoly_pts).vec bIdx (pins[i % 16]'hpoly_pins).ptr hb_lt]
  unfold ptAt
  wp_steps 3
  rw [bv16_bne_zeroExtend32 ((dec.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt).x.value (BitVec.ofNat 16 (i / 16))]
  cases hbeq : ((dec.pts[i % 16]'hpoly_pts).vec[bIdx]'hb_lt).x.value == BitVec.ofNat 16 (i / 16)
  · -- Not found (`hbeq = false`): branch at 0x6bdf8 IS taken to 0x6be14 (+660)
    simp only [Bool.not_false, ↓reduceIte]
    refine SepWP.weaken_pre
      (show _ ⊢
        (sortedSetPtListPinAt A pts_base pins dec.pts ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P) by
        rw [sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
          sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
            (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
          ptSliceAt_focus (dec.pts[i % 16]'hpoly_pts).vec bIdx (pins[i % 16]'hpoly_pins).ptr hb_lt]
        unfold ptAt
        exact Entails.of_eq (by ac_rfl)) ?_
    apply hcont_miss hb_lt hbeq
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hstat1]
    · simpa [wp_norm, arm64_norm] using hsp1
    · simpa [wp_norm, arm64_norm] using htr1
    · simp [wp_norm, arm64_norm, hx0_1']
    · simp [wp_norm, arm64_norm, hx20_1']
    · simp [wp_norm, arm64_norm, hx22_1']
    · simp [wp_norm, arm64_norm, hx24_1']
    · simp [wp_norm, arm64_norm, hx25_1']
    · simp [wp_norm, arm64_norm, hx26_1']
    · simp [wp_norm, arm64_norm, hx29_1']
  · -- Found (`hbeq = true`): branch at 0x6bdf8 NOT taken; steps 0x6bdfc..0x6be10 -> 0x6c0b0 (+1328)
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have h2i_ne : (BitVec.ofNat 64 (2 * i) == BitVec.ofNat 64 (2 * dec.ptsNeeded)) = false := by
      rw [bv64_beq_ofNat (by omega) (by omega), decide_eq_false_iff_not]; omega
    wp_steps 6
    refine SepWP.weaken_pre
      (show _ ⊢
        (sortedSetPtListPinAt A pts_base pins dec.pts ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗ P) by
        rw [sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
          sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
            (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
          ptSliceAt_focus (dec.pts[i % 16]'hpoly_pts).vec bIdx (pins[i % 16]'hpoly_pins).ptr hb_lt]
        unfold ptAt
        exact Entails.of_eq (by ac_rfl)) ?_
    apply hcont_found hb_lt hbeq
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hstat1]
    · simpa [wp_norm, arm64_norm] using hsp1
    · simpa [wp_norm, arm64_norm] using htr1
    · simp [wp_norm, arm64_norm, bv16_lsr8_zeroExtend64_truncate8]; rfl
    · simp [wp_norm, arm64_norm, bv16_zeroExtend64_truncate8]; rfl
    · simp [wp_norm, arm64_norm, hx20_1']
    · simp [wp_norm, arm64_norm, hx22_1']
    · simp [wp_norm, arm64_norm, hx23_1']
    · simp [wp_norm, arm64_norm, hx24_1']
    · simp [wp_norm, arm64_norm, hx25_1']
    · simp [wp_norm, arm64_norm, hx26_1']
    · simp [wp_norm, arm64_norm, hx29_1']

/-- Step 2b of the main loop (`0x6c084..0x6c0a4`, `entry + 1284#64` to `entry + 1328#64`):
    Loads `(ptr_p, len_p)` from `slot = (sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)`,
    evaluates `computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))` via `computeAt_ok` (`0x6c08c`),
    and prepares `w19`/`w21`/`x23` at `0x6c0b0 (+1328)`. -/
theorem decodedMessage_computeAtStep_wpp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hcomp_at : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName) (computeAtSpec A b))
    (sp0 slot : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (i ptsNeeded : Nat) (p : Poly)
    (hi_lt : i < ptsNeeded) (hneed_le : ptsNeeded ≤ 16 * 65536)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1284#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (htr : traceVRegs s = traceVRegs s0)
    (hx19 : s.readReg64 .x19 = slot)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1328#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 →
      BitVec.truncate 8 (sf.readReg64 .x19) =
        BitVec.truncate 8 ((computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value >>> 8) →
      BitVec.truncate 8 (sf.readReg64 .x21) =
        BitVec.truncate 8 (computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = BitVec.ofNat 64 i →
      sf.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        (optPolyCacheSlotAt A slot (some p) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (optPolyCacheSlotAt A slot (some p) ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
        reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
        stackAt (sp0 - 672#64) computeAtStack ∗ F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  have hca := sub_ok_at_backward hcomp_at decodedMessageName
    (num% (2 ^ 64 - ls_rel% "<spqr::encoding::polynomial::Poly>::compute_at"
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"))
    (by rw [decodedMessage_fnOff, computeAt_fnOff]; rfl)
  decodedMessageBin_fetches_range b (Rust.withPanics ext) 1284 40
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hca hpc hnext ⊢
  generalize_entry hentry : (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  have hslot16 : slot + 8#64 + 8#64 = slot + 16#64 := by bv_omega
  have h2i_ne : (BitVec.ofNat 64 (2 * i) != BitVec.ofNat 64 (2 * ptsNeeded)) = true := by
    rw [bv64_bne_ofNat (by omega) (by omega), decide_eq_true_eq]; omega
  unfold optPolyCacheSlotAt
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro ptr_p
  refine SepWPp.pure_elim_focus (1 ≤ p.coefficients.length ∧ p.coefficients.length ≤ 65536 ∧ ptr_p ≠ 0#64)
    (fun ⟨hp_ge1, hp_le, hptr_p_ne⟩ => ?_) (by sep_focus)
  apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 - ls_rel% "<spqr::encoding::polynomial::Poly>::compute_at"
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"))
  wp_steps 3
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
  let a : ComputeAtArgs := {
    p_coeffs := ptr_p
    poly := p
    x := GF16.new (BitVec.ofNat 16 (i / 16))
  }
  refine SepWPp.call (x := a) (ret_pc := entry + 1296#64)
    (F := (slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      ((slot + 8#64) ↦₆₄ ptr_p) ∗
      ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      A.live ptr_p (2 * p.coefficients.length) 2 ∗
      ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
      ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗ F)
    hca
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hstat])
    (by
      unfold State.spAligned
      simp only [wp_norm, arm64_norm, hsp, sp672_aligned sp0 hsp0])
    (by simp [wp_norm, arm64_norm])
    (fun R' hm => ?_)
    (fun sf code R' _ hex => ?_)
    (fun sf _ hm => ?_)
    (fun sf_c hpc_c hrun_c hsp_c hcs_c => ?_)
  · have hx2_trunc :
        BitVec.truncate 16 ((BitVec.ofNat 64 i) >>> 4) =
          (GF16.new (BitVec.ofNat 16 (i / 16))).value :=
      bv64_lsr4_truncate16_ofNat (by omega)
    simp only [computeAtSpec, a, wp_norm, arm64_norm, hsp, hslot16] at hm ⊢
    exact ⟨⟨hx2_trunc, by omega⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
  · simp only [computeAtSpec] at hex
    exact not_satisfies_false_sepConj hex
  · simp only [computeAtSpec] at hm
    exact allowPanic_frame (fun ⟨hal, hpre⟩ => by
      simp only [allocFailedIn, wp_norm, arm64_norm, htr_tr] at hal hpre ⊢
      exact ⟨hal, hpre⟩) hm
  · conv => arg 4; simp only [computeAtSpec, a, wp_norm, arm64_norm, htr_tr, hsp]
    rcases hcs_c with ⟨_, hx20_c, _, hx22_c, _, hx24_c, hx25_c, hx26_c, _, _, hx29_c, hvregs_c⟩
    refine SepWPp.pure_elim_focus (sf_c.trace = s0.trace ∧
      BitVec.truncate 16 (sf_c.readReg64 .x0) = (computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value)
      (fun ⟨htr_c, hx0_c⟩ => ?_) (by sep_focus)
    have hsp_c' : sf_c.sp = sp0 - 672#64 := by simpa [wp_norm, arm64_norm, hsp] using hsp_c
    have hx20_c' : sf_c.readReg64 .x20 = s.readReg64 .x20 := by simpa [wp_norm, arm64_norm] using hx20_c
    have hx22_c' : sf_c.readReg64 .x22 = BitVec.ofNat 64 i := by simpa [wp_norm, arm64_norm, hx22] using hx22_c
    have hx24_c' : sf_c.readReg64 .x24 = s.readReg64 .x24 := by simpa [wp_norm, arm64_norm] using hx24_c
    have hx25_c' : sf_c.readReg64 .x25 = s.readReg64 .x25 := by simpa [wp_norm, arm64_norm] using hx25_c
    have hx26_c' : sf_c.readReg64 .x26 = s.readReg64 .x26 := by simpa [wp_norm, arm64_norm] using hx26_c
    have hx29_c' : sf_c.readReg64 .x29 = sp0 - 96#64 := by simpa [wp_norm, arm64_norm, hx29] using hx29_c
    apply SepWPp.of_sepWP (mid := entry + 1328#64)
    wp_steps 6
    refine SepWP.weaken_pre
      (show _ ⊢
        optPolyCacheSlotAt A slot (some p) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F by
        unfold optPolyCacheSlotAt
        rw [show gf16SliceAt ptr_p p.coefficients ∗ tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗
              stackAt (sp0 - 672#64) computeAtStack ∗
              ((slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
                ((slot + 8#64) ↦₆₄ ptr_p) ∗
                ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
                A.live ptr_p (2 * p.coefficients.length) 2 ∗
                ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗ F) =
            ((slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
              ((slot + 8#64) ↦₆₄ ptr_p) ∗
              ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
              A.live ptr_p (2 * p.coefficients.length) 2 ∗
              gf16SliceAt ptr_p p.coefficients) ∗
              (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
                stackAt (sp0 - 672#64) computeAtStack ∗ F) by ac_rfl]
        refine sepConj_mono_left ?_
        exact Entails.sepExists_right ptr_p
          (Entails.pure_right ⟨hp_ge1, hp_le, hptr_p_ne⟩ (Entails.of_eq (by ac_rfl)))) ?_
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_c])
    apply hnext
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hrun_c]
    · simp [wp_norm, arm64_norm, hsp_c']
    · simp [traceVRegs, wp_norm, arm64_norm, htr_c, hvregs_c, htr_vr]
    · simp only [wp_norm, arm64_norm]
      exact bv64_ubfx_8_8_truncate8 hx0_c
    · simp only [wp_norm, arm64_norm]
      exact bv64_orr_w0_truncate8 hx0_c
    · simp [wp_norm, arm64_norm, hx20_c']
    · simp [wp_norm, arm64_norm, hx22_c']
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hx24_c']
    · simp [wp_norm, arm64_norm, hx25_c']
    · simp [wp_norm, arm64_norm, hx26_c']
    · simp [wp_norm, arm64_norm, hx29_c']

/-- Step 3 of the main loop (`0x6c0b0..0x6c0c8 -> 0x6bd88..0x6bda0`,
    `entry + 1328#64` to `entry + 1404#64` if `i + 1 = ptsNeeded`, or `entry + 548#64` if `i + 1 < ptsNeeded`):
    Appends `u16ToBeBytes yVal` to `out` at `out_ptr + 2 * i` and increments `i` and `2 * i`. -/
theorem decodedMessage_pushTwoBytes_sepWP {b : BitVec 64}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (sp0 out_ptr old_len_slot : BitVec 64) (i ptsNeeded : Nat)
    (out : List (BitVec 8)) (yVal : BitVec 16)
    (hi_lt : i < ptsNeeded) (hneed_le : ptsNeeded ≤ 16 * 65536)
    (hout_len : out.length = 2 * i)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1328#64)
    (hstat : s.status = .Running)
    (hx19 : BitVec.truncate 8 (s.readReg64 .x19) = BitVec.truncate 8 (yVal >>> 8))
    (hx21 : BitVec.truncate 8 (s.readReg64 .x21) = BitVec.truncate 8 yVal)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (2 * i))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (if i + 1 = ptsNeeded then
        (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1404#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 548#64) →
      sf.status = .Running →
      sf.sp = s.sp →
      traceVRegs sf = traceVRegs s →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x23 = BitVec.ofNat 64 (2 * (i + 1)) →
      sf.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
        (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
          ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
          (out_ptr ↦ₛ (out ++ u16ToBeBytes yVal)) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (2 * (ptsNeeded - (i + 1))) ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) ret_pc s
      (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
        ((sp0 - 200#64) ↦₆₄ old_len_slot) ∗
        (out_ptr ↦ₛ out) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (ptsNeeded - i)) ∗ P)
      post := by
  decodedMessageBin_fetches_range b (Rust.withPanics ext) 520 28
  decodedMessageBin_fetches_range b (Rust.withPanics ext) 1328 28
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  have h2i_add1 : BitVec.ofNat 64 (2 * i) + 1#64 = BitVec.ofNat 64 (2 * i + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have h2i1_ne : (BitVec.ofNat 64 (2 * i + 1) != BitVec.ofNat 64 (2 * ptsNeeded)) = true := by
    rw [bv64_bne_ofNat (by omega) (by omega), decide_eq_true_eq]; omega
  have hi_add1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have h2i2 : 2 * i + 2 = 2 * (i + 1) := by omega
  have h2i_add2 : BitVec.ofNat 64 (2 * i) + 2#64 = BitVec.ofNat 64 (2 * (i + 1)) := by
    rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, h2i2]
  have hi1_eq : (BitVec.ofNat 64 (i + 1) == BitVec.ofNat 64 ptsNeeded) = decide (i + 1 = ptsNeeded) :=
    bv64_beq_ofNat (by omega) (by omega)
  rw [memRegion_out_split2 out_ptr hi_lt (by omega)]
  wp_pull_exists
  wp_steps 14
  refine SepWP.weaken_pre
    (show _ ⊢
      (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
        (out_ptr ↦ₛ (out ++ u16ToBeBytes yVal)) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (2 * (ptsNeeded - (i + 1))) ∗ P) by
      rw [← pointsToBytes_append_u16ToBeBytes out_ptr out yVal, hout_len]
      exact Entails.of_eq (by ac_rfl)) ?_
  apply hcont
  · by_cases heq : i + 1 = ptsNeeded <;> simp [wp_norm, arm64_norm, hi1_eq, heq]
  · simp [wp_norm, arm64_norm, hstat]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm, h2i_add2]
  · simp [wp_norm, arm64_norm, hx24]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm, hx29]

/-! ## Full Main Loop (`0x6bda4..0x6c0fc`, `entry + 548#64` to `entry + 1404#64`) -/

/-- Full evaluation/interpolation loop (`0x6bda4..0x6c0fc`, `entry + 548#64` to `entry + 1404#64`):
    executes `rem + 1` iterations from `i` to `dec.ptsNeeded`, matching
    `decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (rem + 1) polys out`. -/
theorem decodedMessageLoop_wpp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hA : AllocContracts b A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName)
      (lagrangeCompleteSpec b))
    (hcomp_at : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName)
      (computeAtSpec A b))
    (dec : PolyDecoder) (sp0 pts_base pts_vec_ptr out_ptr : BitVec 64)
    (pins : List VecPin)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hsort : PolyDecoderStrictSorted dec)
    (hneed_le : dec.ptsNeeded ≤ 16 * 65536)
    (hall_ge : ∀ k (hk : k < 16), dec.necessaryPoints k ≤ (dec.pts[k]'(by omega)).vec.length)
    (s0 : State) (F R : SepProp) (Q : State → SepProp → Prop) :
    ∀ (rem i : Nat) (polys : List (Option Poly)) (out : List (BitVec 8)) (s : State),
      i + (rem + 1) = dec.ptsNeeded →
      polys.length = 16 →
      out.length = 2 * i →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 548#64 →
      s.status = .Running →
      s.sp = sp0 - 672#64 →
      traceVRegs s = traceVRegs s0 →
      s.readReg64 .x20 = pts_base →
      s.readReg64 .x22 = BitVec.ofNat 64 i →
      s.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
      s.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded →
      s.readReg64 .x25 = 24#64 →
      s.readReg64 .x26 = sp0 - 600#64 →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ sf : State,
        sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1404#64 →
        sf.status = .Running →
        sf.sp = sp0 - 672#64 →
        traceVRegs sf = traceVRegs s0 →
        sf.readReg64 .x29 = sp0 - 96#64 →
        let (polysFinal, outFinal) :=
          decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (rem + 1) polys out
        SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
          (optPolyCacheListAt A (sp0 - 600#64) polysFinal ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            sortedSetPtListPinAt A pts_base pins dec.pts ∗
            (out_ptr ↦ₛ outFinal) ∗
            interpolateScratchAt sp0 ∗
            reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          Q
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc s
        (optPolyCacheListAt A (sp0 - 600#64) polys ∗
          ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
          sortedSetPtListPinAt A pts_base pins dec.pts ∗
          (out_ptr ↦ₛ out) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
          interpolateScratchAt sp0 ∗
          reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))
  | rem, i, polys, out, s, hsum, hpolys_len, hout_len,
      hpc, hstat, hsp, htr, hx20, hx22, hx23, hx24, hx25, hx26, hx29, hnext => by
    have hi_lt : i < dec.ptsNeeded := by omega
    have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
    have hpoly_pts : i % 16 < dec.pts.length := by omega
    have hpoly_pins : i % 16 < pins.length := by omega
    have hpoly_p : i % 16 < polys.length := by omega
    have hnec_pos : 1 ≤ dec.necessaryPoints (i % 16) := necessaryPoints_pos_of_lt dec hi_lt
    have hnec_le_len : dec.necessaryPoints (i % 16) ≤ (dec.pts[i % 16]'hpoly_pts).vec.length :=
      hall_ge (i % 16) hpoly_lt
    have hle_len : (dec.pts[i % 16]'hpoly_pts).vec.length ≤ 65536 :=
      polyDecoderStrictSorted_elem_length_le hsort hpoly_pts
    have hge_len : 1 ≤ (dec.pts[i % 16]'hpoly_pts).vec.length := by omega
    have ⟨_, hb_lt0⟩ := bsearchLoop_bounds (dec.pts[i % 16]'hpoly_pts).vec
      (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length hge_len (by omega)
    have hb_lt : bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0
        (dec.pts[i % 16]'hpoly_pts).vec.length < (dec.pts[i % 16]'hpoly_pts).vec.length := by
      omega
    cases hfound : ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).x.value == BitVec.ofNat 16 (i / 16)
    · -- Not found (`0x6be14 (+660)`): interpolate (if needed), then `compute_at`, then push 2 bytes
      apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 660#64)
      refine SepWP.weaken_pre ?_
        (decodedMessage_bsearchStep_sepWP (A := A) dec sp0 pts_base pins i hpts hpins hi_lt hneed_le hge_len hle_len
          s
          (optPolyCacheListAt A (sp0 - 600#64) polys ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            (out_ptr ↦ₛ out) ∗
            memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
            interpolateScratchAt sp0 ∗
            reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          _ hpc hstat hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_ ?_)
      · exact Entails.of_eq (by ac_rfl)
      · dsimp only
        intro _ htrue
        rw [hfound] at htrue
        cases htrue
      · dsimp only
        intro _ hnot_found s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx29_1
        apply SepWP.done hpc1 hrun1
        have hstep_pure := decodedMessageLoopTotal_step_not_found dec hpts hsort hpolys_len (rem := rem) (out := out) rfl hb_lt hnot_found
        let ptsSlice := (dec.pts[i % 16]'hpoly_pts).vec.take (dec.necessaryPoints (i % 16))
        let pInterp := (polys[i % 16]'hpoly_p).getD (lagrangeInterpolateTotal ptsSlice)
        let yInterp := computeAtPure pInterp (GF16.new (BitVec.ofNat 16 (i / 16)))
        have hslice_len : ptsSlice.length = dec.necessaryPoints (i % 16) :=
          List.length_take_of_le hnec_le_len
        have hk_pos : 1 ≤ ptsSlice.length := by rw [hslice_len]; exact hnec_pos
        have hk_le : ptsSlice.length ≤ 65536 := by rw [hslice_len]; omega
        have hfocus_pre :
            sortedSetPtListPinAt A pts_base pins dec.pts ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
              (optPolyCacheListAt A (sp0 - 600#64) polys ∗
                ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
                ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
                ((sp0 - 608#64) ↦₆₄ 16#64) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                interpolateScratchAt sp0 ∗
                reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
                stackAt (sp0 - 672#64) computeAtStack ∗ F) =
            optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (polys[i % 16]'hpoly_p) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16)))
                (pins[i % 16]'hpoly_pins).ptr ptsSlice.length ∗
              ptSliceAt (pins[i % 16]'hpoly_pins).ptr ptsSlice ∗
              interpolateScratchAt sp0 ∗
              reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
              stackAt (sp0 - 672#64) lagrangePrepareStack ∗
              (optPolyCacheListAt A (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr (pins.take (i % 16)) ∗
                ptSliceRefListAt dec (i % 16 + 1) (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16 + 1))) (pins.drop (i % 16 + 1)) ∗
                sortedSetPtListPinAt A pts_base (pins.take (i % 16)) (dec.pts.take (i % 16)) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄ (pins[i % 16]'hpoly_pins).ptr) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄
                  BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
                ptSliceAt ((pins[i % 16]'hpoly_pins).ptr + BitVec.ofNat 64 (4 * dec.necessaryPoints (i % 16)))
                  ((dec.pts[i % 16]'hpoly_pts).vec.drop (dec.necessaryPoints (i % 16))) ∗
                sortedSetPtPinRest A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts) ∗
                sortedSetPtListPinAt A (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1)))
                  (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
                ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                memRegion ((sp0 - 672#64) - 4352#64) 48 ∗ F) := by
          rw [optPolyCacheListAt_focus A polys (i % 16) (sp0 - 600#64) hpoly_p,
            ptSliceRefListAt_focus dec pins (i % 16) pts_vec_ptr hpoly_pins,
            sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
            sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
              (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
            ptSliceAt_split_take_drop (dec.pts[i % 16]'hpoly_pts).vec (dec.necessaryPoints (i % 16))
              (pins[i % 16]'hpoly_pins).ptr hnec_le_len,
            stackAt_computeAt_eq_prepare (sp0 - 672#64), hslice_len]
          ac_rfl
        refine SepWPp.weaken_pre (Entails.of_eq hfocus_pre)
          (lagrangeInterpolate_inlined_wpp hb hA hcomp sp0 pts_vec_ptr (pins[i % 16]'hpoly_pins).ptr
            (BitVec.ofNat 64 dec.ptsNeeded) hsp0 (i % 16) (polys[i % 16]'hpoly_p) ptsSlice
            hpoly_lt hk_pos hk_le s0 s1 _ R Q
            hpc1 hrun1 (by rw [hsp1, hsp]) (by rw [htr1, htr])
            hx0_1 hx24_1 hx25_1 hx26_1 hx29_1 ?_)
        intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx22_2 hx24_2 hx25_2 hx26_2 hx29_2
        have hreasm_mid :
            optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (some pInterp) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16)))
                (pins[i % 16]'hpoly_pins).ptr ptsSlice.length ∗
              ptSliceAt (pins[i % 16]'hpoly_pins).ptr ptsSlice ∗
              interpolateScratchAt sp0 ∗
              reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
              stackAt (sp0 - 672#64) lagrangePrepareStack ∗
              (optPolyCacheListAt A (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr (pins.take (i % 16)) ∗
                ptSliceRefListAt dec (i % 16 + 1) (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16 + 1))) (pins.drop (i % 16 + 1)) ∗
                sortedSetPtListPinAt A pts_base (pins.take (i % 16)) (dec.pts.take (i % 16)) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄ (pins[i % 16]'hpoly_pins).ptr) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄
                  BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
                ptSliceAt ((pins[i % 16]'hpoly_pins).ptr + BitVec.ofNat 64 (4 * dec.necessaryPoints (i % 16)))
                  ((dec.pts[i % 16]'hpoly_pts).vec.drop (dec.necessaryPoints (i % 16))) ∗
                sortedSetPtPinRest A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts) ∗
                sortedSetPtListPinAt A (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1)))
                  (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
                ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                memRegion ((sp0 - 672#64) - 4352#64) 48 ∗ F) =
            optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (some pInterp) ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
              ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
              reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
              stackAt (sp0 - 672#64) computeAtStack ∗
              (optPolyCacheListAt A (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
                ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
                ((sp0 - 608#64) ↦₆₄ 16#64) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
                sortedSetPtListPinAt A pts_base pins dec.pts ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                interpolateScratchAt sp0 ∗ F) := by
          rw [ptSliceRefListAt_focus dec pins (i % 16) pts_vec_ptr hpoly_pins,
            sortedSetPtListPinAt_focus A pins dec.pts (i % 16) pts_base (by rw [hpins, hpts]) hpoly_pts,
            sortedSetPtPinAt_eq_slice A (pins[i % 16]'hpoly_pins) (dec.pts[i % 16]'hpoly_pts)
              (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
            ptSliceAt_split_take_drop (dec.pts[i % 16]'hpoly_pts).vec (dec.necessaryPoints (i % 16))
              (pins[i % 16]'hpoly_pins).ptr hnec_le_len,
            stackAt_computeAt_eq_prepare (sp0 - 672#64), hslice_len]
          ac_rfl
        refine SepWPp.weaken_pre (Entails.of_eq hreasm_mid)
          (decodedMessage_computeAtStep_wpp hcomp_at sp0
            ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) hsp0 i dec.ptsNeeded pInterp
            hi_lt hneed_le s0 s2 _ R Q
            hpc2 hrun2 hsp2 htr2 hx19_2 (by rw [hx22_2, hx22_1]) hx29_2 ?_)
        intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx21_3 hx20_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx29_3
        apply SepWPp.of_sepWP
          (mid := if i + 1 = dec.ptsNeeded then
            (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1404#64
          else
            (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 548#64)
        have hset_polys :
            optPolyCacheListAt A (sp0 - 600#64) (polys.take (i % 16)) ∗
              optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) (some pInterp) ∗
              optPolyCacheListAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) =
            optPolyCacheListAt A (sp0 - 600#64) (polys.set (i % 16) (some pInterp)) :=
          (optPolyCacheListAt_set A polys (i % 16) (some pInterp) (sp0 - 600#64) hpoly_p).symm
        refine SepWP.weaken_pre ?_
          (decodedMessage_pushTwoBytes_sepWP sp0 out_ptr (BitVec.ofNat 64 (2 * i)) i dec.ptsNeeded out
            yInterp.value hi_lt hneed_le hout_len s3
            (optPolyCacheListAt A (sp0 - 600#64) (polys.set (i % 16) (some pInterp)) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
              sortedSetPtListPinAt A pts_base pins dec.pts ∗
              interpolateScratchAt sp0 ∗
              reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
              stackAt (sp0 - 672#64) computeAtStack ∗ F)
            _ hpc3 hrun3 hx19_3 hx21_3 hx22_3 hx23_3 (by rw [hx24_3, hx24_2]) hx29_3 ?_)
        · rw [← hset_polys]
          exact Entails.of_eq (by ac_rfl)
        intro s4 hpc4 hrun4 hsp4 htr4 hx20_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4
        apply SepWP.done hpc4 hrun4
        cases rem with
        | zero =>
          have hi1_eq : i + 1 = dec.ptsNeeded := by omega
          simp only [hi1_eq, ↓reduceIte] at hpc4
          have hrem0 : dec.ptsNeeded - (i + 1) = 0 := by omega
          rw [hrem0, Nat.mul_zero, memRegion_zero]
          have hloop0 :
              decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (0 + 1) polys out =
                (polys.set (i % 16) (some pInterp), out ++ u16ToBeBytes yInterp.value) := by
            rw [hstep_pure]; rfl
          rw [hloop0] at hnext
          refine SepWPp.weaken_pre ?_
            (hnext s4 hpc4 hrun4 (by rw [hsp4, hsp3]) (by rw [htr4, htr3]) hx29_4)
          rw [hi1_eq]
          exact Entails.of_eq (by ac_rfl)
        | succ rem' =>
          have hi1_ne : i + 1 ≠ dec.ptsNeeded := by omega
          simp only [hi1_ne, ↓reduceIte] at hpc4
          refine SepWPp.weaken_pre ?_
            (decodedMessageLoop_wpp hb hA hcomp hcomp_at dec sp0 pts_base pts_vec_ptr out_ptr pins
              hsp0 hpts hpins hsort hneed_le hall_ge s0 F R Q
              rem' (i + 1) (polys.set (i % 16) (some pInterp))
              (out ++ u16ToBeBytes yInterp.value)
              s4 (by omega) (by simp [hpolys_len]) (by simp [hout_len, u16ToBeBytes]; omega)
              hpc4 hrun4 (by rw [hsp4, hsp3]) (by rw [htr4, htr3])
              (by rw [hx20_4, hx20_3, hx20_2, hx20_1]) hx22_4 hx23_4 hx24_4
              (by rw [hx25_4, hx25_3, hx25_2]) (by rw [hx26_4, hx26_3, hx26_2]) hx29_4
              (fun sf hpc_f hrun_f hsp_f htr_f hx29_f => ?_))
          · exact Entails.of_eq (by ac_rfl)
          · rw [← hstep_pure]
            exact hnext sf hpc_f hrun_f hsp_f htr_f hx29_f
    · -- Found in `dec.pts[i % 16]` at `0x6c0b0 (+1328)`
      apply SepWPp.of_sepWP
        (mid := if i + 1 = dec.ptsNeeded then
          (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1404#64
        else
          (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 548#64)
      refine SepWP.weaken_pre ?_
        (decodedMessage_bsearchStep_sepWP (A := A) dec sp0 pts_base pins i hpts hpins hi_lt hneed_le hge_len hle_len
          s
          (optPolyCacheListAt A (sp0 - 600#64) polys ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            (out_ptr ↦ₛ out) ∗
            memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
            interpolateScratchAt sp0 ∗
            reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          _ hpc hstat hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_ ?_)
      · exact Entails.of_eq (by ac_rfl)
      · dsimp only
        intro _ hfound' s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx29_1
        have hstep_pure := decodedMessageLoopTotal_step_found dec hpts hsort (rem := rem) (polys := polys) (out := out) rfl hb_lt hfound'
        refine SepWP.weaken_pre ?_
          (decodedMessage_pushTwoBytes_sepWP sp0 out_ptr (BitVec.ofNat 64 (2 * i)) i dec.ptsNeeded out
            ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value
            hi_lt hneed_le hout_len s1
            (optPolyCacheListAt A (sp0 - 600#64) polys ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
              sortedSetPtListPinAt A pts_base pins dec.pts ∗
              interpolateScratchAt sp0 ∗
              reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
              stackAt (sp0 - 672#64) computeAtStack ∗ F)
            _ hpc1 hrun1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx29_1 ?_)
        · exact Entails.of_eq (by ac_rfl)
        intro s2 hpc2 hrun2 hsp2 htr2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2
        apply SepWP.done hpc2 hrun2
        cases rem with
        | zero =>
          have hi1_eq : i + 1 = dec.ptsNeeded := by omega
          simp only [hi1_eq, ↓reduceIte] at hpc2
          have hrem0 : dec.ptsNeeded - (i + 1) = 0 := by omega
          rw [hrem0, Nat.mul_zero, memRegion_zero]
          have hloop0 :
              decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (0 + 1) polys out =
                (polys, out ++ u16ToBeBytes
                  ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value) := by
            rw [hstep_pure]; rfl
          rw [hloop0] at hnext
          refine SepWPp.weaken_pre ?_
            (hnext s2 hpc2 hrun2 (by rw [hsp2, hsp1, hsp]) (by rw [htr2, htr1, htr]) hx29_2)
          rw [hi1_eq]
          exact Entails.of_eq (by ac_rfl)
        | succ rem' =>
          have hi1_ne : i + 1 ≠ dec.ptsNeeded := by omega
          simp only [hi1_ne, ↓reduceIte] at hpc2
          refine SepWPp.weaken_pre ?_
            (decodedMessageLoop_wpp hb hA hcomp hcomp_at dec sp0 pts_base pts_vec_ptr out_ptr pins
              hsp0 hpts hpins hsort hneed_le hall_ge s0 F R Q
              rem' (i + 1) polys
              (out ++ u16ToBeBytes
                ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value)
              s2 (by omega) hpolys_len (by simp [hout_len, u16ToBeBytes]; omega)
              hpc2 hrun2 (by rw [hsp2, hsp1, hsp]) (by rw [htr2, htr1, htr])
              (by rw [hx20_2, hx20_1]) hx22_2 hx23_2 hx24_2
              (by rw [hx25_2, hx25_1]) (by rw [hx26_2, hx26_1]) hx29_2
              (fun sf hpc_f hrun_f hsp_f htr_f hx29_f => ?_))
          · exact Entails.of_eq (by ac_rfl)
          · rw [← hstep_pure]
            exact hnext sf hpc_f hrun_f hsp_f htr_f hx29_f
      · dsimp only
        intro _ hfalse
        rw [hfound] at hfalse
        cases hfalse

end CryptoVerification.SpqrV1.Poly.DecodedMessage
