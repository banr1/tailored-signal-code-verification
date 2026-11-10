/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyEncoder>::from_pb`: `.polys` Initialization and Inner Loop

**Checked by Lean.**

Proves unaligned 15-byte header-copy bridges, 16-slot `Poly::zero()` initialization (`+556..+1204`),
and the inner `GF16` big-endian deserialization loop (`+1308..+1356`) of `<PolyEncoder>::from_pb`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.EncoderFromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv_lit_add_lit
  ofNat_succ_sub_one ofNat_succ_add_neg_one

@[local arm64_norm, local wp_norm]
theorem zeroExtend_setWidth32_setWidth8 (b0 : BitVec 8) :
    (((b0.zeroExtend 64).setWidth 32).setWidth 8) = b0 := by
  bv_bits

@[local arm64_norm, local wp_norm]
theorem add_neg_64_eq_sub_64 (x : BitVec 64) :
    x + 18446744073709551552#64 = x - 64#64 := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem add_neg_48_eq_sub_48 (x : BitVec 64) :
    x + 18446744073709551568#64 = x - 48#64 := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem add_neg_32_eq_sub_32 (x : BitVec 64) :
    x + 18446744073709551584#64 = x - 32#64 := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem add_neg_24_eq_sub_24 (x : BitVec 64) :
    x + 18446744073709551592#64 = x - 24#64 := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem add_neg_16_eq_sub_16 (x : BitVec 64) :
    x + 18446744073709551600#64 = x - 16#64 := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_928_sub_64 (fsp : BitVec 64) :
    fsp + 928#64 - 64#64 = fsp + 864#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_928_sub_48 (fsp : BitVec 64) :
    fsp + 928#64 - 48#64 = fsp + 880#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_928_sub_32 (fsp : BitVec 64) :
    fsp + 928#64 - 32#64 = fsp + 896#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_928_sub_24 (fsp : BitVec 64) :
    fsp + 928#64 - 24#64 = fsp + 904#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_928_sub_16 (fsp : BitVec 64) :
    fsp + 928#64 - 16#64 = fsp + 912#64 := by bv_omega

/-! ## `zeroPolySlotAt` and `zeroPolySlotsAt` (`Poly::zero()` Slots) -/

/-- One initialized `Poly::zero()` slot (`cap = 1, ptr = p, len = 0`, with a live 2-byte allocation). -/
def zeroPolySlotAt (A : RustAlloc) (addr : BitVec 64) : SepProp :=
  ∃∗ ptr,
    ⌜ptr ≠ 0#64⌝ ∗
    (addr ↦₆₄ 1#64) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗ ((addr + 16#64) ↦₆₄ 0#64) ∗
    A.live ptr 2 2 ∗ memRegion ptr 2

/-- `n` contiguous `zeroPolySlotAt` headers starting at `base` with stride 24. -/
def zeroPolySlotsAt (A : RustAlloc) (base : BitVec 64) : Nat → SepProp
  | 0 => emp
  | n + 1 => zeroPolySlotAt A base ∗ zeroPolySlotsAt A (base + 24#64) n

theorem zeroPolySlotAt_intro (A : RustAlloc) (addr ptr : BitVec 64) (hptr : ptr ≠ 0#64) :
    (addr ↦₆₄ 1#64) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗ ((addr + 16#64) ↦₆₄ 0#64) ∗
      A.live ptr 2 2 ∗ memRegion ptr 2 ⊢
      zeroPolySlotAt A addr := by
  unfold zeroPolySlotAt
  refine Entails.sepExists_right ptr ?_
  exact Entails.pure_right hptr (Entails.of_eq (by ac_rfl))

theorem zeroPolySlotAt_entails_vecGF16Of (A : RustAlloc) (addr : BitVec 64) :
    zeroPolySlotAt A addr ⊢ vecGF16Of A addr [] := by
  unfold zeroPolySlotAt vecGF16Of vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
  apply Entails.sepExists_elim; intro ptr
  apply Entails.pure_left; intro hptr
  refine Entails.sepExists_right 1#64 (Entails.sepExists_right ptr ?_)
  have h1_ne : (1#64 : BitVec 64) ≠ 0#64 := by decide
  have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
  have hp : ([] : List GF16).length ≤ (1#64 : BitVec 64).toNat ∧
      (1#64 : BitVec 64).toNat * 2 < 2 ^ 63 ∧ ptr ≠ 0 := ⟨by decide, by decide, hptr⟩
  simp only [BitVec.ofNat_eq_ofNat, h1_ne, ↓reduceIte, h1_toNat, List.length_nil, Nat.zero_mul,
    Nat.sub_zero, Nat.one_mul, BitVec.add_zero, arrayAt, emp_sepConj]
  simp only [sepConj_pure_left_comm]
  refine Entails.pure_right hp ?_
  exact Entails.of_eq (by ac_rfl)

theorem zeroPolySlotsAt_entails_vecGF16ListOf (A : RustAlloc) :
    ∀ (n : Nat) (base : BitVec 64),
      zeroPolySlotsAt A base n ⊢ vecGF16ListOf A base (List.replicate n [])
  | 0, base => by
    simp [zeroPolySlotsAt, vecGF16ListOf, arrayAt]
    exact Entails.refl _
  | n + 1, base => by
    simp only [zeroPolySlotsAt, List.replicate_succ, vecGF16ListOf, arrayAt, vecHeaderBytes,
      BitVec.ofNat_eq_ofNat]
    exact sepConj_mono (zeroPolySlotAt_entails_vecGF16Of A base)
      (zeroPolySlotsAt_entails_vecGF16ListOf A n (base + 24#64))

/-! ## Unaligned 15-Byte Header Copy Bridges (`pair64_split_at_1`, `pair64_split_at_7`) -/

/-- 64-bit word formed by bytes `1..7` of `v0` followed by byte `0` of `v1`. -/
def midWord1 (v0 v1 : BitVec 64) : BitVec 64 :=
  pack64 (v0.extractLsb' 8 8) (v0.extractLsb' 16 8) (v0.extractLsb' 24 8)
    (v0.extractLsb' 32 8) (v0.extractLsb' 40 8) (v0.extractLsb' 48 8)
    (v0.extractLsb' 56 8) (v1.extractLsb' 0 8)

/-- Trailing 7 bytes (`1..7`) of `v1`. -/
def tailBytes7 (v1 : BitVec 64) : List (BitVec 8) :=
  [v1.extractLsb' 8 8, v1.extractLsb' 16 8, v1.extractLsb' 24 8,
   v1.extractLsb' 32 8, v1.extractLsb' 40 8, v1.extractLsb' 48 8,
   v1.extractLsb' 56 8]

/-- Replace byte `0` of `v1` with `b0`. -/
def replaceLowByte64 (b0 : BitVec 8) (v1 : BitVec 64) : BitVec 64 :=
  pack64 b0 (v1.extractLsb' 8 8) (v1.extractLsb' 16 8) (v1.extractLsb' 24 8)
    (v1.extractLsb' 32 8) (v1.extractLsb' 40 8) (v1.extractLsb' 48 8)
    (v1.extractLsb' 56 8)

/-- Leading 7 bytes (`0..6`) of `u0`. -/
def headBytes7 (u0 : BitVec 64) : List (BitVec 8) :=
  [u0.extractLsb' 0 8, u0.extractLsb' 8 8, u0.extractLsb' 16 8,
   u0.extractLsb' 24 8, u0.extractLsb' 32 8, u0.extractLsb' 40 8,
   u0.extractLsb' 48 8]

/-- 64-bit word at offset `+7` spanning byte `7` of `u0` and bytes `0..6` of `u1`. -/
def midWord7 (u0 u1 : BitVec 64) : BitVec 64 :=
  pack64 (u0.extractLsb' 56 8)
    (u1.extractLsb' 0 8) (u1.extractLsb' 8 8) (u1.extractLsb' 16 8)
    (u1.extractLsb' 24 8) (u1.extractLsb' 32 8) (u1.extractLsb' 40 8)
    (u1.extractLsb' 48 8)

/-- Second 64-bit word formed after writing `len` at offset `+7` with trailing byte `b15`. -/
def shiftedWord7 (len : BitVec 64) (b15 : BitVec 8) : BitVec 64 :=
  pack64 (len.extractLsb' 8 8) (len.extractLsb' 16 8) (len.extractLsb' 24 8)
    (len.extractLsb' 32 8) (len.extractLsb' 40 8) (len.extractLsb' 48 8)
    (len.extractLsb' 56 8) b15

theorem extractLsb_0_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 0 8 = b0 := by unfold pack64; bv_bits
theorem extractLsb_8_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 8 8 = b1 := by unfold pack64; bv_bits
theorem extractLsb_16_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 16 8 = b2 := by unfold pack64; bv_bits
theorem extractLsb_24_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 24 8 = b3 := by unfold pack64; bv_bits
theorem extractLsb_32_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 32 8 = b4 := by unfold pack64; bv_bits
theorem extractLsb_40_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 40 8 = b5 := by unfold pack64; bv_bits
theorem extractLsb_48_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 48 8 = b6 := by unfold pack64; bv_bits
theorem extractLsb_56_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 56 8 = b7 := by unfold pack64; bv_bits

theorem pack64_extractLsb' (v : BitVec 64) :
    pack64 (v.extractLsb' 0 8) (v.extractLsb' 8 8) (v.extractLsb' 16 8)
      (v.extractLsb' 24 8) (v.extractLsb' 32 8) (v.extractLsb' 40 8)
      (v.extractLsb' 48 8) (v.extractLsb' 56 8) = v := by
  unfold pack64; bv_bits

theorem pair64_split_at_1 (a v0 v1 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) =
      ((a ↦₈ v0.extractLsb' 0 8) ∗
       ((a + 1#64) ↦₆₄ midWord1 v0 v1) ∗
       ((a + 9#64) ↦ₛ tailBytes7 v1)) := by
  have hu0 : a + BitVec.ofNat 64 (unpack64 v0).length = a + 8#64 := rfl
  rw [pointsTo64_eq_pointsToBytes a v0, pointsTo64_eq_pointsToBytes (a + 8#64) v1,
      ← hu0, ← pointsToBytes_append a (unpack64 v0) (unpack64 v1),
      ← pointsToBytes_singleton a (v0.extractLsb' 0 8),
      pointsTo64_eq_pointsToBytes (a + 1#64) (midWord1 v0 v1),
      midWord1, pack64, unpack64_pack64]
  have h9 : a + 1#64 + BitVec.ofNat 64 ([v0.extractLsb' 8 8, v0.extractLsb' 16 8, v0.extractLsb' 24 8,
    v0.extractLsb' 32 8, v0.extractLsb' 40 8, v0.extractLsb' 48 8,
    v0.extractLsb' 56 8, v1.extractLsb' 0 8] : List (BitVec 8)).length = a + 9#64 := by
    change a + 1#64 + 8#64 = a + 9#64
    bv_omega
  rw [← h9, ← pointsToBytes_append (a + 1#64)]
  have ha1 : a + BitVec.ofNat 64 ([v0.extractLsb' 0 8] : List (BitVec 8)).length = a + 1#64 := rfl
  rw [← ha1, ← pointsToBytes_append a]
  rfl

theorem midWord1_replaceLowByte64 (outPtr len old1 : BitVec 64) :
    midWord1 outPtr (replaceLowByte64 (len.extractLsb' 0 8) old1) = midWord1 outPtr len := by
  simp only [midWord1, replaceLowByte64, extractLsb_0_pack64]

theorem tailBytes7_replaceLowByte64 (b0 : BitVec 8) (old1 : BitVec 64) :
    tailBytes7 (replaceLowByte64 b0 old1) = tailBytes7 old1 := by
  simp only [tailBytes7, replaceLowByte64, extractLsb_8_pack64, extractLsb_16_pack64,
    extractLsb_24_pack64, extractLsb_32_pack64, extractLsb_40_pack64,
    extractLsb_48_pack64, extractLsb_56_pack64]

theorem split_at_1_after_write (a outPtr len old1 : BitVec 64) :
    ((a ↦₈ outPtr.extractLsb' 0 8) ∗
     ((a + 1#64) ↦₆₄ midWord1 outPtr len) ∗
     ((a + 9#64) ↦ₛ tailBytes7 old1)) =
      ((a ↦₆₄ outPtr) ∗
       ((a + 8#64) ↦₆₄ replaceLowByte64 (len.extractLsb' 0 8) old1)) := by
  rw [pair64_split_at_1 a outPtr (replaceLowByte64 (len.extractLsb' 0 8) old1),
      midWord1_replaceLowByte64, tailBytes7_replaceLowByte64]

theorem pair64_split_at_7 (b u0 u1 : BitVec 64) :
    ((b ↦₆₄ u0) ∗ ((b + 8#64) ↦₆₄ u1)) =
      ((b ↦ₛ headBytes7 u0) ∗
       ((b + 7#64) ↦₆₄ midWord7 u0 u1) ∗
       ((b + 15#64) ↦₈ u1.extractLsb' 56 8)) := by
  have hu0 : b + BitVec.ofNat 64 (unpack64 u0).length = b + 8#64 := rfl
  rw [pointsTo64_eq_pointsToBytes b u0, pointsTo64_eq_pointsToBytes (b + 8#64) u1,
      ← hu0, ← pointsToBytes_append b (unpack64 u0) (unpack64 u1),
      ← pointsToBytes_singleton (b + 15#64) (u1.extractLsb' 56 8),
      pointsTo64_eq_pointsToBytes (b + 7#64) (midWord7 u0 u1),
      midWord7, pack64, unpack64_pack64]
  have h15 : b + 7#64 + BitVec.ofNat 64 ([u0.extractLsb' 56 8, u1.extractLsb' 0 8, u1.extractLsb' 8 8,
    u1.extractLsb' 16 8, u1.extractLsb' 24 8, u1.extractLsb' 32 8,
    u1.extractLsb' 40 8, u1.extractLsb' 48 8] : List (BitVec 8)).length = b + 15#64 := by
    change b + 7#64 + 8#64 = b + 15#64
    bv_omega
  rw [← h15, ← pointsToBytes_append (b + 7#64)]
  have hb7 : b + BitVec.ofNat 64 (headBytes7 u0).length = b + 7#64 := rfl
  rw [← hb7, ← pointsToBytes_append b]
  rfl

theorem midWord7_midWord1_shiftedWord7 (outPtr len : BitVec 64) (b15 : BitVec 8) :
    midWord7 (midWord1 outPtr len) (shiftedWord7 len b15) = len := by
  simp only [midWord7, midWord1, shiftedWord7, extractLsb_56_pack64,
    extractLsb_0_pack64, extractLsb_8_pack64, extractLsb_16_pack64,
    extractLsb_24_pack64, extractLsb_32_pack64, extractLsb_40_pack64,
    extractLsb_48_pack64, pack64_extractLsb']

theorem extractLsb56_shiftedWord7 (len : BitVec 64) (b15 : BitVec 8) :
    (shiftedWord7 len b15).extractLsb' 56 8 = b15 := by
  simp only [shiftedWord7, extractLsb_56_pack64]

theorem split_at_7_after_write (b outPtr len : BitVec 64) (b15 : BitVec 8) :
    ((b ↦ₛ headBytes7 (midWord1 outPtr len)) ∗
     ((b + 7#64) ↦₆₄ len) ∗
     ((b + 15#64) ↦₈ b15)) =
      ((b ↦₆₄ midWord1 outPtr len) ∗
       ((b + 8#64) ↦₆₄ shiftedWord7 len b15)) := by
  rw [pair64_split_at_7 b (midWord1 outPtr len) (shiftedWord7 len b15),
      midWord7_midWord1_shiftedWord7, extractLsb56_shiftedWord7]

theorem fsp_904_split_at_1 (fsp v0 v1 : BitVec 64) :
    (((fsp + 904#64) ↦₆₄ v0) ∗ ((fsp + 912#64) ↦₆₄ v1)) =
      (((fsp + 904#64) ↦₈ v0.extractLsb' 0 8) ∗
       ((fsp + 905#64) ↦₆₄ midWord1 v0 v1) ∗
       ((fsp + 913#64) ↦ₛ tailBytes7 v1)) := by
  have h1 : fsp + 904#64 + 8#64 = fsp + 912#64 := by bv_omega
  have h2 : fsp + 904#64 + 1#64 = fsp + 905#64 := by bv_omega
  have h3 : fsp + 904#64 + 9#64 = fsp + 913#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact pair64_split_at_1 (fsp + 904#64) v0 v1

theorem fsp_864_split_at_7 (fsp u0 u1 : BitVec 64) :
    (((fsp + 864#64) ↦₆₄ u0) ∗ ((fsp + 872#64) ↦₆₄ u1)) =
      (((fsp + 864#64) ↦ₛ headBytes7 u0) ∗
       ((fsp + 871#64) ↦₆₄ midWord7 u0 u1) ∗
       ((fsp + 879#64) ↦₈ u1.extractLsb' 56 8)) := by
  have h1 : fsp + 864#64 + 8#64 = fsp + 872#64 := by bv_omega
  have h2 : fsp + 864#64 + 7#64 = fsp + 871#64 := by bv_omega
  have h3 : fsp + 864#64 + 15#64 = fsp + 879#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact pair64_split_at_7 (fsp + 864#64) u0 u1

theorem fsp_864_after_write (fsp outPtr len : BitVec 64) (b15 : BitVec 8) :
    (((fsp + 864#64) ↦ₛ headBytes7 (midWord1 outPtr len)) ∗
     ((fsp + 871#64) ↦₆₄ len) ∗
     ((fsp + 879#64) ↦₈ b15)) =
      (((fsp + 864#64) ↦₆₄ midWord1 outPtr len) ∗
       ((fsp + 872#64) ↦₆₄ shiftedWord7 len b15)) := by
  have h1 : fsp + 864#64 + 8#64 = fsp + 872#64 := by bv_omega
  have h2 : fsp + 864#64 + 7#64 = fsp + 871#64 := by bv_omega
  have h3 : fsp + 864#64 + 15#64 = fsp + 879#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact split_at_7_after_write (fsp + 864#64) outPtr len b15

theorem fsp_880_split_at_7 (fsp u0 u1 : BitVec 64) :
    (((fsp + 880#64) ↦₆₄ u0) ∗ ((fsp + 888#64) ↦₆₄ u1)) =
      (((fsp + 880#64) ↦ₛ headBytes7 u0) ∗
       ((fsp + 887#64) ↦₆₄ midWord7 u0 u1) ∗
       ((fsp + 895#64) ↦₈ u1.extractLsb' 56 8)) := by
  have h1 : fsp + 880#64 + 8#64 = fsp + 888#64 := by bv_omega
  have h2 : fsp + 880#64 + 7#64 = fsp + 887#64 := by bv_omega
  have h3 : fsp + 880#64 + 15#64 = fsp + 895#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact pair64_split_at_7 (fsp + 880#64) u0 u1

theorem fsp_880_after_write (fsp outPtr len : BitVec 64) (b15 : BitVec 8) :
    (((fsp + 880#64) ↦ₛ headBytes7 (midWord1 outPtr len)) ∗
     ((fsp + 887#64) ↦₆₄ len) ∗
     ((fsp + 895#64) ↦₈ b15)) =
      (((fsp + 880#64) ↦₆₄ midWord1 outPtr len) ∗
       ((fsp + 888#64) ↦₆₄ shiftedWord7 len b15)) := by
  have h1 : fsp + 880#64 + 8#64 = fsp + 888#64 := by bv_omega
  have h2 : fsp + 880#64 + 7#64 = fsp + 887#64 := by bv_omega
  have h3 : fsp + 880#64 + 15#64 = fsp + 895#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact split_at_7_after_write (fsp + 880#64) outPtr len b15

theorem slot_split_at_1 (slotAddr v0 v1 : BitVec 64) :
    (((slotAddr + 8#64) ↦₆₄ v0) ∗ ((slotAddr + 16#64) ↦₆₄ v1)) =
      (((slotAddr + 8#64) ↦₈ v0.extractLsb' 0 8) ∗
       ((slotAddr + 9#64) ↦₆₄ midWord1 v0 v1) ∗
       ((slotAddr + 17#64) ↦ₛ tailBytes7 v1)) := by
  have h1 : slotAddr + 8#64 + 8#64 = slotAddr + 16#64 := by bv_omega
  have h2 : slotAddr + 8#64 + 1#64 = slotAddr + 9#64 := by bv_omega
  have h3 : slotAddr + 8#64 + 9#64 = slotAddr + 17#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact pair64_split_at_1 (slotAddr + 8#64) v0 v1

theorem slot_after_write (slotAddr outPtr len old1 : BitVec 64) :
    (((slotAddr + 8#64) ↦₈ outPtr.extractLsb' 0 8) ∗
     ((slotAddr + 9#64) ↦₆₄ midWord1 outPtr len) ∗
     ((slotAddr + 17#64) ↦ₛ tailBytes7 old1)) =
      (((slotAddr + 8#64) ↦₆₄ outPtr) ∗
       ((slotAddr + 16#64) ↦₆₄ replaceLowByte64 (len.extractLsb' 0 8) old1)) := by
  have h1 : slotAddr + 8#64 + 8#64 = slotAddr + 16#64 := by bv_omega
  have h2 : slotAddr + 8#64 + 1#64 = slotAddr + 9#64 := by bv_omega
  have h3 : slotAddr + 8#64 + 9#64 = slotAddr + 17#64 := by bv_omega
  rw [← h1, ← h2, ← h3]
  exact split_at_1_after_write (slotAddr + 8#64) outPtr len old1

theorem cells_864_eq (fsp : BitVec 64) :
    cells (fsp + 864#64) 4 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3,
        ((fsp + 864#64) ↦₆₄ v0) ∗ ((fsp + 872#64) ↦₆₄ v1) ∗
        ((fsp + 880#64) ↦₆₄ v2) ∗ ((fsp + 888#64) ↦₆₄ v3) := by
  have h1 : fsp + 864#64 + 8#64 = fsp + 872#64 := by bv_omega
  have h2 : fsp + 872#64 + 8#64 = fsp + 880#64 := by bv_omega
  have h3 : fsp + 880#64 + 8#64 = fsp + 888#64 := by bv_omega
  rw [ProofLib.cells_succ, h1, ProofLib.cells_succ, h2, ProofLib.cells_succ, h3,
      ProofLib.cells_succ, ProofLib.cells_zero]
  simp only [sepExists_sepConj_right, sepConj_emp, sepConj_assoc]

theorem cells_896_eq (fsp : BitVec 64) :
    cells (fsp + 896#64) 3 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2,
        ((fsp + 896#64) ↦₆₄ v0) ∗ ((fsp + 904#64) ↦₆₄ v1) ∗ ((fsp + 912#64) ↦₆₄ v2) := by
  have h1 : fsp + 896#64 + 8#64 = fsp + 904#64 := by bv_omega
  have h2 : fsp + 904#64 + 8#64 = fsp + 912#64 := by bv_omega
  rw [ProofLib.cells_succ, h1, ProofLib.cells_succ, h2, ProofLib.cells_succ, ProofLib.cells_zero]
  simp only [sepExists_sepConj_right, sepConj_emp, sepConj_assoc]

/-! ## `.polys` 16-Slot `Poly::zero()` Initialization (`+556 -> +1204`, `0x22c -> 0x4b4`) -/

theorem sepWPp_panic_of_sepWP_1696 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (h1 : SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName + 1696#64) s P
      (fun sm _ => sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm Pm hpcm hrunm htrm =>
    from_pb_panic_1696 s0 sm Pm R hpcm hrunm htrm)

theorem sepWPp_panic_of_sepWP_1708 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (h1 : SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName + 1708#64) s P
      (fun sm _ => sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm Pm hpcm hrunm htrm =>
    from_pb_panic_1708 s0 sm Pm R hpcm hrunm htrm)

local macro "polys_alloc_call" mid:term : tactic => `(tactic| (
  apply SepWPp.of_sepWP (mid := $mid)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
))

local macro "polys_oom_exit" hoom:ident hpanic:ident : tactic => `(tactic| (
  conv => arg 4; simp only [$hoom:ident, ↓reduceIte, sepConj_assoc]
  apply sepWPp_pure_mid; intro _
  refine $hpanic:ident _ _ ?_
  wp_steps
  exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, *])
))

/-- Step allocations 0..3 (`+556 -> +656`, `0x22c -> 0x290`): saves `(out, pbA)` at `[fsp+56, fsp+64]`
    and allocates `p0` (`x20`), `p1` (`[fsp+48]`), `p2` (`[fsp+40]`), `p3` (`[fsp+32]`). -/
theorem polys_alloc_0_3 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 556#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out) (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (p0 p1 p2 p3 : BitVec 64),
      p0 ≠ 0#64 → p1 ≠ 0#64 → p2 ≠ 0#64 → p3 ≠ 0#64 →
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 656#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x20 = p0 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
          ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
          A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
          A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (cells (fsp + 32#64) 5 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk 2 2 := ⟨by omega, hpow2, by omega⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.shim_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
  have hpanic1696 := fun (s : State) (P : SepProp) => @sepWPp_panic_of_sepWP_1696 b ext Q s0 s P R
  have hc5 : cells (fsp + 32#64) 5 =
      ∃∗ c0, ∃∗ c1, ∃∗ c2, ∃∗ c3, ∃∗ c4,
        ((fsp + 32#64) ↦₆₄ c0) ∗ ((fsp + 40#64) ↦₆₄ c1) ∗ ((fsp + 48#64) ↦₆₄ c2) ∗
        ((fsp + 56#64) ↦₆₄ c3) ∗ ((fsp + 64#64) ↦₆₄ c4) := by
    have h1 : fsp + 32#64 + 8#64 = fsp + 40#64 := by bv_omega
    have h2 : fsp + 40#64 + 8#64 = fsp + 48#64 := by bv_omega
    have h3 : fsp + 48#64 + 8#64 = fsp + 56#64 := by bv_omega
    have h4 : fsp + 56#64 + 8#64 = fsp + 64#64 := by bv_omega
    rw [ProofLib.cells_succ, h1, ProofLib.cells_succ, h2, ProofLib.cells_succ, h3,
        ProofLib.cells_succ, h4, ProofLib.cells_succ, ProofLib.cells_zero]
    simp only [sepExists_sepConj_right, sepConj_emp, sepConj_assoc]
  rw [hc5]; simp only [sepExists_sepConj_left, sepConj_assoc]
  iterate 5 (apply SepWPp.exists_elim; intro _)
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 556 104
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic1696 hcont ⊢
  generalize hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry at *
  examples_hide_fetches
  polys_alloc_call (entry + 576#64)
  by_cases hoom0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · polys_oom_exit hoom0 hpanic1696
  · conv => arg 4; simp only [hoom0, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr0⟩
    have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom0
    polys_alloc_call (entry + 600#64)
    by_cases hoom1 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · polys_oom_exit hoom1 hpanic1696
    · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr1⟩
      have hbeq1 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom1
      polys_alloc_call (entry + 624#64)
      by_cases hoom2 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · polys_oom_exit hoom2 hpanic1696
      · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr2⟩
        have hbeq2 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom2
        polys_alloc_call (entry + 648#64)
        by_cases hoom3 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · polys_oom_exit hoom3 hpanic1696
        · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr3⟩
          have hbeq3 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom3
          apply SepWPp.of_sepWP (mid := entry + 656#64)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine SepWPp.weaken_pre
            (by simp only [h_1, h_23, h_45, h_67, hsp_sf, hsp_sf_1, hsp_sf_2, hsp_sf_3, hsp]; exact Entails.of_eq (by ac_rfl))
            (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
              (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
              hoom0 hoom1 hoom2 hoom3
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, Reg.x20, *])
              (by simp only [arm64_norm, wp_norm, Reg.x29, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]))

/-- Step allocations 4..7 (`+656 -> +752`, `0x290 -> 0x2f0`): allocates `p4` (`[fsp+24]`),
    `p5` (`[fsp+16]`), `p6` (`[fsp+8]`), `p7` (`[fsp+0]`). -/
theorem polys_alloc_4_7 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 656#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (p4 p5 p6 p7 : BitVec 64),
      p4 ≠ 0#64 → p5 ≠ 0#64 → p6 ≠ 0#64 → p7 ≠ 0#64 →
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 752#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x20 = s.readReg64 .x20 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
          A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
          A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (cells fsp 4 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk 2 2 := ⟨by omega, hpow2, by omega⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.shim_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
  have hpanic1696 := fun (s : State) (P : SepProp) => @sepWPp_panic_of_sepWP_1696 b ext Q s0 s P R
  have hc4 : cells fsp 4 =
      ∃∗ c0, ∃∗ c1, ∃∗ c2, ∃∗ c3,
        (fsp ↦₆₄ c0) ∗ ((fsp + 8#64) ↦₆₄ c1) ∗ ((fsp + 16#64) ↦₆₄ c2) ∗ ((fsp + 24#64) ↦₆₄ c3) := by
    have h1 : fsp + 8#64 + 8#64 = fsp + 16#64 := by bv_omega
    have h2 : fsp + 16#64 + 8#64 = fsp + 24#64 := by bv_omega
    rw [ProofLib.cells_succ, ProofLib.cells_succ, h1, ProofLib.cells_succ, h2,
        ProofLib.cells_succ, ProofLib.cells_zero]
    simp only [sepExists_sepConj_right, sepConj_emp, sepConj_assoc]
  rw [hc4]; simp only [sepExists_sepConj_left, sepConj_assoc]
  iterate 4 (apply SepWPp.exists_elim; intro _)
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 656 100
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic1696 hcont ⊢
  generalize hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry at *
  examples_hide_fetches
  polys_alloc_call (entry + 672#64)
  by_cases hoom4 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · polys_oom_exit hoom4 hpanic1696
  · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr4⟩
    have hbeq4 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom4
    polys_alloc_call (entry + 696#64)
    by_cases hoom5 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · polys_oom_exit hoom5 hpanic1696
    · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr5⟩
      have hbeq5 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom5
      polys_alloc_call (entry + 720#64)
      by_cases hoom6 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · polys_oom_exit hoom6 hpanic1696
      · conv => arg 4; simp only [hoom6, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr6⟩
        have hbeq6 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom6
        polys_alloc_call (entry + 744#64)
        by_cases hoom7 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · polys_oom_exit hoom7 hpanic1696
        · conv => arg 4; simp only [hoom7, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr7⟩
          have hbeq7 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom7
          apply SepWPp.of_sepWP (mid := entry + 752#64)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine SepWPp.weaken_pre
            (by simp only [h_1, h_23, h_45, h_67, hsp_sf, hsp_sf_1, hsp_sf_2, hsp_sf_3, hsp]; exact Entails.of_eq (by ac_rfl))
            (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
              (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
              hoom4 hoom5 hoom6 hoom7
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, Reg.x20, *])
              (by simp only [arm64_norm, wp_norm, Reg.x29, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]))

/-- Step allocations 8..11 (`+752 -> +848`, `0x2f0 -> 0x350`): allocates `p8` (`x19`),
    `p9` (`x21`), `p10` (`x23`), `p11` (`x24`). -/
theorem polys_alloc_8_11 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 752#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (p8 p9 p10 p11 : BitVec 64),
      p8 ≠ 0#64 → p9 ≠ 0#64 → p10 ≠ 0#64 → p11 ≠ 0#64 →
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 848#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x19 = p8 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = p9 → sm.readReg64 .x23 = p10 →
      sm.readReg64 .x24 = p11 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (A.live p8 2 2 ∗ memRegion p8 2 ∗ A.live p9 2 2 ∗ memRegion p9 2 ∗
          A.live p10 2 2 ∗ memRegion p10 2 ∗ A.live p11 2 2 ∗ memRegion p11 2 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk 2 2 := ⟨by omega, hpow2, by omega⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.shim_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
  have hpanic1696 := fun (s : State) (P : SepProp) => @sepWPp_panic_of_sepWP_1696 b ext Q s0 s P R
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 752 100
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic1696 hcont ⊢
  generalize hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry at *
  examples_hide_fetches
  polys_alloc_call (entry + 768#64)
  by_cases hoom8 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · polys_oom_exit hoom8 hpanic1696
  · conv => arg 4; simp only [hoom8, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr8⟩
    have hbeq8 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom8
    polys_alloc_call (entry + 792#64)
    by_cases hoom9 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · polys_oom_exit hoom9 hpanic1696
    · conv => arg 4; simp only [hoom9, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr9⟩
      have hbeq9 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom9
      polys_alloc_call (entry + 816#64)
      by_cases hoom10 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · polys_oom_exit hoom10 hpanic1696
      · conv => arg 4; simp only [hoom10, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr10⟩
        have hbeq10 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom10
        polys_alloc_call (entry + 840#64)
        by_cases hoom11 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · polys_oom_exit hoom11 hpanic1696
        · conv => arg 4; simp only [hoom11, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr11⟩
          have hbeq11 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom11
          apply SepWPp.of_sepWP (mid := entry + 848#64)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine SepWPp.weaken_pre
            (by simp only [h_1, h_23, h_45, h_67, hsp_sf, hsp_sf_1, hsp_sf_2, hsp_sf_3, hsp]; exact Entails.of_eq (by ac_rfl))
            (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
              (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
              hoom8 hoom9 hoom10 hoom11
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, Reg.x19, *])
              (by simp only [arm64_norm, wp_norm, Reg.x20, *]) (by simp only [arm64_norm, wp_norm, Reg.x21, *])
              (by simp only [arm64_norm, wp_norm, Reg.x23, *]) (by simp only [arm64_norm, wp_norm, Reg.x24, *])
              (by simp only [arm64_norm, wp_norm, Reg.x29, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]))

/-- Step allocations 12..15 (`+848 -> +940`, `0x350 -> 0x3ac`): allocates `p12` (`x25`),
    `p13` (`x26`), `p14` (`x27`), `p15` (`x0`). -/
theorem polys_alloc_12_15 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 848#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (p12 p13 p14 p15 : BitVec 64),
      p12 ≠ 0#64 → p13 ≠ 0#64 → p14 ≠ 0#64 → p15 ≠ 0#64 →
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 940#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x0 = p15 → sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = p12 → sm.readReg64 .x26 = p13 →
      sm.readReg64 .x27 = p14 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (A.live p12 2 2 ∗ memRegion p12 2 ∗ A.live p13 2 2 ∗ memRegion p13 2 ∗
          A.live p14 2 2 ∗ memRegion p14 2 ∗ A.live p15 2 2 ∗ memRegion p15 2 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk 2 2 := ⟨by omega, hpow2, by omega⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.shim_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
  have hpanic1696 := fun (s : State) (P : SepProp) => @sepWPp_panic_of_sepWP_1696 b ext Q s0 s P R
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 848 96
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic1696 hcont ⊢
  generalize hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry at *
  examples_hide_fetches
  polys_alloc_call (entry + 864#64)
  by_cases hoom12 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · polys_oom_exit hoom12 hpanic1696
  · conv => arg 4; simp only [hoom12, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr12⟩
    have hbeq12 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom12
    polys_alloc_call (entry + 888#64)
    by_cases hoom13 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · polys_oom_exit hoom13 hpanic1696
    · conv => arg 4; simp only [hoom13, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr13⟩
      have hbeq13 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom13
      polys_alloc_call (entry + 912#64)
      by_cases hoom14 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · polys_oom_exit hoom14 hpanic1696
      · conv => arg 4; simp only [hoom14, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr14⟩
        have hbeq14 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom14
        polys_alloc_call (entry + 936#64)
        by_cases hoom15 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · polys_oom_exit hoom15 hpanic1696
        · conv => arg 4; simp only [hoom15, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr15⟩
          have hbeq15 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom15
          apply SepWPp.of_sepWP (mid := entry + 940#64)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine SepWPp.weaken_pre
            (by simp only [h_1, h_23, h_45, h_67, hsp_sf, hsp_sf_1, hsp_sf_2, hsp_sf_3, hsp]; exact Entails.of_eq (by ac_rfl))
            (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
              (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
              hoom12 hoom13 hoom14 hoom15
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, Reg.x0, *])
              (by simp only [arm64_norm, wp_norm, Reg.x19, *]) (by simp only [arm64_norm, wp_norm, Reg.x20, *])
              (by simp only [arm64_norm, wp_norm, Reg.x21, *]) (by simp only [arm64_norm, wp_norm, Reg.x23, *])
              (by simp only [arm64_norm, wp_norm, Reg.x24, *]) (by simp only [arm64_norm, wp_norm, Reg.x25, *])
              (by simp only [arm64_norm, wp_norm, Reg.x26, *]) (by simp only [arm64_norm, wp_norm, Reg.x27, *])
              (by simp only [arm64_norm, wp_norm, Reg.x29, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]))

/-- Straight-line scatter of the 16 `Poly::zero()` headers (`+940 -> +1204`, `0x3ac -> 0x4b4`). -/
theorem polys_init_scatter {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (fsp out pbA polysPtr : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 64)
    (hp0 : p0 ≠ 0#64) (hp1 : p1 ≠ 0#64) (hp2 : p2 ≠ 0#64) (hp3 : p3 ≠ 0#64)
    (hp4 : p4 ≠ 0#64) (hp5 : p5 ≠ 0#64) (hp6 : p6 ≠ 0#64) (hp7 : p7 ≠ 0#64)
    (hp8 : p8 ≠ 0#64) (hp9 : p9 ≠ 0#64) (hp10 : p10 ≠ 0#64) (hp11 : p11 ≠ 0#64)
    (hp12 : p12 ≠ 0#64) (hp13 : p13 ≠ 0#64) (hp14 : p14 ≠ 0#64) (hp15 : p15 ≠ 0#64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 940#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = p15) (hx19 : s.readReg64 .x19 = p8)
    (hx20 : s.readReg64 .x20 = p0) (hx21 : s.readReg64 .x21 = p9)
    (hx23 : s.readReg64 .x23 = p10) (hx24 : s.readReg64 .x24 = p11)
    (hx25 : s.readReg64 .x25 = p12) (hx26 : s.readReg64 .x26 = p13)
    (hx27 : s.readReg64 .x27 = p14) (hx29 : s.readReg64 .x29 = fsp + 928#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName + 1204#64)
      s
      ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
        ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
        A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
        A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗
        A.live p8 2 2 ∗ memRegion p8 2 ∗ A.live p9 2 2 ∗ memRegion p9 2 ∗
        A.live p10 2 2 ∗ memRegion p10 2 ∗ A.live p11 2 2 ∗ memRegion p11 2 ∗
        A.live p12 2 2 ∗ memRegion p12 2 ∗ A.live p13 2 2 ∗ memRegion p13 2 ∗
        A.live p14 2 2 ∗ memRegion p14 2 ∗ A.live p15 2 2 ∗ memRegion p15 2 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          cells fsp 7 ∗
          ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
          ((pbA + 32#64) ↦₆₄ polysPtr) ∗
          zeroPolySlotsAt A (fsp + 480#64) 16 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x22 = 0#64 ∧
        sm.readReg64 .x23 = fsp + 864#64 ∧
        sm.readReg64 .x24 = polysPtr ∧
        sm.readReg64 .x28 = 0#64 ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 940 228
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  rw [show
      ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
        ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
        A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
        A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗
        A.live p8 2 2 ∗ memRegion p8 2 ∗ A.live p9 2 2 ∗ memRegion p9 2 ∗
        A.live p10 2 2 ∗ memRegion p10 2 ∗ A.live p11 2 2 ∗ memRegion p11 2 ∗
        A.live p12 2 2 ∗ memRegion p12 2 ∗ A.live p13 2 2 ∗ memRegion p13 2 ∗
        A.live p14 2 2 ∗ memRegion p14 2 ∗ A.live p15 2 2 ∗ memRegion p15 2 ∗ Frame) =
      (cells (fsp + 480#64) 48 ∗
       ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
        ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
        A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
        A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗
        A.live p8 2 2 ∗ memRegion p8 2 ∗ A.live p9 2 2 ∗ memRegion p9 2 ∗
        A.live p10 2 2 ∗ memRegion p10 2 ∗ A.live p11 2 2 ∗ memRegion p11 2 ∗
        A.live p12 2 2 ∗ memRegion p12 2 ∗ A.live p13 2 2 ∗ memRegion p13 2 ∗
        A.live p14 2 2 ∗ memRegion p14 2 ∗ A.live p15 2 2 ∗ memRegion p15 2 ∗ Frame)) by ac_rfl]
  iterate 48 (apply sepWP_cells_succ; intro _)
  apply sepWP_cells_zero
  simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  wp_steps
  refine align_pre ?_ ?_
  · have hc7 :
        (fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
          ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ⊢
          cells fsp 7 := by
      rw [ProofLib.cells_succ]; refine Entails.sepExists_right p7 (sepConj_mono_right ?_)
      rw [ProofLib.cells_succ]; refine Entails.sepExists_right p6 ?_
      simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; refine sepConj_mono_right ?_
      rw [ProofLib.cells_succ]; refine Entails.sepExists_right p5 ?_
      simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; refine sepConj_mono_right ?_
      rw [ProofLib.cells_succ]; refine Entails.sepExists_right p4 ?_
      simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; refine sepConj_mono_right ?_
      rw [ProofLib.cells_succ]; refine Entails.sepExists_right p3 ?_
      simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; refine sepConj_mono_right ?_
      rw [ProofLib.cells_succ]; refine Entails.sepExists_right p2 ?_
      simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; refine sepConj_mono_right ?_
      rw [ProofLib.cells_succ, ProofLib.cells_zero]
      simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_emp]
      exact Entails.sepExists_right p1 (Entails.refl _)
    dsimp only [zeroPolySlotsAt]
    simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_emp, sepConj_assoc]
    have hz0 := zeroPolySlotAt_intro A (fsp + 480#64) p0 hp0
    have hz1 := zeroPolySlotAt_intro A (fsp + 504#64) p1 hp1
    have hz2 := zeroPolySlotAt_intro A (fsp + 528#64) p2 hp2
    have hz3 := zeroPolySlotAt_intro A (fsp + 552#64) p3 hp3
    have hz4 := zeroPolySlotAt_intro A (fsp + 576#64) p4 hp4
    have hz5 := zeroPolySlotAt_intro A (fsp + 600#64) p5 hp5
    have hz6 := zeroPolySlotAt_intro A (fsp + 624#64) p6 hp6
    have hz7 := zeroPolySlotAt_intro A (fsp + 648#64) p7 hp7
    have hz8 := zeroPolySlotAt_intro A (fsp + 672#64) p8 hp8
    have hz9 := zeroPolySlotAt_intro A (fsp + 696#64) p9 hp9
    have hz10 := zeroPolySlotAt_intro A (fsp + 720#64) p10 hp10
    have hz11 := zeroPolySlotAt_intro A (fsp + 744#64) p11 hp11
    have hz12 := zeroPolySlotAt_intro A (fsp + 768#64) p12 hp12
    have hz13 := zeroPolySlotAt_intro A (fsp + 792#64) p13 hp13
    have hz14 := zeroPolySlotAt_intro A (fsp + 816#64) p14 hp14
    have hz15 := zeroPolySlotAt_intro A (fsp + 840#64) p15 hp15
    simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hz0 hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8 hz9 hz10 hz11 hz12 hz13 hz14 hz15
    refine Entails.trans ?_
      (sepConj_mono hc7 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hz0 (sepConj_mono hz1 (sepConj_mono hz2 (sepConj_mono hz3
        (sepConj_mono hz4 (sepConj_mono hz5 (sepConj_mono hz6 (sepConj_mono hz7
        (sepConj_mono hz8 (sepConj_mono hz9 (sepConj_mono hz10 (sepConj_mono hz11
        (sepConj_mono hz12 (sepConj_mono hz13 (sepConj_mono hz14
        (sepConj_mono_left hz15))))))))))))))))))))
    exact Entails.of_eq (by ac_rfl)
  · wp_done

/-- Combined 16-slot `Poly::zero()` initialization (`+556 -> +1204`, `0x22c -> 0x4b4`). -/
theorem polys_init_zero_headers {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out pbA polysPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 556#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out) (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 928#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm,
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 1204#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x22 = 0#64 → sm.readReg64 .x23 = fsp + 864#64 →
      sm.readReg64 .x24 = polysPtr → sm.readReg64 .x28 = 0#64 →
      sm.readReg64 .x29 = fsp + 928#64 → sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (cells fsp 7 ∗
          ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
          ((pbA + 32#64) ↦₆₄ polysPtr) ∗
          zeroPolySlotsAt A (fsp + 480#64) 16 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (cells fsp 4 ∗ cells (fsp + 32#64) 5 ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        cells (fsp + 480#64) 48 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (polys_alloc_0_3 hA s0 s fsp out pbA hfsp_align
      (cells fsp 4 ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗ cells (fsp + 480#64) 48 ∗ Frame)
      R hpc hrun hsp hx0 hx1 htrace hvregs ?_)
  intro s1 p0 p1 p2 p3 hp0 hp1 hp2 hp3 hpc1 hrun1 hsp1 hx20_1 hx29_1 htr1 hvregs1
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (polys_alloc_4_7 hA s0 s1 fsp hfsp_align
      (((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗ Frame)
      R hpc1 hrun1 hsp1 htr1 hvregs1 ?_)
  intro s2 p4 p5 p6 p7 hp4 hp5 hp6 hp7 hpc2 hrun2 hsp2 hx20_2 hx29_2 htr2 hvregs2
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (polys_alloc_8_11 hA s0 s2 fsp hfsp_align
      ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
        ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
        A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
        A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗ Frame)
      R hpc2 hrun2 hsp2 htr2 hvregs2 ?_)
  intro s3 p8 p9 p10 p11 hp8 hp9 hp10 hp11 hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx23_3 hx24_3 hx29_3 htr3 hvregs3
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (polys_alloc_12_15 hA s0 s3 fsp hfsp_align
      ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
        ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
        A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
        A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗
        A.live p8 2 2 ∗ memRegion p8 2 ∗ A.live p9 2 2 ∗ memRegion p9 2 ∗
        A.live p10 2 2 ∗ memRegion p10 2 ∗ A.live p11 2 2 ∗ memRegion p11 2 ∗ Frame)
      R hpc3 hrun3 hsp3 htr3 hvregs3 ?_)
  intro s4 p12 p13 p14 p15 hp12 hp13 hp14 hp15 hpc4 hrun4 hsp4
    hx0_4 hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4 htr4 hvregs4
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (sepWPp_seq_clean
      (polys_init_scatter (A := A) (b := b) (ext := ext) s4 fsp out pbA polysPtr
        p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
        hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15
        hfsp_align (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        hpc4 hrun4 hsp4 hx0_4
        (by rw [hx19_4, hx19_3])
        (by rw [hx20_4, hx20_3, hx20_2, hx20_1])
        (by rw [hx21_4, hx21_3])
        (by rw [hx23_4, hx23_3])
        (by rw [hx24_4, hx24_3])
        hx25_4 hx26_4 hx27_4
        (by rw [hx29_4, hx29_3, hx29_2, hx29_1, hx29]))
      ?_)
  intro s5 hpc5 hrun5 ⟨hsp5, hx22_5, hx23_5, hx24_5, hx28_5, hx29_5, htr5, hvregs5⟩
  exact hcont s5 hpc5 hrun5 hsp5 hx22_5 hx23_5 hx24_5 hx28_5 hx29_5 (by rw [htr5, htr4]) (by rw [hvregs5, hvregs4])

/-! ## `.polys` Inner `GF16` Deserialization Loop (`+1308 -> +1356`, `0x51c -> 0x54c`) -/

/-- `.polys` inner loop (`+1308 -> +1356`, `0x51c -> 0x54c`): converts `bs` of length `2 * (n + 1)`
    starting at byte offset `2 * k` (`2 * k + bs.length = 2 * totalGF16`) into `n + 1` `GF16`
    elements at `outPtr + 2 * k`. -/
theorem polys_inner_loop {b : BitVec 64} {ext : String → Option (State → State)} :
    ∀ (n : Nat) (bs : List (BitVec 8)) (k totalGF16 : Nat) (s : State)
      (fsp bsPtr outPtr v_len : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp),
      bs.length = 2 * (n + 1) →
      k + (n + 1) = totalGF16 →
      2 * totalGF16 < 2 ^ 63 →
      s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1308#64 →
      s.status = .Running →
      s.sp = fsp →
      s.readReg64 .x0 = outPtr →
      s.readReg64 .x19 = bsPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 (2 * totalGF16) →
      s.readReg64 .x26 = BitVec.ofNat 64 (2 * k) →
      s.readReg64 .x27 = BitVec.ofNat 64 (k + 1) →
      s.readReg64 .x29 = fsp + 928#64 →
      SepWP (contractProg b ext)
        ((contractProg b ext).fnAddr encoderFromPbName + 1356#64)
        s
        (((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 totalGF16) ∗
          ((fsp + 912#64) ↦₆₄ v_len) ∗
          ((bsPtr + BitVec.ofNat 64 (2 * k)) ↦ₛ bs) ∗
          memRegion (outPtr + BitVec.ofNat 64 (2 * k)) bs.length ∗
          Frame)
        (fun sm Pm =>
          (Pm ⊢ ((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 totalGF16) ∗
            ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (k + n + 1)) ∗
            ((bsPtr + BitVec.ofNat 64 (2 * k)) ↦ₛ bs) ∗
            arrayAt gf16At 2 (outPtr + BitVec.ofNat 64 (2 * k)) (bytesToGF16ListTotal bs) ∗
            Frame) ∧
          sm.sp = fsp ∧
          sm.readReg64 .x0 = outPtr ∧
          sm.readReg64 .x19 = bsPtr ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (2 * totalGF16) ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x23 = s.readReg64 .x23 ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x28 = s.readReg64 .x28 ∧
          sm.readReg64 .x29 = fsp + 928#64 ∧
          sm.trace = s.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s) := by
  intro n
  induction n with
  | zero =>
    intro bs k totalGF16 s fsp bsPtr outPtr v_len hfsp_align Frame
      hlen htot hmax hpc hrun hsp hx0 hx19 hx21 hx26 hx27 hx29
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · encoder_from_pb_fetches_range b (Rust.withPanics ext) 1280 76
      dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
      examples_hide_fetches
      have htot2 : 2 * k + 2 = 2 * totalGF16 := by omega
      have hlt1 : 2 * k < 2 * totalGF16 := by omega
      have hlt2 : 2 * k + 1 < 2 * totalGF16 := by omega
      have hk_lt : k < totalGF16 := by omega
      have hmax64 : 2 * totalGF16 < 2 ^ 64 := by omega
      have hgf64 : totalGF16 < 2 ^ 64 := by omega
      have h_ule1 : BitVec.ule (BitVec.ofNat 64 (2 * totalGF16)) (BitVec.ofNat 64 (2 * k)) = false :=
        ule_false_of_lt hlt1 hmax64
      have h_ult1 : BitVec.ult (BitVec.ofNat 64 (2 * k)) (BitVec.ofNat 64 (2 * totalGF16)) = true :=
        ult_of_lt hlt1 hmax64
      have h_ule2 : BitVec.ule (BitVec.ofNat 64 (2 * totalGF16)) (BitVec.ofNat 64 (2 * k + 1)) = false :=
        ule_false_of_lt hlt2 hmax64
      have h_ult2 : BitVec.ult (BitVec.ofNat 64 (2 * k + 1)) (BitVec.ofNat 64 (2 * totalGF16)) = true :=
        ult_of_lt hlt2 hmax64
      have h_bne : (BitVec.ofNat 64 k != BitVec.ofNat 64 totalGF16) = true :=
        bne_of_lt hk_lt hgf64
      have h_bne' : (BitVec.ofNat 64 totalGF16 != BitVec.ofNat 64 k) = true :=
        bne_of_gt hk_lt hgf64
      have h_beq : (BitVec.ofNat 64 k == BitVec.ofNat 64 totalGF16) = false :=
        beq_false_of_lt hk_lt hgf64
      have h_beq' : (BitVec.ofNat 64 totalGF16 == BitVec.ofNat 64 k) = false :=
        beq_false_of_gt hk_lt hgf64
      have h_end_eq : BitVec.ofNat 64 (2 * k + 2) = BitVec.ofNat 64 (2 * totalGF16) :=
        congrArg (BitVec.ofNat 64) htot2
      have htot1 : k + 1 = totalGF16 := by omega
      rw [pointsToBytes_pair_cons (bsPtr + BitVec.ofNat 64 (2 * k)) b0 b1 []]
      dsimp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
      rw [ProofLib.memRegion_two (outPtr + BitVec.ofNat 64 (2 * k))]
      simp only [ProofLib.pointsToBytes_nil, sepConj_emp, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro d16
      wp_steps
      refine align_pre ?_ ?_
      · dsimp only [bytesToGF16ListTotal, arrayAt, gf16At, GF16.new]
        simp only [ProofLib.pointsToBytes_nil, Nat.add_zero, htot1, sepConj_emp,
          rev16_pair_eq_u16FromBeBytes]
        exact Entails.of_eq (by ac_rfl)
      · wp_done
    · simp at hlen
  | succ n ih =>
    intro bs k totalGF16 s fsp bsPtr outPtr v_len hfsp_align Frame
      hlen htot hmax hpc hrun hsp hx0 hx19 hx21 hx26 hx27 hx29
    rcases bs with _ | ⟨b0, _ | ⟨b1, bs'⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · have hlen' : bs'.length = 2 * (n + 1) := by simp at hlen; omega
      have htot' : (k + 1) + (n + 1) = totalGF16 := by omega
      have hlt1 : 2 * k < 2 * totalGF16 := by omega
      have hlt2 : 2 * k + 1 < 2 * totalGF16 := by omega
      have hlt3 : 2 * k + 2 < 2 * totalGF16 := by omega
      have hk_lt : k < totalGF16 := by omega
      have hmax64 : 2 * totalGF16 < 2 ^ 64 := by omega
      have hgf64 : totalGF16 < 2 ^ 64 := by omega
      have h_ule1 : BitVec.ule (BitVec.ofNat 64 (2 * totalGF16)) (BitVec.ofNat 64 (2 * k)) = false :=
        ule_false_of_lt hlt1 hmax64
      have h_ult1 : BitVec.ult (BitVec.ofNat 64 (2 * k)) (BitVec.ofNat 64 (2 * totalGF16)) = true :=
        ult_of_lt hlt1 hmax64
      have h_ule2 : BitVec.ule (BitVec.ofNat 64 (2 * totalGF16)) (BitVec.ofNat 64 (2 * k + 1)) = false :=
        ule_false_of_lt hlt2 hmax64
      have h_ult2 : BitVec.ult (BitVec.ofNat 64 (2 * k + 1)) (BitVec.ofNat 64 (2 * totalGF16)) = true :=
        ult_of_lt hlt2 hmax64
      have h_ule3 : BitVec.ule (BitVec.ofNat 64 (2 * totalGF16)) (BitVec.ofNat 64 (2 * k + 2)) = false :=
        ule_false_of_lt hlt3 hmax64
      have h_ult3 : BitVec.ult (BitVec.ofNat 64 (2 * k + 2)) (BitVec.ofNat 64 (2 * totalGF16)) = true :=
        ult_of_lt hlt3 hmax64
      have h_bne : (BitVec.ofNat 64 k != BitVec.ofNat 64 totalGF16) = true :=
        bne_of_lt hk_lt hgf64
      have h_bne' : (BitVec.ofNat 64 totalGF16 != BitVec.ofNat 64 k) = true :=
        bne_of_gt hk_lt hgf64
      have h_beq : (BitVec.ofNat 64 k == BitVec.ofNat 64 totalGF16) = false :=
        beq_false_of_lt hk_lt hgf64
      have h_beq' : (BitVec.ofNat 64 totalGF16 == BitVec.ofNat 64 k) = false :=
        beq_false_of_gt hk_lt hgf64
      have hbs_len_eq : (b0 :: b1 :: bs').length = 2 * ((n + 1) + 1) := by
        simp [hlen']; omega
      have hbs_addr : bsPtr + BitVec.ofNat 64 (2 * k + 2) = bsPtr + BitVec.ofNat 64 (2 * (k + 1)) := by
        congr 2
      rw [pointsToBytes_pair_cons (bsPtr + BitVec.ofNat 64 (2 * k)) b0 b1 bs',
          bv_add_lit_add_lit, hbs_addr, hbs_len_eq,
          memRegion_two_cons outPtr k (n + 1) (by omega),
          ← hlen']
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro d16
      refine seq_clean
        (mid := (contractProg b ext).fnAddr encoderFromPbName + 1308#64)
        (P_mid :=
          ((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 totalGF16) ∗
          ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          ((bsPtr + BitVec.ofNat 64 (2 * (k + 1))) ↦ₛ bs') ∗
          memRegion (outPtr + BitVec.ofNat 64 (2 * (k + 1))) bs'.length ∗
          (((bsPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ (b1 ++ b0)) ∗
            ((outPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ u16FromBeBytes b0 b1) ∗
            Frame))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x0 = outPtr ∧
          sm.readReg64 .x19 = bsPtr ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (2 * totalGF16) ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x23 = s.readReg64 .x23 ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x26 = BitVec.ofNat 64 (2 * (k + 1)) ∧
          sm.readReg64 .x27 = BitVec.ofNat 64 ((k + 1) + 1) ∧
          sm.readReg64 .x28 = s.readReg64 .x28 ∧
          sm.readReg64 .x29 = fsp + 928#64 ∧
          sm.trace = s.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s)
        ?_ ?_
      · encoder_from_pb_fetches_range b (Rust.withPanics ext) 1280 76
        dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase b
          (Rust.withPanics ext)).fnAddr
          "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine align_pre ?_ ?_
        · simp only [rev16_pair_eq_u16FromBeBytes]
          exact Entails.of_eq (by ac_rfl)
        · have hk2 : BitVec.ofNat 64 (2 * k + 2) = BitVec.ofNat 64 (2 * (k + 1)) := by
            congr 1
          wp_done
      · intro sm hpcm hrunm ⟨hspm, hx0m, hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx26m, hx27m, hx28m, hx29m, htrm, hvregsm⟩
        have hstep := ih bs' (k + 1) totalGF16 sm fsp bsPtr outPtr (BitVec.ofNat 64 (k + 1))
          hfsp_align
          (((bsPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ (b1 ++ b0)) ∗
            ((outPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ u16FromBeBytes b0 b1) ∗
            Frame)
          hlen' htot' hmax hpcm hrunm hspm hx0m hx19m hx21m hx26m hx27m hx29m
        refine SepWP.mono hstep ?_
        intro sf Pf hpcf hrunf ⟨hPf, hspf, hx0f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx28f, hx29f, htrf, hvregsf⟩
        refine ⟨Entails.trans hPf ?_, hspf, hx0f, hx19f, by rw [hx20f, hx20m],
          hx21f, by rw [hx22f, hx22m], by rw [hx23f, hx23m], by rw [hx24f, hx24m],
          by rw [hx28f, hx28m], hx29f, by rw [htrf, htrm], by rw [hvregsf, hvregsm]⟩
        have hk_assoc : (k + 1) + n + 1 = k + (n + 1) + 1 := by omega
        have hout_addr : outPtr + BitVec.ofNat 64 (2 * k) + 2#64 =
            outPtr + BitVec.ofNat 64 (2 * (k + 1)) := by
          rw [BitVec.add_assoc, ofNat_add_two]
        dsimp only [bytesToGF16ListTotal, arrayAt, gf16At, GF16.new, BitVec.ofNat_eq_ofNat]
        rw [hk_assoc, hout_addr]
        exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Poly.EncoderFromPb
