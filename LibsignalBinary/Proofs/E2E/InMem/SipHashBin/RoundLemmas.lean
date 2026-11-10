/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Defs
public import ProofLib.SepLogic.Bytes
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.SepLogic.WP.StateNorm
import VCVio.Prelude.Core

/-!
# SipHash-1-3 Bitvector and Round Bridge Lemmas

Equivalences relating `UInt64` operations in `SipHashModel` (`rotl64`, `compress`,
`compressBlock`, `u8to64Le`, `loadU64Le`) to the `BitVec 64` shifts, rotations, and
little-endian word packings (`pack32`, `pack64`) produced by ARM64 symbolic execution.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.SipHashBin

open Arm64 ProofLib
open CryptoVerification.E2E.InMem.SipHashModel

/-! ## `UInt64` and `BitVec 64` Conversions -/

@[simp]
theorem toBitVec_ofBitVec64 (x : BitVec 64) : (UInt64.ofBitVec x).toBitVec = x := rfl

@[simp]
theorem ofBitVec_toBitVec64 (u : UInt64) : UInt64.ofBitVec u.toBitVec = u := rfl

@[simp]
theorem toBitVec_add64 (a b : UInt64) : (a + b).toBitVec = a.toBitVec + b.toBitVec := rfl

@[simp]
theorem toBitVec_xor64 (a b : UInt64) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

@[simp]
theorem toBitVec_or64 (a b : UInt64) : (a ||| b).toBitVec = a.toBitVec ||| b.toBitVec := rfl

@[simp]
theorem toBitVec_shl64 (a b : UInt64) :
    (a <<< b).toBitVec = a.toBitVec <<< (b.toBitVec.umod 64#64) := rfl

@[simp]
theorem toBitVec_ushr64 (a b : UInt64) :
    (a >>> b).toBitVec = a.toBitVec >>> (b.toBitVec.umod 64#64) := rfl

/-! ## Rotation Equivalences -/

theorem shl_or_ushr_eq_rotateRight (x : BitVec 64) (k : Nat) (hk0 : 0 < k) (hk64 : k < 64) :
    (x <<< k) ||| (x >>> (64 - k)) = x.rotateRight (64 - k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_rotateRight, hi]
  have hmod : (64 - k) % 64 = 64 - k := Nat.mod_eq_of_lt (by omega)
  have hsub : 64 - (64 - k) = k := by omega
  rw [hmod, hsub]
  by_cases hik : i < k
  · simp [hik]
  · have hge : 64 ≤ 64 - k + i := by omega
    simp [hik, BitVec.getLsbD_of_ge x (64 - k + i) hge]

theorem toBitVec_rotl64_13 (u : UInt64) :
    (rotl64 u 13).toBitVec = u.toBitVec.rotateRight 51 :=
  shl_or_ushr_eq_rotateRight u.toBitVec 13 (by decide) (by decide)

theorem toBitVec_rotl64_16 (u : UInt64) :
    (rotl64 u 16).toBitVec = u.toBitVec.rotateRight 48 :=
  shl_or_ushr_eq_rotateRight u.toBitVec 16 (by decide) (by decide)

theorem toBitVec_rotl64_17 (u : UInt64) :
    (rotl64 u 17).toBitVec = u.toBitVec.rotateRight 47 :=
  shl_or_ushr_eq_rotateRight u.toBitVec 17 (by decide) (by decide)

theorem toBitVec_rotl64_21 (u : UInt64) :
    (rotl64 u 21).toBitVec = u.toBitVec.rotateRight 43 :=
  shl_or_ushr_eq_rotateRight u.toBitVec 21 (by decide) (by decide)

theorem toBitVec_rotl64_32 (u : UInt64) :
    (rotl64 u 32).toBitVec = u.toBitVec.rotateRight 32 :=
  shl_or_ushr_eq_rotateRight u.toBitVec 32 (by decide) (by decide)

@[simp, arm64_norm]
theorem setWidth64_append_ushiftRight_32_eq_rotateRight (x : BitVec 64) :
    BitVec.setWidth 64 ((x ++ x) >>> 32) = x.rotateRight 32 := by
  rw [setWidth64_append_ushiftRight_eq_rotateLeft x 32 32,
      rotateRight64_eq_rotateLeft64 x 32 32]

@[simp, arm64_norm]
theorem setWidth64_append_ushiftRight_51_eq_rotateRight (x : BitVec 64) :
    BitVec.setWidth 64 ((x ++ x) >>> 51) = x.rotateRight 51 := by
  rw [setWidth64_append_ushiftRight_eq_rotateLeft x 51 13,
      rotateRight64_eq_rotateLeft64 x 51 13]

@[simp, arm64_norm]
theorem setWidth64_append_ushiftRight_48_eq_rotateRight (x : BitVec 64) :
    BitVec.setWidth 64 ((x ++ x) >>> 48) = x.rotateRight 48 := by
  rw [setWidth64_append_ushiftRight_eq_rotateLeft x 48 16,
      rotateRight64_eq_rotateLeft64 x 48 16]

@[simp, arm64_norm]
theorem setWidth64_append_ushiftRight_47_eq_rotateRight (x : BitVec 64) :
    BitVec.setWidth 64 ((x ++ x) >>> 47) = x.rotateRight 47 := by
  rw [setWidth64_append_ushiftRight_eq_rotateLeft x 47 17,
      rotateRight64_eq_rotateLeft64 x 47 17]

@[simp, arm64_norm]
theorem setWidth64_append_ushiftRight_43_eq_rotateRight (x : BitVec 64) :
    BitVec.setWidth 64 ((x ++ x) >>> 43) = x.rotateRight 43 := by
  rw [setWidth64_append_ushiftRight_eq_rotateLeft x 43 21,
      rotateRight64_eq_rotateLeft64 x 43 21]

/-! ## `compress` and `compressBlock` in `BitVec 64` Form -/

/-- Pure `BitVec 64` formulation of one SipRound (`SipHashModel.compress`). -/
def compressBv (v0 v1 v2 v3 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let v0 := v1 + v0
  let v2 := v2 + v3
  let v1 := v0 ^^^ (v1.rotateRight 51)
  let v3 := v2 ^^^ (v3.rotateRight 48)
  let v0 := v0.rotateRight 32
  let v2 := v2 + v1
  let v0 := v3 + v0
  let v1 := v2 ^^^ (v1.rotateRight 47)
  let v3 := v0 ^^^ (v3.rotateRight 43)
  let v2 := v2.rotateRight 32
  (v0, v1, v2, v3)

theorem compress_toBitVec_aux (v0 v1 v2 v3 : BitVec 64) :
    (let v0 := v0 + v1
     let v1 := v1.rotateRight 51 ^^^ v0
     let v0 := v0.rotateRight 32
     let v2 := v2 + v3
     let v3 := v3.rotateRight 48 ^^^ v2
     let v0 := v0 + v3
     let v3 := v3.rotateRight 43 ^^^ v0
     let v2 := v2 + v1
     let v1 := v1.rotateRight 47 ^^^ v2
     let v2 := v2.rotateRight 32
     (v0, v1, v2, v3)) = compressBv v0 v1 v2 v3 := by
  dsimp only [compressBv]
  rw [BitVec.add_comm v0 v1]
  rw [BitVec.xor_comm (v1.rotateRight 51) (v1 + v0)]
  rw [BitVec.xor_comm (v3.rotateRight 48) (v2 + v3)]
  rw [BitVec.add_comm ((v1 + v0).rotateRight 32) ((v2 + v3) ^^^ v3.rotateRight 48)]
  rw [BitVec.xor_comm (((v2 + v3) ^^^ v3.rotateRight 48).rotateRight 43)]
  rw [BitVec.xor_comm (((v1 + v0) ^^^ v1.rotateRight 51).rotateRight 47)]

theorem compress_toBitVec (st : SipHashModel.State) :
    ((SipHashModel.compress st).v0.toBitVec, (SipHashModel.compress st).v1.toBitVec,
     (SipHashModel.compress st).v2.toBitVec, (SipHashModel.compress st).v3.toBitVec) =
      compressBv st.v0.toBitVec st.v1.toBitVec st.v2.toBitVec st.v3.toBitVec := by
  unfold SipHashModel.compress
  simp only [toBitVec_add64, toBitVec_xor64,
    toBitVec_rotl64_13, toBitVec_rotl64_16, toBitVec_rotl64_17,
    toBitVec_rotl64_21, toBitVec_rotl64_32]
  exact compress_toBitVec_aux st.v0.toBitVec st.v1.toBitVec st.v2.toBitVec st.v3.toBitVec

def stateOfBv (v0 v1 v2 v3 : BitVec 64) : SipHashModel.State :=
  { v0 := UInt64.ofBitVec v0
    v1 := UInt64.ofBitVec v1
    v2 := UInt64.ofBitVec v2
    v3 := UInt64.ofBitVec v3 }

theorem eq_stateOfBv (st : SipHashModel.State) :
    st = stateOfBv st.v0.toBitVec st.v1.toBitVec st.v2.toBitVec st.v3.toBitVec := by
  cases st; rfl

theorem sipStateAt_stateOfBv (a : BitVec 64) (v0 v1 v2 v3 : BitVec 64) :
    sipStateAt a (stateOfBv v0 v1 v2 v3) =
      (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v2) ∗ ((a + 16#64) ↦₆₄ v1) ∗ ((a + 24#64) ↦₆₄ v3) := rfl

theorem state_ext {s1 s2 : SipHashModel.State}
    (h0 : s1.v0.toBitVec = s2.v0.toBitVec)
    (h1 : s1.v1.toBitVec = s2.v1.toBitVec)
    (h2 : s1.v2.toBitVec = s2.v2.toBitVec)
    (h3 : s1.v3.toBitVec = s2.v3.toBitVec) : s1 = s2 := by
  cases s1; cases s2
  dsimp only at h0 h1 h2 h3
  have e0 := congrArg UInt64.ofBitVec h0
  have e1 := congrArg UInt64.ofBitVec h1
  have e2 := congrArg UInt64.ofBitVec h2
  have e3 := congrArg UInt64.ofBitVec h3
  simp only [UInt64.ofBitVec_toBitVec] at e0 e1 e2 e3
  subst e0 e1 e2 e3; rfl

theorem compress_stateOfBv (v0 v1 v2 v3 : BitVec 64) :
    SipHashModel.compress (stateOfBv v0 v1 v2 v3) =
      stateOfBv
        (compressBv v0 v1 v2 v3).1
        (compressBv v0 v1 v2 v3).2.1
        (compressBv v0 v1 v2 v3).2.2.1
        (compressBv v0 v1 v2 v3).2.2.2 := by
  have h := compress_toBitVec (stateOfBv v0 v1 v2 v3)
  dsimp only [stateOfBv, UInt64.toBitVec_ofBitVec] at h
  rw [Prod.mk.injEq] at h; rcases h with ⟨h0, h⟩
  rw [Prod.mk.injEq] at h; rcases h with ⟨h1, h⟩
  rw [Prod.mk.injEq] at h; rcases h with ⟨h2, h3⟩
  exact state_ext h0 h1 h2 h3

theorem compressBlock_stateOfBv (v0 v1 v2 v3 : BitVec 64) (m : UInt64) :
    SipHashModel.compressBlock (stateOfBv v0 v1 v2 v3) m =
      stateOfBv
        ((compressBv v0 v1 v2 (v3 ^^^ m.toBitVec)).1 ^^^ m.toBitVec)
        (compressBv v0 v1 v2 (v3 ^^^ m.toBitVec)).2.1
        (compressBv v0 v1 v2 (v3 ^^^ m.toBitVec)).2.2.1
        (compressBv v0 v1 v2 (v3 ^^^ m.toBitVec)).2.2.2 := by
  unfold SipHashModel.compressBlock SipHashModel.cRounds
  have hsub : { stateOfBv v0 v1 v2 v3 with v3 := (stateOfBv v0 v1 v2 v3).v3 ^^^ m } =
      stateOfBv v0 v1 v2 (v3 ^^^ m.toBitVec) := by
    apply state_ext <;> simp [stateOfBv]
  rw [hsub]
  dsimp only
  rw [compress_stateOfBv]
  apply state_ext <;> simp [stateOfBv]

/-! ## Little-Endian Byte-Packing Bridges -/

theorem toBitVec_toUInt64_ofBitVec8 (b : BitVec 8) :
    (UInt8.ofBitVec b).toUInt64.toBitVec = b.zeroExtend 64 := by
  revert b; decide

theorem getD_map_ofBitVec8 (msg : List (BitVec 8)) (i : Nat) :
    (msg.map UInt8.ofBitVec).getD i 0 = UInt8.ofBitVec (msg.getD i 0#8) := by
  induction msg generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

theorem toBitVec_byteAt64_map (msg : List (BitVec 8)) (i : Nat) :
    (SipHashModel.byteAt64 (msg.map UInt8.ofBitVec) i).toBitVec = (msg.getD i 0#8).zeroExtend 64 := by
  unfold SipHashModel.byteAt64
  rw [getD_map_ofBitVec8, toBitVec_toUInt64_ofBitVec8]

theorem toBitVec_u8to64Le_4 (msg : List (BitVec 8)) (start : Nat) :
    (SipHashModel.u8to64Le (msg.map UInt8.ofBitVec) start 4).toBitVec =
      (pack32 (msg.getD start 0#8) (msg.getD (start + 1) 0#8)
        (msg.getD (start + 2) 0#8) (msg.getD (start + 3) 0#8)).zeroExtend 64 := by
  rw [pack32_zeroExtend64]
  simp only [SipHashModel.u8to64Le, Nat.add_zero, Nat.mul_zero, Nat.mul_one,
    toBitVec_or64, toBitVec_shl64, toBitVec_byteAt64_map]
  have h0 : (0#64 : BitVec 64) ||| ((msg.getD start 0#8).zeroExtend 64 <<< 0#64) =
      (msg.getD start 0#8).zeroExtend 64 := by simp
  change ((0#64 ||| ((msg.getD start 0#8).zeroExtend 64 <<< 0#64)) |||
      ((msg.getD (start + 1) 0#8).zeroExtend 64 <<< 8#64) |||
      ((msg.getD (start + 2) 0#8).zeroExtend 64 <<< 16#64) |||
      ((msg.getD (start + 3) 0#8).zeroExtend 64 <<< 24#64)) =
    ((msg.getD start 0#8).zeroExtend 64 |||
      ((msg.getD (start + 1) 0#8).zeroExtend 64 <<< 8) |||
      ((msg.getD (start + 2) 0#8).zeroExtend 64 <<< 16) |||
      ((msg.getD (start + 3) 0#8).zeroExtend 64 <<< 24))
  rw [h0]; rfl

private theorem append56_8_eq (x : BitVec 56) (b0 : BitVec 8) :
    (x ++ b0 : BitVec 64) = b0.zeroExtend 64 ||| ((x.zeroExtend 64) <<< 8) := by
  bv_bits

private theorem append48_8_eq (x : BitVec 48) (b1 : BitVec 8) :
    ((x ++ b1).zeroExtend 64) <<< 8 =
      ((b1.zeroExtend 64) <<< 8) ||| ((x.zeroExtend 64) <<< 16) := by
  bv_bits

private theorem append40_8_eq (x : BitVec 40) (b2 : BitVec 8) :
    ((x ++ b2).zeroExtend 64) <<< 16 =
      ((b2.zeroExtend 64) <<< 16) ||| ((x.zeroExtend 64) <<< 24) := by
  bv_bits

private theorem append32_8_eq (x : BitVec 32) (b3 : BitVec 8) :
    ((x ++ b3).zeroExtend 64) <<< 24 =
      ((b3.zeroExtend 64) <<< 24) ||| ((x.zeroExtend 64) <<< 32) := by
  bv_bits

private theorem shl_shl_64 (b : BitVec 8) (k m : Nat) :
    ((b.zeroExtend 64) <<< k) <<< m = (b.zeroExtend 64) <<< (k + m) := by
  rw [BitVec.shiftLeft_add]

theorem pack64_eq_or_shifts (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    pack64 b0 b1 b2 b3 b4 b5 b6 b7 =
      b0.zeroExtend 64 ||| ((b1.zeroExtend 64) <<< 8) |||
      ((b2.zeroExtend 64) <<< 16) ||| ((b3.zeroExtend 64) <<< 24) |||
      ((b4.zeroExtend 64) <<< 32) ||| ((b5.zeroExtend 64) <<< 40) |||
      ((b6.zeroExtend 64) <<< 48) ||| ((b7.zeroExtend 64) <<< 56) := by
  unfold pack64
  rw [append56_8_eq, append48_8_eq, append40_8_eq, append32_8_eq]
  change b0.zeroExtend 64 |||
      (((b1.zeroExtend 64) <<< 8) |||
       (((b2.zeroExtend 64) <<< 16) |||
        (((b3.zeroExtend 64) <<< 24) ||| (((pack32 b4 b5 b6 b7).zeroExtend 64) <<< 32)))) = _
  rw [pack32_zeroExtend64]
  simp only [BitVec.shiftLeft_or_distrib, shl_shl_64, BitVec.or_assoc]

theorem toBitVec_loadU64Le (msg : List (BitVec 8)) (start : Nat) :
    (SipHashModel.loadU64Le (msg.map UInt8.ofBitVec) start).toBitVec =
      pack64 (msg.getD start 0#8) (msg.getD (start + 1) 0#8)
        (msg.getD (start + 2) 0#8) (msg.getD (start + 3) 0#8)
        (msg.getD (start + 4) 0#8) (msg.getD (start + 5) 0#8)
        (msg.getD (start + 6) 0#8) (msg.getD (start + 7) 0#8) := by
  rw [pack64_eq_or_shifts]
  unfold SipHashModel.loadU64Le
  simp only [toBitVec_or64, toBitVec_shl64, toBitVec_byteAt64_map]
  rfl

end CryptoVerification.E2E.InMem.SipHashBin
