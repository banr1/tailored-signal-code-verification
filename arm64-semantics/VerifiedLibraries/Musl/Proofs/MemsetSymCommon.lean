/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.SepLogic.LoopTactics
public meta import ProofLib.SepLogic.LoopTactics

/-!
# Shared Definitions for `musl` `memset.S`

Defines the instruction words `memsetWordsSym` of `musl` v1.2.5 AArch64 `memset.S` (`65`
instructions), the leaf-function preservation predicate `MemsetLeafPreserved`, the SIMD byte
broadcasts `memsetDup16` and `memsetDup8`, and the memory-fill invariant `PrefixFilled` with its
store-stepping lemmas.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Musl

open Arm64 ProofLib

/-- Instruction words of `memset` (65 words, 260 bytes). -/
def memsetWordsSym : List (BitVec 32) := [
  0x4e010c20#32, 0x8b020004#32, 0xf101805f#32, 0x540003a8#32, 0xf100405f#32, 0x54000202#32,
  0x4e083c01#32, 0x361800a2#32, 0xf9000001#32, 0xf81f8081#32, 0xd65f03c0#32, 0xd503201f#32,
  0x36100082#32, 0xb9000001#32, 0xb81fc081#32, 0xd65f03c0#32, 0xb4000082#32, 0x39000001#32,
  0x36080042#32, 0x781fe081#32, 0xd65f03c0#32, 0x3d800000#32, 0x373000c2#32, 0x3c9f0080#32,
  0x36280062#32, 0x3d800400#32, 0x3c9e0080#32, 0xd65f03c0#32, 0x3d800400#32, 0xad010000#32,
  0xad3f0080#32, 0xd65f03c0#32, 0x12001c21#32, 0x927cec03#32, 0x3d800000#32, 0xf102805f#32,
  0x7a402820#32, 0x54000241#32, 0xd53b00e5#32, 0x924010a5#32, 0xf10010bf#32, 0x540001c1#32,
  0x3d800460#32, 0xad010060#32, 0x927ae463#32, 0xcb030082#32, 0xd1020042#32, 0xd503201f#32,
  0x91010063#32, 0xd50b7423#32, 0xf1010042#32, 0x54ffffa8#32, 0xad3e0080#32, 0xad3f0080#32,
  0xd65f03c0#32, 0xcb030082#32, 0xd1004063#32, 0xd1014042#32, 0xad010060#32, 0xad820060#32,
  0xf1010042#32, 0x54ffffa8#32, 0xad3e0080#32, 0xad3f0080#32, 0xd65f03c0#32]

/-! ## Leaf-function frame predicate -/

/-- Calling-convention preservation together with `lr` (`x30`) preservation for leaf functions. -/
def MemsetLeafPreserved (s0 s : State) : Prop :=
  CallingConventionPreserved s0 s ∧ s.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5)

@[simp, arm64_norm]
theorem MemsetLeafPreserved_refl (s : State) : MemsetLeafPreserved s s :=
  ⟨⟨rfl, by simp [CalleeSavedPreserved]⟩, rfl⟩

@[simp, arm64_norm]
theorem MemsetLeafPreserved_advancePC (s0 s : State) :
    MemsetLeafPreserved s0 s.advancePC ↔ MemsetLeafPreserved s0 s := by
  simp [MemsetLeafPreserved, arm64_norm]

@[simp, arm64_norm]
theorem MemsetLeafPreserved_setPC (s0 s : State) (pc : BitVec 64) :
    MemsetLeafPreserved s0 (s.setPC pc) ↔ MemsetLeafPreserved s0 s := by
  simp [MemsetLeafPreserved, arm64_norm]

@[simp, arm64_norm]
theorem MemsetLeafPreserved_setMem (s0 s : State) (m : Memory) :
    MemsetLeafPreserved s0 (s.setMem m) ↔ MemsetLeafPreserved s0 s := by
  simp [MemsetLeafPreserved, arm64_norm]

@[simp, arm64_norm]
theorem MemsetLeafPreserved_setPState (s0 s : State) (ps : PState) :
    MemsetLeafPreserved s0 (s.setPState ps) ↔ MemsetLeafPreserved s0 s := by
  simp [MemsetLeafPreserved, arm64_norm]

@[simp, arm64_norm]
theorem MemsetLeafPreserved_writeReg64_caller (s0 s : State) (r : Reg) (val : BitVec 64)
    (h1 : isCalleeSavedOrSPReg r = false := by decide)
    (h2 : decide (Reg.gpr 30#5 = r) = false := by decide) :
    MemsetLeafPreserved s0 (s.writeReg64 r val) ↔ MemsetLeafPreserved s0 s := by
  have hne : Reg.gpr 30#5 ≠ r := of_decide_eq_false h2
  simp [MemsetLeafPreserved, CallingConventionPreserved_writeReg64_caller s0 s r val h1,
    State.readReg64_writeReg64, hne]

@[simp, arm64_norm]
theorem MemsetLeafPreserved_writeVReg128 (s0 s : State) (idx : BitVec 5) (val : BitVec 128)
    (h : isCalleeSavedVReg idx = false := by decide) :
    MemsetLeafPreserved s0 (s.writeVReg128 idx val) ↔ MemsetLeafPreserved s0 s := by
  simp [MemsetLeafPreserved, CallingConventionPreserved,
    CalleeSavedPreserved_writeVReg128 s0 s idx val h, arm64_norm]

/-! ## Byte broadcast (`dup v0.16b, w1`) -/

/-- 128-bit vector produced by `dup v0.16b, w1` from register value `v`. -/
def memsetDup16 (v : BitVec 64) : BitVec 128 :=
  mapLanes 8 0#128 (fun _ => v.zeroExtend 128 &&& 255#128) 16

/-- Low 64 bits of `memsetDup16 v`. -/
def memsetDup8 (v : BitVec 64) : BitVec 64 :=
  (getSimdLane (memsetDup16 v) 64 0).truncate 64

private theorem memset_laneMask_8_eq : laneMask 8 = 255#128 := rfl
private theorem memset_mask_64_eq : (1#128 <<< 64) - 1#128 = 0xffffffffffffffff#128 := rfl

@[simp high, arm64_norm]
theorem memset_mapSimdLanes_dup16 (v : BitVec 64) :
    mapSimdLanes true 8 0#128 (fun _ => v.zeroExtend 128 &&& 255#128) = memsetDup16 v :=
  mapSimdLanes_true_8 _ _

@[simp high, arm64_norm]
theorem memset_getSimdLane_dup16_64_0 (v : BitVec 64) :
    (getSimdLane (memsetDup16 v) 64 0).truncate 64 = memsetDup8 v := rfl

@[simp high, arm64_norm]
theorem memset_zext64_dup16_low64 (v : BitVec 64) :
    BitVec.zeroExtend 64 (memsetDup16 v >>> 0 &&& 18446744073709551615#128) = memsetDup8 v := rfl

@[simp high, arm64_norm]
theorem memset_zext64_dup16_low64' (v : BitVec 64) :
    BitVec.zeroExtend 64 (memsetDup16 v &&& 18446744073709551615#128) = memsetDup8 v := rfl

@[simp high, arm64_norm]
theorem memset_truncate64_dup16 (v : BitVec 64) :
    (memsetDup16 v).truncate 64 = memsetDup8 v := by
  dsimp only [memsetDup8, getSimdLane]
  simp only [memset_mask_64_eq]
  bv_slice

@[simp high, arm64_norm]
theorem memset_setWidth64_dup16 (v : BitVec 64) :
    BitVec.setWidth 64 (memsetDup16 v) = memsetDup8 v :=
  memset_truncate64_dup16 v

theorem memsetDup16_extract_0_64 (v : BitVec 64) :
    (memsetDup16 v).extractLsb' 0 64 = memsetDup8 v := by
  dsimp only [memsetDup8, getSimdLane]
  simp only [memset_mask_64_eq]
  bv_slice

theorem memsetDup16_extract_64_64 (v : BitVec 64) :
    (memsetDup16 v).extractLsb' 64 64 = memsetDup8 v := by
  dsimp only [memsetDup8, memsetDup16, getSimdLane, mapLanes]
  simp only [memset_laneMask_8_eq, memset_mask_64_eq]
  bv_slice

theorem memsetDup8_extracts (v : BitVec 64) :
    (memsetDup8 v).extractLsb' 0 8 = v.truncate 8 ∧
    (memsetDup8 v).extractLsb' 8 8 = v.truncate 8 ∧
    (memsetDup8 v).extractLsb' 16 8 = v.truncate 8 ∧
    (memsetDup8 v).extractLsb' 24 8 = v.truncate 8 ∧
    (memsetDup8 v).extractLsb' 32 8 = v.truncate 8 ∧
    (memsetDup8 v).extractLsb' 40 8 = v.truncate 8 ∧
    (memsetDup8 v).extractLsb' 48 8 = v.truncate 8 ∧
    (memsetDup8 v).extractLsb' 56 8 = v.truncate 8 := by
  dsimp only [memsetDup8, memsetDup16, getSimdLane, mapLanes]
  simp only [memset_laneMask_8_eq, memset_mask_64_eq]
  bv_slice

theorem memsetDup16_eq_zero_of_truncate8_zero {v : BitVec 64} (h : v.truncate 8 = 0#8) :
    memsetDup16 v = 0#128 := by
  dsimp only [memsetDup16, mapLanes]
  simp only [memset_laneMask_8_eq]
  bv_slice

theorem memsetDup16_expand (c : BitVec 64) :
    (0#128 ||| (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 0 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 8 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 16 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 24 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 32 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 40 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 48 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 56 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 64 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 72 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 80 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 88 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 96 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 104 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 112 |||
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 120) = memsetDup16 c := rfl

attribute [irreducible] memsetDup16 memsetDup8

attribute [simp high, arm64_norm] memsetDup16_extract_0_64 memsetDup16_extract_64_64

theorem memsetDup8_eq_zero_of_truncate8_zero {v : BitVec 64} (h : v.truncate 8 = 0#8) :
    memsetDup8 v = 0#64 := by
  rw [← memsetDup16_extract_0_64, memsetDup16_eq_zero_of_truncate8_zero h]
  rfl

theorem memset_read8_write64_dup8 (m : Memory) (a v : BitVec 64) {d : Nat} (hd : d < 8) :
    (m.write64 a (memsetDup8 v)).read8 (a + BitVec.ofNat 64 d) = v.truncate 8 := by
  have hx := memsetDup8_extracts v
  have hd_cases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by omega
  rcases hd_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> {
    dsimp only [Memory.write64]
    rw [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1,
        hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2]
    simp (config := { decide := true }) only [Memory.read8_write8, Memory.add_eq_add_left,
      ↓reduceIte]
  }

/-! ## Prefix byte-fill invariant (`PrefixFilled`) -/

/-- The first `k` bytes at `dst` in `m` have been filled with `v.truncate 8`, and all bytes
    outside `[dst, dst + len)` in `m` agree with `m₀` (with permissions unchanged). -/
def PrefixFilled (m₀ m : Memory) (dst v : BitVec 64) (k len : Nat) : Prop :=
  AgreesOutside m₀ m dst len ∧
  ∀ i : Nat, i < k → m.read8 (dst + BitVec.ofNat 64 i) = v.truncate 8

theorem PrefixFilled.zero (m₀ : Memory) (dst v : BitVec 64) (len : Nat) :
    PrefixFilled m₀ m₀ dst v 0 len :=
  ⟨AgreesOutside.rfl' m₀ dst len, fun _ hi => by omega⟩

theorem PrefixFilled.mono {m₀ m : Memory} {dst v : BitVec 64} {k k' len : Nat}
    (h : PrefixFilled m₀ m dst v k len) (hle : k' ≤ k) :
    PrefixFilled m₀ m dst v k' len :=
  ⟨h.1, fun i hi => h.2 i (by omega)⟩

theorem PrefixFilled.perm_eq {m₀ m : Memory} {dst v : BitVec 64} {k len : Nat}
    (h : PrefixFilled m₀ m dst v k len) : m.perm = m₀.perm :=
  h.1.2.1

theorem PrefixFilled.rw {m₀ m : Memory} {dst v : BitVec 64} {k len : Nat}
    {b : BitVec 64} {n : Nat} (h : PrefixFilled m₀ m dst v k len) (hrw : m₀.RW b n) :
    m.RW b n :=
  hrw.of_perm_eq h.1.2.1 h.1.2.2.2.1

/-- One 64-bit broadcast store at `dst + off` (with `off ≤ k`, `off + 8 ≤ len`) extends the
    filled prefix to `off + 8`. -/
theorem PrefixFilled.memset_step64 {m₀ m : Memory} {dst v a : BitVec 64} {k off len : Nat}
    (h : PrefixFilled m₀ m dst v k len)
    (hoff_le : off ≤ k) (hoff_len : off + 8 ≤ len) (hlen : len ≤ 2 ^ 64)
    (ha : a = dst + BitVec.ofNat 64 off) :
    PrefixFilled m₀ (m.write64 a (memsetDup8 v)) dst v (off + 8) len := by
  subst ha
  refine ⟨h.1.write64 (by bv_omega) hlen, fun i hi => ?_⟩
  by_cases hioff : i < off
  · rw [Memory.read8_write64_outside (by unfold OutsideRegion; bv_arith)]
    exact h.2 i (by omega)
  · have h_dst_i : dst + BitVec.ofNat 64 i =
        (dst + BitVec.ofNat 64 off) + BitVec.ofNat 64 (i - off) := by bv_arith
    rw [h_dst_i]
    exact memset_read8_write64_dup8 m _ v (by omega)

/-- A pair of 64-bit broadcast stores at `dst + off` and `dst + off + 8` (one `str q0` / half of
    an `stp q0, q0`) extends the filled prefix to `off + 16`. -/
theorem PrefixFilled.memset_step128 {m₀ m : Memory} {dst v a1 a2 : BitVec 64} {k' len : Nat}
    (k off : Nat) (hoff_le : off ≤ k) (hoff_len : off + 16 ≤ len) (hlen : len ≤ 2 ^ 64)
    (hk' : off + 16 = k')
    (ha1 : a1 = dst + BitVec.ofNat 64 off) (ha2 : a2 = a1 + 8#64)
    (h : PrefixFilled m₀ m dst v k len) :
    PrefixFilled m₀ ((m.write64 a1 (memsetDup8 v)).write64 a2 (memsetDup8 v)) dst v k' len := by
  subst hk' ha2
  have h1 := h.memset_step64 hoff_le (by omega) hlen ha1
  exact h1.memset_step64 (off := off + 8) (by omega) (by omega) hlen (by subst ha1; bv_arith)

/-- Four `memset_step128` pairs (two `stp q0, q0` at consecutive 32-byte slots) extend the filled
    prefix to `off + 64`. -/
theorem PrefixFilled.memset_step512 {m₀ m : Memory} {dst v a1 a2 a3 a4 a5 a6 a7 a8 : BitVec 64}
    {k' len : Nat} (k off : Nat)
    (hoff_le : off ≤ k) (hoff_len : off + 64 ≤ len) (hlen : len ≤ 2 ^ 64) (hk' : off + 64 = k')
    (ha1 : a1 = dst + BitVec.ofNat 64 off) (ha2 : a2 = a1 + 8#64)
    (ha3 : a3 = a1 + 16#64) (ha4 : a4 = a3 + 8#64)
    (ha5 : a5 = a3 + 16#64) (ha6 : a6 = a5 + 8#64)
    (ha7 : a7 = a5 + 16#64) (ha8 : a8 = a7 + 8#64)
    (h : PrefixFilled m₀ m dst v k len) :
    PrefixFilled m₀
      ((((((((m.write64 a1 (memsetDup8 v)).write64 a2 (memsetDup8 v)).write64 a3
        (memsetDup8 v)).write64 a4 (memsetDup8 v)).write64 a5 (memsetDup8 v)).write64 a6
        (memsetDup8 v)).write64 a7 (memsetDup8 v)).write64 a8 (memsetDup8 v)) dst v k' len := by
  subst ha3 ha5 ha7
  refine PrefixFilled.memset_step128 (off + 48) (off + 48) (by omega) (by omega) hlen hk'
    (by subst ha1; bv_arith) ha8 ?_
  refine PrefixFilled.memset_step128 (off + 32) (off + 32) (by omega) (by omega) hlen rfl
    (by subst ha1; bv_arith) ha6 ?_
  refine PrefixFilled.memset_step128 (off + 16) (off + 16) (by omega) (by omega) hlen rfl
    (by subst ha1; bv_arith) ha4 ?_
  exact PrefixFilled.memset_step128 k off hoff_le (by omega) hlen rfl ha1 ha2 h

/-- `memset_step512` for stores of zero when the fill byte is zero (`dc zva`). -/
theorem PrefixFilled.memset_step512_zero {m₀ m : Memory}
    {dst v a1 a2 a3 a4 a5 a6 a7 a8 : BitVec 64} {k' len : Nat} (k off : Nat)
    (hv0 : v.truncate 8 = 0#8)
    (hoff_le : off ≤ k) (hoff_len : off + 64 ≤ len) (hlen : len ≤ 2 ^ 64) (hk' : off + 64 = k')
    (ha1 : a1 = dst + BitVec.ofNat 64 off) (ha2 : a2 = a1 + 8#64)
    (ha3 : a3 = a1 + 16#64) (ha4 : a4 = a3 + 8#64)
    (ha5 : a5 = a3 + 16#64) (ha6 : a6 = a5 + 8#64)
    (ha7 : a7 = a5 + 16#64) (ha8 : a8 = a7 + 8#64)
    (h : PrefixFilled m₀ m dst v k len) :
    PrefixFilled m₀
      ((((((((m.write64 a1 0#64).write64 a2 0#64).write64 a3 0#64).write64 a4 0#64).write64
        a5 0#64).write64 a6 0#64).write64 a7 0#64).write64 a8 0#64) dst v k' len := by
  have h := h.memset_step512 k off hoff_le hoff_len hlen hk' ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8
  rwa [memsetDup8_eq_zero_of_truncate8_zero hv0] at h

end VerifiedLibraries.Musl
