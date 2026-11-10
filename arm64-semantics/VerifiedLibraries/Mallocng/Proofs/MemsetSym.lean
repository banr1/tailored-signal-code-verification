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
import VerifiedLibraries.Mallocng.Proofs.MemcpySym

/-!
# Symbolic Execution and Loop Invariants for `musl` `memset`

Spec-independent symbolic execution and byte-fill invariants for `musl` v1.2.5's AArch64
`memset.S` (65 instructions, 260 bytes). Sizes `n ≤ 96` are proved as `SepWP` triples over an
owned slice `dst ↦ₛ bs` (`memset_sepWP_le96`), and the `96 < n` `stp` and `dc zva` 64-byte loops
step with the `PrefixFilled` invariant (`memset_sym_large`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

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

/-- Calling-convention, `lr` (`x30`), and non-GPR system-field preservation for leaf functions. -/
def MemsetLeafPreserved (s0 s : State) : Prop :=
  CallingConventionPreserved s0 s ∧
  s.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) ∧
  s.fs = s0.fs ∧ s.trace = s0.trace ∧ s.tpidrEl0 = s0.tpidrEl0 ∧
  s.brkStart = s0.brkStart ∧ s.oracle = s0.oracle ∧ s.symtab = s0.symtab ∧
  s.sigActions = s0.sigActions ∧ s.brk = s0.brk

@[simp, arm64_norm]
theorem MemsetLeafPreserved_refl (s : State) : MemsetLeafPreserved s s :=
  ⟨⟨rfl, by simp [CalleeSavedPreserved]⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
    State.readReg64_writeReg64, hne, arm64_norm]

@[simp, arm64_norm]
theorem MemsetLeafPreserved_writeVReg128 (s0 s : State) (idx : BitVec 5) (val : BitVec 128)
    (h : isCalleeSavedVReg idx = false := by decide) :
    MemsetLeafPreserved s0 (s.writeVReg128 idx val) ↔ MemsetLeafPreserved s0 s := by
  simp [MemsetLeafPreserved, CallingConventionPreserved,
    CalleeSavedPreserved_writeVReg128 s0 s idx val h, arm64_norm]

/-- 128-bit vector produced by `dup v0.16b, w1` from register value `v : BitVec 64`. -/
def dup16 (v : BitVec 64) : BitVec 128 :=
  mapLanes 8 0#128 (fun _ => v.zeroExtend 128 &&& 255#128) 16

/-- 64-bit register value produced by `mov x1, v0.d[0]` after `dup v0.16b, w1`. -/
def dup8 (v : BitVec 64) : BitVec 64 :=
  (getSimdLane (dup16 v) 64 0).truncate 64

@[simp high, arm64_norm]
theorem mapSimdLanes_dup16 (v : BitVec 64) :
    mapSimdLanes true 8 0#128 (fun _ => v.zeroExtend 128 &&& 255#128) = dup16 v :=
  mapSimdLanes_true_8 _ _

@[simp high, arm64_norm]
theorem getSimdLane_dup16_64_0 (v : BitVec 64) :
    (getSimdLane (dup16 v) 64 0).truncate 64 = dup8 v := rfl

@[simp high, arm64_norm]
theorem zext64_dup16_low64 (v : BitVec 64) :
    BitVec.zeroExtend 64 (dup16 v >>> 0 &&& 0xffffffffffffffff#128) = dup8 v := rfl

@[simp high, arm64_norm]
theorem zext64_dup16_low64' (v : BitVec 64) :
    BitVec.zeroExtend 64 (dup16 v &&& 0xffffffffffffffff#128) = dup8 v := rfl

private theorem laneMask_8_eq : laneMask 8 = 255#128 := rfl
private theorem mask_64_eq : (1#128 <<< 64) - 1#128 = 0xffffffffffffffff#128 := rfl

theorem dup16_extract_0_64 (v : BitVec 64) :
    (dup16 v).extractLsb' 0 64 = dup8 v := by
  dsimp only [dup8, getSimdLane]
  simp only [mask_64_eq]
  bv_slice

@[simp high, arm64_norm]
theorem truncate64_dup16 (v : BitVec 64) :
    (dup16 v).truncate 64 = dup8 v := by
  dsimp only [dup8, getSimdLane]
  simp only [mask_64_eq]
  bv_slice

@[simp high, arm64_norm]
theorem setWidth64_dup16 (v : BitVec 64) :
    BitVec.setWidth 64 (dup16 v) = dup8 v :=
  truncate64_dup16 v

theorem dup16_extract_64_64 (v : BitVec 64) :
    (dup16 v).extractLsb' 64 64 = dup8 v := by
  dsimp only [dup8, dup16, getSimdLane, mapLanes]
  simp only [laneMask_8_eq, mask_64_eq]
  bv_slice

theorem dup8_extracts (v : BitVec 64) :
    (dup8 v).extractLsb' 0 8 = v.truncate 8 ∧
    (dup8 v).extractLsb' 8 8 = v.truncate 8 ∧
    (dup8 v).extractLsb' 16 8 = v.truncate 8 ∧
    (dup8 v).extractLsb' 24 8 = v.truncate 8 ∧
    (dup8 v).extractLsb' 32 8 = v.truncate 8 ∧
    (dup8 v).extractLsb' 40 8 = v.truncate 8 ∧
    (dup8 v).extractLsb' 48 8 = v.truncate 8 ∧
    (dup8 v).extractLsb' 56 8 = v.truncate 8 := by
  dsimp only [dup8, dup16, getSimdLane, mapLanes]
  simp only [laneMask_8_eq, mask_64_eq]
  bv_slice

theorem read8_write64_dup8 (m : Memory) (a : BitVec 64) (v : BitVec 64) {d : Nat} (hd : d < 8) :
    (m.write64 a (dup8 v)).read8 (a + BitVec.ofNat 64 d) = v.truncate 8 := by
  have hx := dup8_extracts v
  have hd_cases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by omega
  rcases hd_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> {
    dsimp only [Memory.write64]
    rw [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1,
        hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2]
    simp (config := { decide := true }) only [Memory.read8_write8, Memory.add_eq_add_left, ↓reduceIte]
  }

theorem memset_read8_write64_outside {m : Memory} {addr a : BitVec 64} {v : BitVec 64}
    (h : OutsideRegion addr 8 a) : (m.write64 addr v).read8 a = m.read8 a := by
  unfold OutsideRegion at h
  dsimp only [Memory.write64]
  rw [Memory.read8_write8_ne (by bv_arith),
      Memory.read8_write8_ne (by bv_arith),
      Memory.read8_write8_ne (by bv_arith),
      Memory.read8_write8_ne (by bv_arith),
      Memory.read8_write8_ne (by bv_arith),
      Memory.read8_write8_ne (by bv_arith),
      Memory.read8_write8_ne (by bv_arith),
      Memory.read8_write8_ne (by bv_arith)]

theorem read8_write128_dup16 (m : Memory) (a : BitVec 64) (v : BitVec 64) {d : Nat} (hd : d < 16) :
    (m.write128 a (dup16 v)).read8 (a + BitVec.ofNat 64 d) = v.truncate 8 := by
  dsimp only [Memory.write128]
  rw [dup16_extract_0_64, dup16_extract_64_64]
  by_cases hd8 : d < 8
  · rw [memset_read8_write64_outside (by unfold OutsideRegion; bv_arith)]
    exact read8_write64_dup8 m a v hd8
  · have h_addr : a + BitVec.ofNat 64 d = (a + 8#64) + BitVec.ofNat 64 (d - 8) := by bv_arith
    rw [h_addr]
    exact read8_write64_dup8 (m.write64 a (dup8 v)) (a + 8#64) v (by omega)

theorem dup16_eq_zero_of_truncate8_zero {v : BitVec 64} (h : v.truncate 8 = 0#8) :
    dup16 v = 0#128 := by
  dsimp only [dup16, mapLanes]
  simp only [laneMask_8_eq]
  bv_slice

theorem dup16_expand (c : BitVec 64) :
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
      (BitVec.zeroExtend 128 c &&& 255#128 &&& 255#128) <<< 120) = dup16 c := rfl

attribute [irreducible] dup16 dup8

theorem memset_read8_write128_outside {m : Memory} {addr a : BitVec 64} {v : BitVec 128}
    (h : OutsideRegion addr 16 a) : (m.write128 addr v).read8 a = m.read8 a := by
  unfold OutsideRegion at h
  dsimp only [Memory.write128]
  rw [memset_read8_write64_outside (by unfold OutsideRegion; bv_arith),
      memset_read8_write64_outside (by unfold OutsideRegion; bv_arith)]

/-! ## Prefix Byte-Fill Invariant (`PrefixFilled`) -/

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

theorem PrefixFilled.step128 {m₀ m : Memory} {dst v a_dst : BitVec 64} {val : BitVec 128}
    {k off len : Nat}
    (h : PrefixFilled m₀ m dst v k len)
    (hoff_le : off ≤ k) (hoff_len : off + 16 ≤ len) (hlen : len ≤ 2 ^ 64)
    (hdst : a_dst = dst + BitVec.ofNat 64 off)
    (hval : val = dup16 v) :
    PrefixFilled m₀ (m.write128 a_dst val) dst v (off + 16) len := by
  subst hdst hval
  refine ⟨h.1.write128 (by bv_omega) hlen, ?_⟩
  · intro i hi
    by_cases hioff : i < off
    · rw [memset_read8_write128_outside (by unfold OutsideRegion; bv_arith)]
      exact h.2 i (by omega)
    · have hd : i - off < 16 := by omega
      have h_dst_i : dst + BitVec.ofNat 64 i =
          (dst + BitVec.ofNat 64 off) + BitVec.ofNat 64 (i - off) := by bv_arith
      rw [h_dst_i]
      exact read8_write128_dup16 m (dst + BitVec.ofNat 64 off) v hd

/-! ## Large sizes (`96 < n`): manual stepping -/

attribute [simp high, arm64_norm] dup16_extract_0_64 dup16_extract_64_64

theorem dup8_eq_zero_of_truncate8_zero {v : BitVec 64} (h : v.truncate 8 = 0#8) :
    dup8 v = 0#64 := by
  rw [← dup16_extract_0_64, dup16_eq_zero_of_truncate8_zero h]
  rfl

theorem write64_pair_dup8_eq_write128 (m : Memory) (a a' v : BitVec 64) (ha' : a' = a + 8#64) :
    (m.write64 a (dup8 v)).write64 a' (dup8 v) = m.write128 a (dup16 v) := by
  subst ha'
  dsimp only [Memory.write128]
  rw [dup16_extract_0_64, dup16_extract_64_64]

theorem PrefixFilled.step128_pair {m₀ m : Memory} {dst v a1 a2 : BitVec 64} {val1 val2 : BitVec 64}
    {k' len : Nat} (k off : Nat)
    (hoff_le : off ≤ k) (hoff_len : off + 16 ≤ len) (hlen : len ≤ 2 ^ 64) (hk' : off + 16 = k')
    (ha1 : a1 = dst + BitVec.ofNat 64 off)
    (ha2 : a2 = a1 + 8#64)
    (hval1 : val1 = dup8 v) (hval2 : val2 = dup8 v)
    (h : PrefixFilled m₀ m dst v k len) :
    PrefixFilled m₀ ((m.write64 a1 val1).write64 a2 val2) dst v k' len := by
  subst hk' ha1 ha2 hval1 hval2
  rw [write64_pair_dup8_eq_write128 _ _ _ _ rfl]
  exact h.step128 hoff_le hoff_len hlen rfl rfl

theorem PrefixFilled.step512_pair {m₀ m : Memory} {dst v a1 a2 a3 a4 a5 a6 a7 a8 : BitVec 64}
    {val1 val2 val3 val4 val5 val6 val7 val8 : BitVec 64}
    {k' len : Nat} (k off : Nat)
    (hoff_le : off ≤ k) (hoff_len : off + 64 ≤ len) (hlen : len ≤ 2 ^ 64) (hk' : off + 64 = k')
    (ha1 : a1 = dst + BitVec.ofNat 64 off) (ha2 : a2 = a1 + 8#64)
    (ha3 : a3 = a1 + 16#64) (ha4 : a4 = a3 + 8#64)
    (ha5 : a5 = a3 + 16#64) (ha6 : a6 = a5 + 8#64)
    (ha7 : a7 = a5 + 16#64) (ha8 : a8 = a7 + 8#64)
    (hv1 : val1 = dup8 v) (hv2 : val2 = dup8 v) (hv3 : val3 = dup8 v) (hv4 : val4 = dup8 v)
    (hv5 : val5 = dup8 v) (hv6 : val6 = dup8 v) (hv7 : val7 = dup8 v) (hv8 : val8 = dup8 v)
    (h : PrefixFilled m₀ m dst v k len) :
    PrefixFilled m₀
      ((((((((m.write64 a1 val1).write64 a2 val2).write64 a3 val3).write64 a4 val4).write64
        a5 val5).write64 a6 val6).write64 a7 val7).write64 a8 val8) dst v k' len := by
  subst ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8
  refine PrefixFilled.step128_pair (off + 48) (off + 48) (by omega) (by omega) hlen hk' (by bv_arith) rfl hv7 hv8 ?_
  refine PrefixFilled.step128_pair (off + 32) (off + 32) (by omega) (by omega) hlen rfl (by bv_arith) rfl hv5 hv6 ?_
  refine PrefixFilled.step128_pair (off + 16) (off + 16) (by omega) (by omega) hlen rfl (by bv_arith) rfl hv3 hv4 ?_
  exact PrefixFilled.step128_pair k off hoff_le (by omega) hlen rfl rfl rfl hv1 hv2 h

theorem PrefixFilled.step512_pair_zero {m₀ m : Memory} {dst v a1 a2 a3 a4 a5 a6 a7 a8 : BitVec 64}
    {k' len : Nat} (k off : Nat)
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
  have hd := (dup8_eq_zero_of_truncate8_zero hv0).symm
  exact h.step512_pair k off hoff_le hoff_len hlen hk' ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8
    hd hd hd hd hd hd hd hd

theorem memset_stp_loop_0x0e8 (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memsetWordsSym)
    (m₀ : Memory) (dst c n : BitVec 64)
    (hrw : m₀.RW dst n.toNat)
    (hlen : n.toNat ≤ 2 ^ 64)
    (s0 : State) (Post : State → Prop)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.readReg64 .x0 = dst → MemsetLeafPreserved s0 sf →
      PrefixFilled m₀ sf.mem dst c n.toNat n.toNat →
      Post sf) :
    ∀ (fuel k : Nat) (rem : BitVec 64) (s : State),
      (rem.toNat - 1) / 64 ≤ fuel →
      1 ≤ rem.toNat →
      k + rem.toNat + 64 = n.toNat →
      s.pc = a + 0xe8#64 →
      s.status = .Running →
      s.readReg64 .x0 = dst →
      s.readReg64 .x2 = rem →
      s.readReg64 .x3 = dst + BitVec.ofNat 64 k - 32#64 →
      s.readReg64 .x4 = dst + n →
      s.readVReg128 0#5 = dup16 c →
      MemsetLeafPreserved s0 s →
      PrefixFilled m₀ s.mem dst c k n.toNat →
      reaches_pc prog (s0.readReg64 .lr) s Post := by
  intro fuel
  induction fuel with
  | zero =>
    intro k rem s hfuel hrem_pos hk_eq hpc hrun hx0 hx2 hx3 hx4 hv0 hcc hfc
    have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
    have hrem_le : rem.toNat ≤ 64 := by omega
    have hbhi : (64#64).ult rem = false := by bv_arith
    arm64_step_inst -- +0x0e8: stp q0, q0, [x3, #0x20]
    arm64_step_inst -- +0x0ec: stp q0, q0, [x3, #0x40]!
    arm64_step_inst -- +0x0f0: subs x2, x2, #0x40
    arm64_step_inst -- +0x0f4: b.hi +0x0e8 (not taken)
    arm64_step_inst -- +0x0f8: stp q0, q0, [x4, #-0x40]
    arm64_step_inst -- +0x0fc: stp q0, q0, [x4, #-0x20]
    arm64_step_inst -- +0x100: ret
    refine reaches_pc_refl (by simpa [arm64_norm] using hcc.2.1) (by simp [arm64_norm, hrun]) ?_
    apply hpost _ (by simpa [arm64_norm] using hcc.2.1) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hx0]) (by simp (config := { decide := true }) only [arm64_norm]; exact hcc)
    dsimp only [State.setMem]
    refine PrefixFilled.step512_pair (k + 64) (n.toNat - 64) (by omega) (by omega) hlen (by omega)
      (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith)
      (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith)
      rfl rfl rfl rfl rfl rfl rfl rfl ?_
    exact PrefixFilled.step512_pair k k (by omega) (by omega) hlen rfl
      (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith)
      (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith)
      rfl rfl rfl rfl rfl rfl rfl rfl hfc
  | succ fuel ih =>
    intro k rem s hfuel hrem_pos hk_eq hpc hrun hx0 hx2 hx3 hx4 hv0 hcc hfc
    by_cases hrem_le : rem.toNat ≤ 64
    · exact ih k rem s (by omega) hrem_pos hk_eq hpc hrun hx0 hx2 hx3 hx4 hv0 hcc hfc
    · have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
      have hrem_gt : 64 < rem.toNat := by omega
      have hbhi : (64#64).ult rem = true := by bv_arith
      have hrem_sub : (rem - 64#64).toNat = rem.toNat - 64 := by bv_omega
      arm64_step_inst -- +0x0e8: stp q0, q0, [x3, #0x20]
      arm64_step_inst -- +0x0ec: stp q0, q0, [x3, #0x40]!
      arm64_step_inst -- +0x0f0: subs x2, x2, #0x40
      arm64_step_inst -- +0x0f4: b.hi +0x0e8 (taken)
      refine ih (k + 64) (rem - 64#64) _ (by omega) (by omega) (by omega)
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm]) ?_
        (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
        (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) ?_
      · simp only [arm64_norm]; bv_arith
      · dsimp only [State.setMem]
        exact PrefixFilled.step512_pair k k (by omega) (by omega) hlen rfl
          (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith)
          (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith)
          rfl rfl rfl rfl rfl rfl rfl rfl hfc

theorem simdStoreRegs_dcZva (ea : BitVec 64) (m : Memory) :
    simdStoreRegs SimdMemSize.Q128 (fun _ => 0#128) 4 0#5 ea m =
      (((((((m.write64 ea 0#64).write64 (ea + 8#64) 0#64).write64
        (ea + 16#64) 0#64).write64 (ea + 16#64 + 8#64) 0#64).write64
        (ea + 16#64 + 16#64) 0#64).write64 (ea + 16#64 + 16#64 + 8#64) 0#64).write64
        (ea + 16#64 + 16#64 + 16#64) 0#64).write64 (ea + 16#64 + 16#64 + 16#64 + 8#64) 0#64 :=
  rfl

theorem perm_simdStoreRegs_dcZva (ea : BitVec 64) (m : Memory) :
    (simdStoreRegs SimdMemSize.Q128 (fun _ => 0#128) 4 0#5 ea m).perm = m.perm := by
  rw [simdStoreRegs_dcZva]
  simp only [Memory.perm_write64]

theorem Memory.RW.simdStoreRegs_dcZva {m : Memory} {dst : BitVec 64} {n : Nat}
    (ea : BitVec 64) (h : m.RW dst n) :
    (simdStoreRegs SimdMemSize.Q128 (fun _ => 0#128) 4 0#5 ea m).RW dst n :=
  h.of_perm_eq (perm_simdStoreRegs_dcZva ea m) fun _ ha => by
    rw [VerifiedLibraries.Mallocng.Proofs.simdStoreRegs_dcZva]
    exact Memory.isLazyFree_write64_of_false _ _ (Memory.isLazyFree_write64_of_false _ _
      (Memory.isLazyFree_write64_of_false _ _ (Memory.isLazyFree_write64_of_false _ _
        (Memory.isLazyFree_write64_of_false _ _ (Memory.isLazyFree_write64_of_false _ _
          (Memory.isLazyFree_write64_of_false _ _ (Memory.isLazyFree_write64_of_false _ _ ha)))))))

theorem PrefixFilled.step_dcZva {m₀ m : Memory} {dst v ea : BitVec 64}
    {k' len : Nat} (k off : Nat)
    (hv0 : v.truncate 8 = 0#8)
    (hoff_le : off ≤ k) (hoff_len : off + 64 ≤ len) (hlen : len ≤ 2 ^ 64) (hk' : off + 64 = k')
    (hea : ea = dst + BitVec.ofNat 64 off)
    (h : PrefixFilled m₀ m dst v k len) :
    PrefixFilled m₀ (simdStoreRegs SimdMemSize.Q128 (fun _ => 0#128) 4 0#5 ea m) dst v k' len := by
  rw [simdStoreRegs_dcZva]
  exact h.step512_pair_zero k off hv0 hoff_le hoff_len hlen hk' hea rfl rfl rfl rfl rfl rfl rfl

def Aligned64 (x : BitVec 64) : Prop :=
  x &&& 0xffffffffffffffc0#64 = x

theorem Aligned64.add_64 {x : BitVec 64} (h : Aligned64 x) :
    Aligned64 (x + 64#64) := by
  unfold Aligned64 at *
  bv_bits

theorem memset_zva_tail_0x0d0 (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memsetWordsSym)
    (m₀ : Memory) (dst c n : BitVec 64)
    (hrw : m₀.RW dst n.toNat)
    (hlen : n.toNat ≤ 2 ^ 64)
    (s0 s : State) (Post : State → Prop)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.readReg64 .x0 = dst → MemsetLeafPreserved s0 sf →
      PrefixFilled m₀ sf.mem dst c n.toNat n.toNat →
      Post sf)
    (k : Nat)
    (hn64 : 64 ≤ n.toNat)
    (hk_cover : n.toNat ≤ k + 64)
    (hk_le : k ≤ n.toNat)
    (hpc : s.pc = a + 0xd0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx4 : s.readReg64 .x4 = dst + n)
    (hv0 : s.readVReg128 0#5 = dup16 c)
    (hcc : MemsetLeafPreserved s0 s)
    (hfc : PrefixFilled m₀ s.mem dst c k n.toNat) :
    reaches_pc prog (s0.readReg64 .lr) s Post := by
  have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
  arm64_step_inst -- +0x0d0: stp q0, q0, [x4, #-0x40]
  arm64_step_inst -- +0x0d4: stp q0, q0, [x4, #-0x20]
  arm64_step_inst -- +0x0d8: ret
  refine reaches_pc_refl (by simpa [arm64_norm] using hcc.2.1) (by simp [arm64_norm, hrun]) ?_
  apply hpost _ (by simpa [arm64_norm] using hcc.2.1) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hx0]) (by simp (config := { decide := true }) only [arm64_norm]; exact hcc)
  dsimp only [State.setMem]
  exact PrefixFilled.step512_pair k (n.toNat - 64) (by omega) (by omega) hlen (by omega)
    (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith)
    (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith)
    rfl rfl rfl rfl rfl rfl rfl rfl hfc

theorem memset_zva_loop_0x0c0 (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memsetWordsSym)
    (m₀ : Memory) (dst c n : BitVec 64)
    (hrw : m₀.RW dst n.toNat)
    (hlen : n.toNat ≤ 2 ^ 64)
    (hc0 : c.truncate 8 = 0#8)
    (s0 : State) (Post : State → Prop)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.readReg64 .x0 = dst → MemsetLeafPreserved s0 sf →
      PrefixFilled m₀ sf.mem dst c n.toNat n.toNat →
      Post sf) :
    ∀ (fuel k : Nat) (rem : BitVec 64) (s : State),
      (rem.toNat - 1) / 64 ≤ fuel →
      1 ≤ rem.toNat →
      k + rem.toNat + 64 = n.toNat →
      Aligned64 (dst + BitVec.ofNat 64 k) →
      s.pc = a + 0xc0#64 →
      s.status = .Running →
      s.readReg64 .x0 = dst →
      s.readReg64 .x2 = rem →
      s.readReg64 .x3 = dst + BitVec.ofNat 64 k - 64#64 →
      s.readReg64 .x4 = dst + n →
      s.readVReg128 0#5 = dup16 c →
      MemsetLeafPreserved s0 s →
      PrefixFilled m₀ s.mem dst c k n.toNat →
      reaches_pc prog (s0.readReg64 .lr) s Post := by
  intro fuel
  induction fuel with
  | zero =>
    intro k rem s hfuel hrem_pos hk_eq halign hpc hrun hx0 hx2 hx3 hx4 hv0 hcc hfc
    have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
    have hrem_le : rem.toNat ≤ 64 := by omega
    have hbhi : (64#64).ult rem = false := by bv_arith
    arm64_step_inst -- +0x0c0: add x3, x3, #0x40
    have halign' : (dst + BitVec.ofNat 64 k) &&& 0xffffffffffffffc0#64 =
        dst + BitVec.ofNat 64 k := halign
    have hcw : s.mem.canWrite ((dst + BitVec.ofNat 64 k) &&& 0xffffffffffffffc0#64) 64 = true := by
      rw [halign']
      exact hrw_s.canWrite_sub (by bv_arith) hlen
    arm64_step_inst -- +0x0c4: dc zva, x3
    clear hcw halign'
    arm64_step_inst -- +0x0c8: subs x2, x2, #0x40
    arm64_step_inst -- +0x0cc: b.hi +0x0c0 (not taken)
    refine memset_zva_tail_0x0d0 prog a hc m₀ dst c n hrw hlen s0 _ Post hpost
      (k + 64) (by omega) (by omega) (by omega)
      (by simp only [arm64_norm]; bv_arith) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx4])
      (by simp [arm64_norm, hv0])
      (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) ?_
    dsimp only [State.setMem]
    exact PrefixFilled.step_dcZva k k hc0 (by omega) (by omega) hlen rfl rfl hfc
  | succ fuel ih =>
    intro k rem s hfuel hrem_pos hk_eq halign hpc hrun hx0 hx2 hx3 hx4 hv0 hcc hfc
    by_cases hrem_le : rem.toNat ≤ 64
    · exact ih k rem s (by omega) hrem_pos hk_eq halign hpc hrun hx0 hx2 hx3 hx4 hv0 hcc hfc
    · have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
      have hrem_gt : 64 < rem.toNat := by omega
      have hbhi : (64#64).ult rem = true := by bv_arith
      arm64_step_inst -- +0x0c0: add x3, x3, #0x40
      have halign' : (dst + BitVec.ofNat 64 k) &&& 0xffffffffffffffc0#64 =
          dst + BitVec.ofNat 64 k := halign
      have hcw : s.mem.canWrite ((dst + BitVec.ofNat 64 k) &&& 0xffffffffffffffc0#64) 64 = true := by
        rw [halign']
        exact hrw_s.canWrite_sub (by bv_arith) hlen
      arm64_step_inst -- +0x0c4: dc zva, x3
      clear hcw halign'
      arm64_step_inst -- +0x0c8: subs x2, x2, #0x40
      arm64_step_inst -- +0x0cc: b.hi +0x0c0 (taken)
      have hrem_sub : (rem - 64#64).toNat = rem.toNat - 64 := by bv_omega
      have halign_next : Aligned64 (dst + BitVec.ofNat 64 (k + 64)) := by
        rw [show dst + BitVec.ofNat 64 (k + 64) = (dst + BitVec.ofNat 64 k) + 64#64 by bv_arith]
        exact halign.add_64
      refine ih (k + 64) (rem - 64#64) _ (by omega) (by omega) (by omega) halign_next
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm]) ?_
        (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
        (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) ?_
      · simp only [arm64_norm]; bv_arith
      · dsimp only [State.setMem]
        exact PrefixFilled.step_dcZva k k hc0 (by omega) (by omega) hlen rfl rfl hfc

theorem and_15_lt (dst : BitVec 64) : (dst &&& 15#64).toNat < 16 := by
  have h : (dst &&& 15#64).ult 16#64 = true := by bv_bits
  simpa [BitVec.ult] using h

theorem and_63_lt (dst : BitVec 64) : (dst &&& 63#64).toNat < 64 := by
  have h : (dst &&& 63#64).ult 64#64 = true := by bv_bits
  simpa [BitVec.ult] using h

theorem and_15_le_and_63 (dst : BitVec 64) :
    (dst &&& 15#64).toNat ≤ (dst &&& 63#64).toNat := by
  have h : (dst &&& 15#64).ule (dst &&& 63#64) = true := by bv_bits
  simpa [BitVec.ule] using h

theorem and_mask16_eq_sub (dst : BitVec 64) :
    dst &&& -16#64 = dst - BitVec.ofNat 64 (dst &&& 15#64).toNat := by
  have h1 : dst &&& -16#64 = dst - (dst &&& 15#64) := by bv_bits
  have h2 : BitVec.ofNat 64 (dst &&& 15#64).toNat = dst &&& 15#64 := by bv_arith
  rw [h1, h2]

theorem and_mask64_of_sub_and15 (dst : BitVec 64) :
    (dst - (dst &&& 15#64)) &&& -64#64 =
      dst - BitVec.ofNat 64 (dst &&& 63#64).toNat := by
  have h1 : (dst - (dst &&& 15#64)) &&& -64#64 = dst - (dst &&& 63#64) := by bv_bits
  have h3 : BitVec.ofNat 64 (dst &&& 63#64).toNat = dst &&& 63#64 := by bv_arith
  rw [h1, h3]

theorem Aligned64.dst_add_sub_and63 (dst : BitVec 64) :
    Aligned64 (dst + BitVec.ofNat 64 (64 - (dst &&& 63#64).toNat)) := by
  have hlt : (dst &&& 63#64).toNat < 64 := and_63_lt dst
  have heq : BitVec.ofNat 64 (64 - (dst &&& 63#64).toNat) = 64#64 - (dst &&& 63#64) := by
    bv_arith
  unfold Aligned64
  rw [heq]
  bv_bits

theorem memset_stp_setup_0x0dc (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memsetWordsSym)
    (m₀ : Memory) (dst c n : BitVec 64)
    (hrw : m₀.RW dst n.toNat)
    (hn_gt : 96 < n.toNat) (hn_le : n.toNat + 260 ≤ 2 ^ 64)
    (d0 : Nat) (hd0_lt : d0 < 16)
    (s0 s : State) (Post : State → Prop)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.readReg64 .x0 = dst → MemsetLeafPreserved s0 sf →
      PrefixFilled m₀ sf.mem dst c n.toNat n.toNat →
      Post sf)
    (hpc : s.pc = a + 0xdc#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst) (hx3 : s.readReg64 .x3 = dst - BitVec.ofNat 64 d0)
    (hx4 : s.readReg64 .x4 = dst + n) (hv0 : s.readVReg128 0#5 = dup16 c)
    (hcc : MemsetLeafPreserved s0 s) (hfc : PrefixFilled m₀ s.mem dst c (16 - d0) n.toNat) :
    reaches_pc prog (s0.readReg64 .lr) s Post := by
  have hlen : n.toNat ≤ 2 ^ 64 := by omega
  arm64_step_inst -- +0x0dc: sub x2, x4, x3
  arm64_step_inst -- +0x0e0: sub x3, x3, #0x10
  arm64_step_inst -- +0x0e4: sub x2, x2, #0x50
  let rem := (dst + n) - (dst - BitVec.ofNat 64 d0) - 80#64
  have hrem_eq : rem.toNat = n.toNat + d0 - 80 := by dsimp only [rem]; bv_omega
  refine memset_stp_loop_0x0e8 prog a hc m₀ dst c n hrw hlen s0 Post hpost
    ((rem.toNat - 1) / 64) (16 - d0) rem _
    (Nat.le_refl _) (by omega) (by omega)
    (by simp only [arm64_norm]; bv_arith) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hx0]) (by simp [arm64_norm, rem]) ?_
    (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
    (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) hfc
  simp only [arm64_norm]; bv_arith

theorem memset_zva_setup_0x098 (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memsetWordsSym)
    (m₀ : Memory) (dst c n : BitVec 64)
    (hrw : m₀.RW dst n.toNat)
    (hn_ge : 160 ≤ n.toNat) (hn_le : n.toNat + 260 ≤ 2 ^ 64) (hc0 : c.truncate 8 = 0#8)
    (s0 s : State) (Post : State → Prop)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.readReg64 .x0 = dst → MemsetLeafPreserved s0 sf →
      PrefixFilled m₀ sf.mem dst c n.toNat n.toNat →
      Post sf)
    (hpc : s.pc = a + 0x98#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx3 : s.readReg64 .x3 = dst - BitVec.ofNat 64 (dst &&& 15#64).toNat)
    (hx4 : s.readReg64 .x4 = dst + n) (hv0 : s.readVReg128 0#5 = dup16 c)
    (hcc : MemsetLeafPreserved s0 s)
    (hfc : PrefixFilled m₀ s.mem dst c (16 - (dst &&& 15#64).toNat) n.toNat) :
    reaches_pc prog (s0.readReg64 .lr) s Post := by
  have hlen : n.toNat ≤ 2 ^ 64 := by omega
  have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
  have hd0_lt : (dst &&& 15#64).toNat < 16 := and_15_lt dst
  have hd64_lt : (dst &&& 63#64).toNat < 64 := and_63_lt dst
  have hd0_le_d64 : (dst &&& 15#64).toNat ≤ (dst &&& 63#64).toNat := and_15_le_and_63 dst
  arm64_step_inst -- +0x098: mrs x5, DCZID_EL0
  arm64_step_inst -- +0x09c: and x5, x5, #0x1f
  arm64_step_inst -- +0x0a0: cmp x5, #0x4
  arm64_step_inst -- +0x0a4: b.ne +0x0dc (not taken)
  arm64_step_inst -- +0x0a8: str q0, [x3, #0x10]
  arm64_step_inst -- +0x0ac: stp q0, q0, [x3, #0x20]
  arm64_step_inst -- +0x0b0: and x3, x3, #0xffffffffffffffc0
  arm64_step_inst -- +0x0b4: sub x2, x4, x3
  arm64_step_inst -- +0x0b8: sub x2, x2, #0x80
  arm64_step_inst -- +0x0bc: nop
  have hx3_64 := and_mask64_of_sub_and15 dst
  let d0 := (dst &&& 15#64).toNat
  let d64 := (dst &&& 63#64).toNat
  let rem := (dst + n) - ((dst - (dst &&& 15#64)) &&& -64#64) - 128#64
  have hrem_eq : rem.toNat = n.toNat + d64 - 128 := by
    dsimp only [rem, d64]; rw [hx3_64]; bv_omega
  refine memset_zva_loop_0x0c0 prog a hc m₀ dst c n hrw hlen hc0 s0 Post hpost
    ((rem.toNat - 1) / 64) (64 - d64) rem _
    (Nat.le_refl _) (by omega) (by omega) (Aligned64.dst_add_sub_and63 dst)
    (by simp only [arm64_norm]; bv_arith) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hx0]) (by simp [arm64_norm, rem]) ?_
    (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
    (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) ?_
  · simp only [arm64_norm]; dsimp only [d64]; rw [hx3_64]; bv_arith
  · dsimp only [State.setMem]
    refine PrefixFilled.mono (k := 64 - d0) ?_ (by omega)
    have h64 : 64 - d0 = 16 - d0 + 16 + 16 + 16 := by omega
    rw [h64]
    refine PrefixFilled.step128_pair (16 - d0 + 16 + 16) (48 - d0)
      (by omega) (by omega) hlen (by omega) (by bv_arith) (by bv_arith) rfl rfl ?_
    refine PrefixFilled.step128_pair (16 - d0 + 16) (32 - d0)
      (by omega) (by omega) hlen (by omega) (by bv_arith) (by bv_arith) rfl rfl ?_
    exact PrefixFilled.step128_pair (16 - d0) (16 - d0)
      (by omega) (by omega) hlen (by omega) (by bv_arith) (by bv_arith) rfl rfl hfc

theorem trunc32_zext64_and255_eq_zero {c : BitVec 64} (h : c.truncate 8 = 0#8) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 c) &&& 255#64) = 0#32 := by
  bv_bits

theorem trunc32_zext64_and255_bne_zero {c : BitVec 64} (h : c.truncate 8 ≠ 0#8) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 c) &&& 255#64) != 0#32) = true := by
  cases hbne : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 c) &&& 255#64) != 0#32)
  · exfalso; apply h
    have heq : BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 c) &&& 255#64) = 0#32 := by
      simpa [bne] using hbne
    bv_bits
  · rfl

theorem memset_large_0x080 (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memsetWordsSym)
    (m₀ : Memory) (dst c n : BitVec 64)
    (hrw : m₀.RW dst n.toNat) (hn_gt : 96 < n.toNat) (hn_le : n.toNat + 260 ≤ 2 ^ 64)
    (s0 s : State) (Post : State → Prop)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.readReg64 .x0 = dst → MemsetLeafPreserved s0 sf →
      PrefixFilled m₀ sf.mem dst c n.toNat n.toNat →
      Post sf)
    (hpc : s.pc = a + 0x80#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = c)
    (hx2 : s.readReg64 .x2 = n) (hx4 : s.readReg64 .x4 = dst + n)
    (hv0 : s.readVReg128 0#5 = dup16 c)
    (hcc : MemsetLeafPreserved s0 s) (hfc : PrefixFilled m₀ s.mem dst c 0 n.toNat) :
    reaches_pc prog (s0.readReg64 .lr) s Post := by
  have hlen : n.toNat ≤ 2 ^ 64 := by omega
  have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
  have hd0_lt : (dst &&& 15#64).toNat < 16 := and_15_lt dst
  have hand16 := and_mask16_eq_sub dst
  arm64_step_inst -- +0x080: and w1, w1, #0xff
  arm64_step_inst -- +0x084: and x3, x0, #0xfffffffffffffff0
  arm64_step_inst -- +0x088: str q0, [x0]
  arm64_step_inst -- +0x08c: cmp x2, #0xa0
  by_cases hn160 : 160 ≤ n.toNat
  · have hule160 : (160#64).ule n = true := by bv_arith
    by_cases hc0 : c.truncate 8 = 0#8
    · have hc0_32 := trunc32_zext64_and255_eq_zero hc0
      arm64_step_inst -- +0x090: ccmp w1, #0x0, #0x0, hs
      arm64_step_inst -- +0x094: b.ne +0x0dc (not taken)
      refine memset_zva_setup_0x098 prog a hc m₀ dst c n hrw hn160 hn_le hc0 s0 _ Post hpost
        (by simp only [arm64_norm]; bv_arith) (by simp [arm64_norm, hrun])
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm])
        (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
        (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) ?_
      dsimp only [State.setMem]
      refine PrefixFilled.mono (k := 16) ?_ (by omega)
      exact PrefixFilled.step128_pair 0 0 (by omega) (by omega) hlen (by omega)
        (by bv_arith) (by bv_arith) rfl rfl hfc
    · have hbne0 := trunc32_zext64_and255_bne_zero hc0
      arm64_step_inst -- +0x090: ccmp w1, #0x0, #0x0, hs
      arm64_step_inst -- +0x094: b.ne +0x0dc (taken)
      refine memset_stp_setup_0x0dc prog a hc m₀ dst c n hrw hn_gt hn_le
        (dst &&& 15#64).toNat hd0_lt s0 _ Post hpost
        (by simp only [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm])
        (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
        (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) ?_
      dsimp only [State.setMem]
      refine PrefixFilled.mono (k := 16) ?_ (by omega)
      exact PrefixFilled.step128_pair 0 0 (by omega) (by omega) hlen (by omega)
        (by bv_arith) (by bv_arith) rfl rfl hfc
  · have hule160 : (160#64).ule n = false := by bv_arith
    arm64_step_inst -- +0x090: ccmp w1, #0x0, #0x0, hs
    arm64_step_inst -- +0x094: b.ne +0x0dc (taken)
    refine memset_stp_setup_0x0dc prog a hc m₀ dst c n hrw hn_gt hn_le
      (dst &&& 15#64).toNat hd0_lt s0 _ Post hpost
      (by simp only [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm])
      (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
      (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) ?_
    dsimp only [State.setMem]
    refine PrefixFilled.mono (k := 16) ?_ (by omega)
    exact PrefixFilled.step128_pair 0 0 (by omega) (by omega) hlen (by omega)
      (by bv_arith) (by bv_arith) rfl rfl hfc

/-- Large sizes (`96 < n`) of `memset`: starting at `s0.pc = a` with writable `[dst, dst + n)`,
    execution reaches `s0.readReg64 .lr` with `x0 = dst`, `MemsetLeafPreserved s0 sf`, and
    `PrefixFilled s0.mem sf.mem dst c n.toNat n.toNat`. -/
theorem memset_sym_large (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memsetWordsSym)
    (s0 : State) (Post : State → Prop)
    (dst c n : BitVec 64)
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = c)
    (hx2 : s0.readReg64 .x2 = n)
    (hrw : s0.mem.RW dst n.toNat)
    (hn96 : 96 < n.toNat) (hn_le : n.toNat + 260 ≤ 2 ^ 64)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.readReg64 .x0 = dst → MemsetLeafPreserved s0 sf →
      PrefixFilled s0.mem sf.mem dst c n.toNat n.toNat →
      Post sf) :
    reaches_pc prog (s0.readReg64 .lr) s0 Post := by
  have hfc0 : PrefixFilled s0.mem s0.mem dst c 0 n.toNat := PrefixFilled.zero s0.mem dst c n.toNat
  arm64_step_inst -- +0x000: dup v0.16b, w1
  arm64_step_inst -- +0x004: add x4, x0, x2
  arm64_step_inst -- +0x008: cmp x2, #0x60
  have hbhi96 : (96#64).ult n = true := by bv_arith
  arm64_step_inst -- +0x00c: b.hi +0x080 (taken)
  exact memset_large_0x080 prog a hc s0.mem dst c n hrw hn96 hn_le s0 _ Post hpost
    (by simp only [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1])
    (by simp [arm64_norm, hx2]) (by simp [arm64_norm])
    (by simp only [arm64_norm]; exact dup16_expand c)
    (by simp (config := { decide := true }) only [arm64_norm]) hfc0

/-! ## Sizes `n ≤ 96` as `SepWP` triples over an owned byte slice -/

abbrev MemsetFinal (s0 : State) (dst : BitVec 64) (sf : State) : Prop :=
  sf.readReg64 .x0 = dst ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧
  sf.brkStart = s0.brkStart ∧ sf.oracle = s0.oracle ∧ sf.symtab = s0.symtab ∧
  sf.sigActions = s0.sigActions ∧ sf.brk = s0.brk

/-! ### Byte-list lemmas -/

theorem memset_write64_fillSet_zero (bs : List (BitVec 8)) (p : Nat → Bool) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    ByteSlice.write64 (ByteSlice.fillSet bs 0#8 p) off 0#64 =
      ByteSlice.fillSet bs 0#8 (fun i => p i || (decide (off ≤ i) && decide (i < off + 8))) :=
  ByteSlice.writeLE_fillSet 8 bs 0#8 p off 0#64 h (fun j _ => by ext k hk; simp)

theorem memset_write64_zero (bs : List (BitVec 8)) (off : Nat) (h : off + 8 ≤ bs.length) :
    ByteSlice.write64 bs off 0#64 =
      ByteSlice.fillSet bs 0#8 (fun i => decide (off ≤ i) && decide (i < off + 8)) := by
  have := memset_write64_fillSet_zero bs (fun _ => false) off h
  rw [ByteSlice.fillSet_false] at this
  simpa only [Bool.false_or] using this

theorem memset_fillSet_fillSet (bs : List (BitVec 8)) (b : BitVec 8) (p q : Nat → Bool) :
    ByteSlice.fillSet (ByteSlice.fillSet bs b p) b q =
      ByteSlice.fillSet bs b (fun i => p i || q i) := by
  apply ByteSlice.ext_getD (by simp)
  intro i hi
  simp only [ByteSlice.fillSet_length] at hi
  simp only [ByteSlice.getD_fillSet, ByteSlice.fillSet_length, hi, decide_true, Bool.and_true]
  cases p i <;> cases q i <;> simp

theorem memset_lo64 (hi lo : BitVec 64) :
    BitVec.setWidth 64 ((hi ++ lo) >>> 0 &&& 0xffffffffffffffff#128) = lo := by
  bv_slice

theorem truncate16_truncate32 (x : BitVec 64) : (x.truncate 32).truncate 16 = x.truncate 16 := by
  ext i hi
  simp [BitVec.getElem_setWidth]

theorem memset_dup_chain (c : BitVec 64) :
    (0#128 ||| (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 0 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 8 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 16 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 24 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 32 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 40 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 48 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 56 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 64 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 72 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 80 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 88 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 96 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 104 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 112 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 120) =
      ByteSlice.bcast64 (c.truncate 8) ++ ByteSlice.bcast64 (c.truncate 8) := by
  unfold ByteSlice.bcast64
  bv_slice

/-! ### Byte-fill closers -/

local macro "memset_fill_collapse" : tactic =>
  `(tactic| try simp (disch := byte_region_len) only [ByteSlice.write64_fillSet_bcast64,
    ByteSlice.write64_bcast64, memset_write64_fillSet_zero, memset_write64_zero,
    memset_fillSet_fillSet])

local macro "memset_fill" : tactic =>
  `(tactic| (
    apply ProofLib.ByteSlice.entails_of_eq
    apply ProofLib.pointsToBytes_congr_bytes
    memset_fill_collapse
    first
    | (refine ByteSlice.fillSet_all (by omega) ?_
       intro i hi
       simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
       omega)
    | (refine ByteSlice.fillSet_congr ?_
       intro i hi
       rw [Bool.eq_iff_iff]
       simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
       omega)))

/-! ## Small sizes (`n < 16`, `+0x018`) -/

section Small
variable (prog : Program) (a : BitVec 64) (hc : prog.hasCode a memsetWordsSym)
  (s0 : State) (dst c n : BitVec 64) (bs : List (BitVec 8))
  (hpc : s0.pc = a) (hrun : s0.status = .Running)
  (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = c)
  (hx2 : s0.readReg64 .x2 = n) (hlen : bs.length = n.toNat)
include hc hpc hrun hx0 hx1 hx2 hlen

theorem memset_small8 (hn8 : 8 ≤ n.toNat) (hn16 : n.toNat < 16) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  have hdup := memset_dup_chain c
  have hlo := memset_lo64 (ByteSlice.bcast64 (c.truncate 8)) (ByteSlice.bcast64 (c.truncate 8))
  have hbhi96 : (96#64).ult n = false := by bv_arith
  have hule16 : (16#64).ule n = false := by bv_arith
  have htbz3 : n.getLsbD 3 = true := by bv_bits
  wp_sym_steps
  wp_done

theorem memset_small4 (hn4 : 4 ≤ n.toNat) (hn8 : n.toNat < 8) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  have hdup := memset_dup_chain c
  have hlo := memset_lo64 (ByteSlice.bcast64 (c.truncate 8)) (ByteSlice.bcast64 (c.truncate 8))
  have hbhi96 : (96#64).ult n = false := by bv_arith
  have hule16 : (16#64).ule n = false := by bv_arith
  have htbz3 : n.getLsbD 3 = false := by bv_bits
  have htbz2 : n.getLsbD 2 = true := by bv_bits
  wp_sym_steps
  simp (disch := byte_region_len) only [ByteSlice.write32_bcast64]
  wp_done

theorem memset_small2 (hn1 : 1 ≤ n.toNat) (hn4 : n.toNat < 4) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  have hdup := memset_dup_chain c
  have hlo := memset_lo64 (ByteSlice.bcast64 (c.truncate 8)) (ByteSlice.bcast64 (c.truncate 8))
  have hbhi96 : (96#64).ult n = false := by bv_arith
  have hule16 : (16#64).ule n = false := by bv_arith
  have htbz3 : n.getLsbD 3 = false := by bv_bits
  have htbz2 : n.getLsbD 2 = false := by bv_bits
  have hn0 : (n == 0#64) = false := by bv_arith
  by_cases hn2 : 2 ≤ n.toNat
  · have h1 : n.getLsbD 1 = true := by bv_bits
    wp_sym_steps
    simp (disch := byte_region_len) only [truncate16_truncate32, ByteSlice.write16_bcast64,
      ByteSlice.bcast64_truncate8]
    wp_done
  · have h1 : n.getLsbD 1 = false := by bv_bits
    wp_sym_steps
    simp (disch := byte_region_len) only [ByteSlice.bcast64_truncate8]
    wp_done

theorem memset_small0 (hn0 : n.toNat = 0) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  have hdup := memset_dup_chain c
  have hlo := memset_lo64 (ByteSlice.bcast64 (c.truncate 8)) (ByteSlice.bcast64 (c.truncate 8))
  have hn : n = 0#64 := by bv_omega
  subst hn
  wp_sym_steps
  wp_done

/-! ## Medium sizes (`16 ≤ n ≤ 96`, `+0x054`) -/

theorem memset_medium16 (hn16 : 16 ≤ n.toNat) (hn64 : n.toNat < 64) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  have hdup := memset_dup_chain c
  have hlo := memset_lo64 (ByteSlice.bcast64 (c.truncate 8)) (ByteSlice.bcast64 (c.truncate 8))
  have hbhi96 : (96#64).ult n = false := by bv_arith
  have hule16 : (16#64).ule n = true := by bv_arith
  have htbnz6 : n.getLsbD 6 = false := by bv_bits
  by_cases hn32 : 32 ≤ n.toNat
  · have htbz5 : n.getLsbD 5 = true := by bv_bits
    wp_sym_steps
    refine SepWP.weaken_pre (P' := dst ↦ₛ List.replicate n.toNat (c.truncate 8))
      (by memset_fill) ?_
    wp_done
  · have htbz5 : n.getLsbD 5 = false := by bv_bits
    wp_sym_steps
    refine SepWP.weaken_pre (P' := dst ↦ₛ List.replicate n.toNat (c.truncate 8))
      (by memset_fill) ?_
    wp_done

theorem memset_medium64 (hn64 : 64 ≤ n.toNat) (hn96 : n.toNat ≤ 96) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  have hdup := memset_dup_chain c
  have hlo := memset_lo64 (ByteSlice.bcast64 (c.truncate 8)) (ByteSlice.bcast64 (c.truncate 8))
  have hbhi96 : (96#64).ult n = false := by bv_arith
  have hule16 : (16#64).ule n = true := by bv_arith
  have htbnz6 : n.getLsbD 6 = true := by bv_bits
  wp_sym_steps
  refine SepWP.weaken_pre (P' := dst ↦ₛ List.replicate n.toNat (c.truncate 8))
    (by memset_fill) ?_
  wp_done

end Small

/-- `memset` for `n ≤ 96` as a `SepWP` triple over the owned destination slice: starting at
    `s0.pc = a`, it returns to `lr` with `x0 = dst`, the stack pointer and callee-saved registers
    preserved, and `dst ↦ₛ List.replicate n (c.truncate 8)`. -/
theorem memset_sepWP_le96 (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memsetWordsSym)
    (s0 : State) (dst c n : BitVec 64) (bs : List (BitVec 8))
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = c)
    (hx2 : s0.readReg64 .x2 = n) (hlen : bs.length = n.toNat) (hn96 : n.toNat ≤ 96) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  by_cases hn64 : 64 ≤ n.toNat
  · exact memset_medium64 prog a hc s0 dst c n bs hpc hrun hx0 hx1 hx2 hlen hn64 hn96
  by_cases hn16 : 16 ≤ n.toNat
  · exact memset_medium16 prog a hc s0 dst c n bs hpc hrun hx0 hx1 hx2 hlen hn16 (by omega)
  by_cases hn8 : 8 ≤ n.toNat
  · exact memset_small8 prog a hc s0 dst c n bs hpc hrun hx0 hx1 hx2 hlen hn8 (by omega)
  by_cases hn4 : 4 ≤ n.toNat
  · exact memset_small4 prog a hc s0 dst c n bs hpc hrun hx0 hx1 hx2 hlen hn4 (by omega)
  by_cases hn1 : 1 ≤ n.toNat
  · exact memset_small2 prog a hc s0 dst c n bs hpc hrun hx0 hx1 hx2 hlen hn1 (by omega)
  · exact memset_small0 prog a hc s0 dst c n bs hpc hrun hx0 hx1 hx2 hlen (by omega)

end VerifiedLibraries.Mallocng.Proofs
