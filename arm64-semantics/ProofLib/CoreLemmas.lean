/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Std.Tactic.BVDecide
public import Arm64
public import Arm64.Trusted.Spec.SepLogicModel
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model
public import ProofLib.SepLogic.Defs
public import ProofLib.Hoare.SubroutineOk
public import ProofLib.SimpAttrs
public import ProofLib.Invariant
public import ProofLib.BV.Bits

/-!
# Core Memory, State, Semantics, and Hoare Logic Lemmas

Foundational simplification and reasoning lemmas for `Memory` read-over-write and region
disjointness, `State` register and field updates, small-step operational semantics (`Step`,
`Steps`, `StepsUntil`), separation-logic entailment, and `reaches_pc` / `subroutine_ok` Hoare
contracts.
-/

@[expose] public section

namespace Arm64

/-! ## Memory Simplification and Read-Over-Write Lemmas -/

namespace Memory

@[simp]
theorem writeBytes_nil (m : Memory) (base : BitVec 64) : m.writeBytes base [] = m := rfl

@[simp]
theorem writeBytes_cons (m : Memory) (base : BitVec 64) (b : BitVec 8) (rest : List (BitVec 8)) :
    m.writeBytes base (b :: rest) = (m.write8 base b).writeBytes (base + 1#64) rest := rfl

theorem writeBytes_append (m : Memory) (a : BitVec 64) (xs ys : List (BitVec 8)) :
    m.writeBytes a (xs ++ ys) =
      (m.writeBytes a xs).writeBytes (a + BitVec.ofNat 64 xs.length) ys := by
  induction xs generalizing m a with
  | nil => simp [writeBytes]
  | cons x xs ih =>
    have hadd : a + 1#64 + BitVec.ofNat 64 xs.length = a + BitVec.ofNat 64 (xs.length + 1) := by
      bv_arith
    simp only [List.cons_append, List.length_cons, writeBytes, ih, hadd]

@[simp]
theorem readBytes_zero (m : Memory) (base : BitVec 64) : m.readBytes base 0 = [] := rfl

@[simp]
theorem readBytes_succ (m : Memory) (base : BitVec 64) (n : Nat) :
    m.readBytes base (n + 1) = m.read8 base :: m.readBytes (base + 1#64) n := rfl

@[simp]
theorem readBytes_length (m : Memory) (p : BitVec 64) (n : Nat) :
    (m.readBytes p n).length = n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [readBytes_succ, ih]

theorem readBytes_congr {m₁ m₂ : Memory} (p : BitVec 64) (n : Nat)
    (h : ∀ i : Nat, i < n →
      m₂.read8 (p + BitVec.ofNat 64 i) = m₁.read8 (p + BitVec.ofNat 64 i)) :
    m₂.readBytes p n = m₁.readBytes p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [readBytes_succ]
    have h0 : m₂.read8 p = m₁.read8 p := by simpa using h 0 (Nat.zero_lt_succ n)
    have hrest : m₂.readBytes (p + 1#64) n = m₁.readBytes (p + 1#64) n := by
      apply ih (p + 1#64)
      intro i hi
      have hadd : p + 1#64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (i + 1) := by bv_arith
      rw [hadd]
      exact h (i + 1) (Nat.succ_lt_succ hi)
    rw [h0, hrest]

/-- `readBytes` returns `bs` when every byte of `bs` is at its offset. -/
theorem readBytes_of_read8 {m : Memory} {base : BitVec 64} {bs : List (BitVec 8)}
    (h : ∀ i (hi : i < bs.length), m.read8 (base + BitVec.ofNat 64 i) = bs[i]) :
    m.readBytes base bs.length = bs := by
  induction bs generalizing base with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons, readBytes_succ, List.cons.injEq]
    refine ⟨?_, ih (base := base + 1#64) fun i hi => ?_⟩
    · simpa using h 0 (Nat.zero_lt_succ _)
    · have hadd : base + 1#64 + BitVec.ofNat 64 i = base + BitVec.ofNat 64 (i + 1) := by
        bv_arith
      rw [hadd]
      exact h (i + 1) (Nat.succ_lt_succ hi)

@[simp]
theorem read8_write8_same (m : Memory) (a : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).read8 a = v := by
  simp

theorem add_eq_add_left (a x y : BitVec 64) : (a + x = a + y) ↔ (x = y) := by
  constructor
  · intro h; bv_arith
  · intro h; subst h; rfl

@[simp]
theorem add_eq_self_left (a x : BitVec 64) : (a + x = a) ↔ (x = 0#64) := by
  constructor
  · intro h; bv_arith
  · intro h; subst h; simp

@[simp]
theorem self_eq_add_left (a y : BitVec 64) : (a = a + y) ↔ (0#64 = y) := by
  constructor
  · intro h; bv_arith
  · intro h; subst h; simp

theorem read8_write16 (m : Memory) (addr a : BitVec 64) (val : BitVec 16) :
    (m.write16 addr val).read8 a =
      if a = addr + 1#64 then val.extractLsb' 8 8
      else if a = addr then val.extractLsb' 0 8
      else m.read8 a := by
  simp [write16, read8_write8]

theorem read8_write32 (m : Memory) (addr a : BitVec 64) (val : BitVec 32) :
    (m.write32 addr val).read8 a =
      if a = addr + 3#64 then val.extractLsb' 24 8
      else if a = addr + 2#64 then val.extractLsb' 16 8
      else if a = addr + 1#64 then val.extractLsb' 8 8
      else if a = addr then val.extractLsb' 0 8
      else m.read8 a := by
  simp [write32, read8_write8]

theorem read8_write64 (m : Memory) (addr a : BitVec 64) (val : BitVec 64) :
    (m.write64 addr val).read8 a =
      if a = addr + 7#64 then val.extractLsb' 56 8
      else if a = addr + 6#64 then val.extractLsb' 48 8
      else if a = addr + 5#64 then val.extractLsb' 40 8
      else if a = addr + 4#64 then val.extractLsb' 32 8
      else if a = addr + 3#64 then val.extractLsb' 24 8
      else if a = addr + 2#64 then val.extractLsb' 16 8
      else if a = addr + 1#64 then val.extractLsb' 8 8
      else if a = addr then val.extractLsb' 0 8
      else m.read8 a := by
  simp [write64, read8_write8]

theorem concat_bytes_16 (v : BitVec 16) :
    v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  bv_decide

theorem concat_bytes_32 (v : BitVec 32) :
    v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  bv_decide

theorem concat_bytes_64 (v : BitVec 64) :
    v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++
    v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  bv_decide

@[simp]
theorem read16_write16_same (m : Memory) (addr : BitVec 64) (v : BitVec 16) :
    (m.write16 addr v).read16 addr = v := by
  simp [read16, read8_write16]
  exact concat_bytes_16 v

@[simp]
theorem read32_write32_same (m : Memory) (addr : BitVec 64) (v : BitVec 32) :
    (m.write32 addr v).read32 addr = v := by
  simp [read32, read8_write32]
  exact concat_bytes_32 v

@[simp]
theorem read64_write64_same (m : Memory) (addr : BitVec 64) (v : BitVec 64) :
    (m.write64 addr v).read64 addr = v := by
  simp [read64, read8_write64]
  exact concat_bytes_64 v

/-! ### Same-Address Sub-Slice Forwarding (`readR` from wider `writeW` at `addr`) -/

@[simp]
theorem read8_write16_same (m : Memory) (addr : BitVec 64) (v : BitVec 16) :
    (m.write16 addr v).read8 addr = v.extractLsb' 0 8 := by
  simp [read8_write16]

@[simp]
theorem read8_write32_same (m : Memory) (addr : BitVec 64) (v : BitVec 32) :
    (m.write32 addr v).read8 addr = v.extractLsb' 0 8 := by
  simp [read8_write32]

@[simp]
theorem read8_write64_same (m : Memory) (addr : BitVec 64) (v : BitVec 64) :
    (m.write64 addr v).read8 addr = v.extractLsb' 0 8 := by
  simp [read8_write64]

@[simp]
theorem read16_write32_same (m : Memory) (addr : BitVec 64) (v : BitVec 32) :
    (m.write32 addr v).read16 addr = v.extractLsb' 0 16 := by
  simp [read16, read8_write32]
  bv_decide

@[simp]
theorem read16_write64_same (m : Memory) (addr : BitVec 64) (v : BitVec 64) :
    (m.write64 addr v).read16 addr = v.extractLsb' 0 16 := by
  simp [read16, read8_write64]
  bv_decide

@[simp]
theorem read32_write64_same (m : Memory) (addr : BitVec 64) (v : BitVec 64) :
    (m.write64 addr v).read32 addr = v.extractLsb' 0 32 := by
  simp [read32, read8_write64]
  bv_decide

/-! ### In-Bounds Sub-Slice Forwarding (`readR` inside wider `writeW`) -/

private theorem add_sub_add_left (base off1 off2 : BitVec 64) :
    (base + off2) - (base + off1) = off2 - off1 := by bv_arith

private theorem self_sub_add_left (base off : BitVec 64) :
    base - (base + off) = 0#64 - off := by bv_arith

private theorem add_sub_self_left (base off : BitVec 64) :
    (base + off) - base = off := by bv_arith

private theorem add_sub_self_left_zero (base off : BitVec 64) :
    (base + off) - base = off - 0#64 := by bv_arith

theorem read8_write16_inbounds (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : (a2 - a1).toNat < 2) :
    (m.write16 a1 v).read8 a2 = v.extractLsb' (8 * (a2 - a1).toNat) 8 := by
  have ha : (m.write16 a1 v).read8 a2 = (m.write16 a1 v).read8 (a1 + BitVec.ofNat 64 (a2 - a1).toNat) := by
    congr 1; bv_arith
  rw [ha]; clear ha
  have hd : (a2 - a1).toNat = 0 ∨ (a2 - a1).toNat = 1 := by omega
  rcases hd with hd | hd <;> (rw [hd]; simp [read8_write16])

theorem read8_write32_inbounds (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : (a2 - a1).toNat < 4) :
    (m.write32 a1 v).read8 a2 = v.extractLsb' (8 * (a2 - a1).toNat) 8 := by
  have ha : (m.write32 a1 v).read8 a2 = (m.write32 a1 v).read8 (a1 + BitVec.ofNat 64 (a2 - a1).toNat) := by
    congr 1; bv_arith
  rw [ha]; clear ha
  have hd : (a2 - a1).toNat = 0 ∨ (a2 - a1).toNat = 1 ∨ (a2 - a1).toNat = 2 ∨ (a2 - a1).toNat = 3 := by omega
  rcases hd with hd | hd | hd | hd <;> (rw [hd]; simp [read8_write32])

theorem read8_write64_inbounds (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : (a2 - a1).toNat < 8) :
    (m.write64 a1 v).read8 a2 = v.extractLsb' (8 * (a2 - a1).toNat) 8 := by
  have ha : (m.write64 a1 v).read8 a2 = (m.write64 a1 v).read8 (a1 + BitVec.ofNat 64 (a2 - a1).toNat) := by
    congr 1; bv_arith
  rw [ha]; clear ha
  have hd : (a2 - a1).toNat = 0 ∨ (a2 - a1).toNat = 1 ∨ (a2 - a1).toNat = 2 ∨ (a2 - a1).toNat = 3 ∨
            (a2 - a1).toNat = 4 ∨ (a2 - a1).toNat = 5 ∨ (a2 - a1).toNat = 6 ∨ (a2 - a1).toNat = 7 := by omega
  rcases hd with hd | hd | hd | hd | hd | hd | hd | hd <;> (rw [hd]; simp [read8_write64])

theorem read16_write32_inbounds (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : (a2 - a1).toNat + 2 ≤ 4) :
    (m.write32 a1 v).read16 a2 = v.extractLsb' (8 * (a2 - a1).toNat) 16 := by
  dsimp only [read16]
  have h0 : ((a2 + 0#64) - a1).toNat = (a2 - a1).toNat := by bv_arith
  have h1 : ((a2 + 1#64) - a1).toNat = (a2 - a1).toNat + 1 := by bv_arith
  rw [read8_write32_inbounds m a1 (a2 + 1#64) v (by omega),
      read8_write32_inbounds m a1 (a2 + 0#64) v (by omega), h0, h1]
  have hd : (a2 - a1).toNat = 0 ∨ (a2 - a1).toNat = 1 ∨ (a2 - a1).toNat = 2 := by omega
  rcases hd with hd | hd | hd <;> (rw [hd]; bv_decide)

theorem read16_write64_inbounds (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : (a2 - a1).toNat + 2 ≤ 8) :
    (m.write64 a1 v).read16 a2 = v.extractLsb' (8 * (a2 - a1).toNat) 16 := by
  dsimp only [read16]
  have h0 : ((a2 + 0#64) - a1).toNat = (a2 - a1).toNat := by bv_arith
  have h1 : ((a2 + 1#64) - a1).toNat = (a2 - a1).toNat + 1 := by bv_arith
  rw [read8_write64_inbounds m a1 (a2 + 1#64) v (by omega),
      read8_write64_inbounds m a1 (a2 + 0#64) v (by omega), h0, h1]
  have hd : (a2 - a1).toNat = 0 ∨ (a2 - a1).toNat = 1 ∨ (a2 - a1).toNat = 2 ∨ (a2 - a1).toNat = 3 ∨
            (a2 - a1).toNat = 4 ∨ (a2 - a1).toNat = 5 ∨ (a2 - a1).toNat = 6 := by omega
  rcases hd with hd | hd | hd | hd | hd | hd | hd <;> (rw [hd]; bv_decide)

theorem read32_write64_inbounds (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : (a2 - a1).toNat + 4 ≤ 8) :
    (m.write64 a1 v).read32 a2 = v.extractLsb' (8 * (a2 - a1).toNat) 32 := by
  have hsplit : (m.write64 a1 v).read32 a2 =
      (m.write64 a1 v).read16 (a2 + 2#64) ++ (m.write64 a1 v).read16 a2 := by
    dsimp only [read32, read16]
    have h20 : (a2 + 2#64) + 0#64 = a2 + 2#64 := by bv_arith
    have h21 : (a2 + 2#64) + 1#64 = a2 + 3#64 := by bv_arith
    rw [h20, h21]; bv_bits
  have h2 : ((a2 + 2#64) - a1).toNat = (a2 - a1).toNat + 2 := by bv_arith
  rw [hsplit,
      read16_write64_inbounds m a1 (a2 + 2#64) v (by omega),
      read16_write64_inbounds m a1 a2 v (by omega), h2]
  have hd : (a2 - a1).toNat = 0 ∨ (a2 - a1).toNat = 1 ∨ (a2 - a1).toNat = 2 ∨
            (a2 - a1).toNat = 3 ∨ (a2 - a1).toNat = 4 := by omega
  rcases hd with hd | hd | hd | hd | hd <;> (rw [hd]; bv_bits)

@[simp]
theorem read8_write16_base_off_inbounds (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 16)
    (h : decide ((off2 - off1).toNat < 2) = true) :
    (m.write16 (base + off1) v).read8 (base + off2) = v.extractLsb' (8 * (off2 - off1).toNat) 8 := by
  have h1 := of_decide_eq_true h
  have hsub := add_sub_add_left base off1 off2
  have hin := read8_write16_inbounds m (base + off1) (base + off2) v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read8_write16_base_off_zero_inbounds (m : Memory) (base off : BitVec 64) (v : BitVec 16)
    (h : decide (off.toNat < 2) = true) :
    (m.write16 base v).read8 (base + off) = v.extractLsb' (8 * off.toNat) 8 := by
  have h1 := of_decide_eq_true h
  have hsub := add_sub_self_left base off
  have hin := read8_write16_inbounds m base (base + off) v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read8_write16_base_zero_off_inbounds (m : Memory) (base off : BitVec 64) (v : BitVec 16)
    (h : decide ((0#64 - off).toNat < 2) = true) :
    (m.write16 (base + off) v).read8 base = v.extractLsb' (8 * (0#64 - off).toNat) 8 := by
  have h1 := of_decide_eq_true h
  have hsub := self_sub_add_left base off
  have hin := read8_write16_inbounds m (base + off) base v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read8_write32_base_off_inbounds (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 32)
    (h : decide ((off2 - off1).toNat < 4) = true) :
    (m.write32 (base + off1) v).read8 (base + off2) = v.extractLsb' (8 * (off2 - off1).toNat) 8 := by
  have h1 := of_decide_eq_true h
  have hsub := add_sub_add_left base off1 off2
  have hin := read8_write32_inbounds m (base + off1) (base + off2) v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read8_write32_base_off_zero_inbounds (m : Memory) (base off : BitVec 64) (v : BitVec 32)
    (h : decide (off.toNat < 4) = true) :
    (m.write32 base v).read8 (base + off) = v.extractLsb' (8 * off.toNat) 8 := by
  have h1 := of_decide_eq_true h
  have hsub := add_sub_self_left base off
  have hin := read8_write32_inbounds m base (base + off) v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read8_write32_base_zero_off_inbounds (m : Memory) (base off : BitVec 64) (v : BitVec 32)
    (h : decide ((0#64 - off).toNat < 4) = true) :
    (m.write32 (base + off) v).read8 base = v.extractLsb' (8 * (0#64 - off).toNat) 8 := by
  have h1 := of_decide_eq_true h
  have hsub := self_sub_add_left base off
  have hin := read8_write32_inbounds m (base + off) base v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read8_write64_base_off_inbounds (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 64)
    (h : decide ((off2 - off1).toNat < 8) = true) :
    (m.write64 (base + off1) v).read8 (base + off2) = v.extractLsb' (8 * (off2 - off1).toNat) 8 := by
  have h1 := of_decide_eq_true h
  have hsub := add_sub_add_left base off1 off2
  have hin := read8_write64_inbounds m (base + off1) (base + off2) v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read8_write64_base_off_zero_inbounds (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide (off.toNat < 8) = true) :
    (m.write64 base v).read8 (base + off) = v.extractLsb' (8 * off.toNat) 8 := by
  have h1 := of_decide_eq_true h
  have hsub := add_sub_self_left base off
  have hin := read8_write64_inbounds m base (base + off) v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read8_write64_base_zero_off_inbounds (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide ((0#64 - off).toNat < 8) = true) :
    (m.write64 (base + off) v).read8 base = v.extractLsb' (8 * (0#64 - off).toNat) 8 := by
  have h1 := of_decide_eq_true h
  have hsub := self_sub_add_left base off
  have hin := read8_write64_inbounds m (base + off) base v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read16_write32_base_off_inbounds (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 32)
    (h : decide ((off2 - off1).toNat + 2 ≤ 4) = true) :
    (m.write32 (base + off1) v).read16 (base + off2) = v.extractLsb' (8 * (off2 - off1).toNat) 16 := by
  have h1 := of_decide_eq_true h
  have hsub := add_sub_add_left base off1 off2
  have hin := read16_write32_inbounds m (base + off1) (base + off2) v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read16_write32_base_off_zero_inbounds (m : Memory) (base off : BitVec 64) (v : BitVec 32)
    (h : decide (off.toNat + 2 ≤ 4) = true) :
    (m.write32 base v).read16 (base + off) = v.extractLsb' (8 * off.toNat) 16 := by
  have h1 := of_decide_eq_true h
  have hsub := add_sub_self_left base off
  have hin := read16_write32_inbounds m base (base + off) v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read16_write32_base_zero_off_inbounds (m : Memory) (base off : BitVec 64) (v : BitVec 32)
    (h : decide ((0#64 - off).toNat + 2 ≤ 4) = true) :
    (m.write32 (base + off) v).read16 base = v.extractLsb' (8 * (0#64 - off).toNat) 16 := by
  have h1 := of_decide_eq_true h
  have hsub := self_sub_add_left base off
  have hin := read16_write32_inbounds m (base + off) base v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read16_write64_base_off_inbounds (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 64)
    (h : decide ((off2 - off1).toNat + 2 ≤ 8) = true) :
    (m.write64 (base + off1) v).read16 (base + off2) = v.extractLsb' (8 * (off2 - off1).toNat) 16 := by
  have h1 := of_decide_eq_true h
  have hsub := add_sub_add_left base off1 off2
  have hin := read16_write64_inbounds m (base + off1) (base + off2) v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read16_write64_base_off_zero_inbounds (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide (off.toNat + 2 ≤ 8) = true) :
    (m.write64 base v).read16 (base + off) = v.extractLsb' (8 * off.toNat) 16 := by
  have h1 := of_decide_eq_true h
  have hsub := add_sub_self_left base off
  have hin := read16_write64_inbounds m base (base + off) v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read16_write64_base_zero_off_inbounds (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide ((0#64 - off).toNat + 2 ≤ 8) = true) :
    (m.write64 (base + off) v).read16 base = v.extractLsb' (8 * (0#64 - off).toNat) 16 := by
  have h1 := of_decide_eq_true h
  have hsub := self_sub_add_left base off
  have hin := read16_write64_inbounds m (base + off) base v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read32_write64_base_off_inbounds (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 64)
    (h : decide ((off2 - off1).toNat + 4 ≤ 8) = true) :
    (m.write64 (base + off1) v).read32 (base + off2) = v.extractLsb' (8 * (off2 - off1).toNat) 32 := by
  have h1 := of_decide_eq_true h
  have hsub := add_sub_add_left base off1 off2
  have hin := read32_write64_inbounds m (base + off1) (base + off2) v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read32_write64_base_off_zero_inbounds (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide (off.toNat + 4 ≤ 8) = true) :
    (m.write64 base v).read32 (base + off) = v.extractLsb' (8 * off.toNat) 32 := by
  have h1 := of_decide_eq_true h
  have hsub := add_sub_self_left base off
  have hin := read32_write64_inbounds m base (base + off) v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

@[simp]
theorem read32_write64_base_zero_off_inbounds (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide ((0#64 - off).toNat + 4 ≤ 8) = true) :
    (m.write64 (base + off) v).read32 base = v.extractLsb' (8 * (0#64 - off).toNat) 32 := by
  have h1 := of_decide_eq_true h
  have hsub := self_sub_add_left base off
  have hin := read32_write64_inbounds m (base + off) base v (by rw [hsub]; exact h1)
  rwa [hsub] at hin

/-! ### Adjacent Narrow Writes Read by Wider Load -/

@[simp]
theorem read16_write8_write8_adjacent (m : Memory) (addr : BitVec 64) (lo hi : BitVec 8) :
    ((m.write8 addr lo).write8 (addr + 1#64) hi).read16 addr = hi ++ lo := by
  simp [read16, read8_write8]

@[simp]
theorem read16_write8_write8_base_off_adjacent (m : Memory) (base off1 off2 : BitVec 64) (lo hi : BitVec 8)
    (h : decide (off2 = off1 + 1#64) = true) :
    ((m.write8 (base + off1) lo).write8 (base + off2) hi).read16 (base + off1) = hi ++ lo := by
  have heq := of_decide_eq_true h
  subst heq
  rw [← BitVec.add_assoc, read16_write8_write8_adjacent]

@[simp]
theorem read32_write16_write16_adjacent (m : Memory) (addr : BitVec 64) (lo hi : BitVec 16) :
    ((m.write16 addr lo).write16 (addr + 2#64) hi).read32 addr = hi ++ lo := by
  simp [read32, read8_write16, BitVec.add_assoc]
  bv_bits

@[simp]
theorem read32_write16_write16_base_off_adjacent (m : Memory) (base off1 off2 : BitVec 64) (lo hi : BitVec 16)
    (h : decide (off2 = off1 + 2#64) = true) :
    ((m.write16 (base + off1) lo).write16 (base + off2) hi).read32 (base + off1) = hi ++ lo := by
  have heq := of_decide_eq_true h
  subst heq
  rw [← BitVec.add_assoc, read32_write16_write16_adjacent]

@[simp]
theorem read64_write32_write32_adjacent (m : Memory) (addr : BitVec 64) (lo hi : BitVec 32) :
    ((m.write32 addr lo).write32 (addr + 4#64) hi).read64 addr = hi ++ lo := by
  simp [read64, read8_write32, BitVec.add_assoc]
  bv_bits

@[simp]
theorem read64_write32_write32_base_off_adjacent (m : Memory) (base off1 off2 : BitVec 64) (lo hi : BitVec 32)
    (h : decide (off2 = off1 + 4#64) = true) :
    ((m.write32 (base + off1) lo).write32 (base + off2) hi).read64 (base + off1) = hi ++ lo := by
  have heq := of_decide_eq_true h
  subst heq
  rw [← BitVec.add_assoc, read64_write32_write32_adjacent]

/-! ### Cross-Width Byte-Disjoint Read-Over-Write Lemmas (`{8, 16, 32, 64} × {8, 16, 32, 64}`) -/

private theorem ite_false_right {α : Type} {c : Prop} [Decidable c] (t e : α) (hc : ¬c) :
    (if c then t else e) = e :=
  ite_eq_right_iff.mpr (fun h => False.elim (hc h))

private theorem read16_eq_of_read8 {m1 m2 : Memory} {a : BitVec 64}
    (h : ∀ (i : BitVec 64), i.toNat < 2 → m1.read8 (a + i) = m2.read8 (a + i)) :
    m1.read16 a = m2.read16 a := by
  dsimp only [read16]
  rw [h 0#64 (by decide), h 1#64 (by decide)]

private theorem read32_eq_of_read8 {m1 m2 : Memory} {a : BitVec 64}
    (h : ∀ (i : BitVec 64), i.toNat < 4 → m1.read8 (a + i) = m2.read8 (a + i)) :
    m1.read32 a = m2.read32 a := by
  dsimp only [read32]
  rw [h 0#64 (by decide), h 1#64 (by decide), h 2#64 (by decide), h 3#64 (by decide)]

private theorem read64_eq_of_read8 {m1 m2 : Memory} {a : BitVec 64}
    (h : ∀ (i : BitVec 64), i.toNat < 8 → m1.read8 (a + i) = m2.read8 (a + i)) :
    m1.read64 a = m2.read64 a := by
  dsimp only [read64]
  rw [h 0#64 (by decide), h 1#64 (by decide), h 2#64 (by decide), h 3#64 (by decide),
      h 4#64 (by decide), h 5#64 (by decide), h 6#64 (by decide), h 7#64 (by decide)]

private theorem offset_disjoint {a1 a2 i : BitVec 64} {W R : Nat}
    (h1 : (a2 - a1).toNat ≥ W) (h2 : (a1 - a2).toNat ≥ R) (hWR : W ≤ 8 ∧ R ≤ 8) (hi : i.toNat < R) :
    ((a2 + i) - a1).toNat ≥ W ∧ (a1 - (a2 + i)).toNat ≥ 1 := by
  exact ⟨by bv_arith, by bv_arith⟩

theorem read8_write8_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (_h1 : (a2 - a1).toNat ≥ 1) (_h2 : (a1 - a2).toNat ≥ 1) :
    (m.write8 a1 v).read8 a2 = m.read8 a2 := by
  have hne : a2 ≠ a1 := by bv_arith
  simp only [read8_write8, hne, ↓reduceIte]

theorem read8_write16_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h1 : (a2 - a1).toNat ≥ 2) (_h2 : (a1 - a2).toNat ≥ 1) :
    (m.write16 a1 v).read8 a2 = m.read8 a2 := by
  have hne : ∀ j : BitVec 64, j.toNat < 2 → a2 ≠ a1 + j := by intro j hj; bv_arith
  simp only [write16, read8_write8]
  repeat' (rw [ite_false_right _ _ (hne _ (by decide))])

theorem read8_write32_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h1 : (a2 - a1).toNat ≥ 4) (_h2 : (a1 - a2).toNat ≥ 1) :
    (m.write32 a1 v).read8 a2 = m.read8 a2 := by
  have hne : ∀ j : BitVec 64, j.toNat < 4 → a2 ≠ a1 + j := by intro j hj; bv_arith
  simp only [write32, read8_write8]
  repeat' (rw [ite_false_right _ _ (hne _ (by decide))])

theorem read8_write64_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h1 : (a2 - a1).toNat ≥ 8) (_h2 : (a1 - a2).toNat ≥ 1) :
    (m.write64 a1 v).read8 a2 = m.read8 a2 := by
  have hne : ∀ j : BitVec 64, j.toNat < 8 → a2 ≠ a1 + j := by intro j hj; bv_arith
  simp only [write64, read8_write8]
  repeat' (rw [ite_false_right _ _ (hne _ (by decide))])

theorem read16_write8_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h1 : (a2 - a1).toNat ≥ 1) (h2 : (a1 - a2).toNat ≥ 2) :
    (m.write8 a1 v).read16 a2 = m.read16 a2 := by
  apply read16_eq_of_read8; intro i hi
  have ⟨hd1, hd2⟩ := offset_disjoint h1 h2 (by decide) hi
  exact read8_write8_disjoint m a1 (a2 + i) v hd1 hd2

theorem read16_write16_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h1 : (a2 - a1).toNat ≥ 2) (h2 : (a1 - a2).toNat ≥ 2) :
    (m.write16 a1 v).read16 a2 = m.read16 a2 := by
  apply read16_eq_of_read8; intro i hi
  have ⟨hd1, hd2⟩ := offset_disjoint h1 h2 (by decide) hi
  exact read8_write16_disjoint m a1 (a2 + i) v hd1 hd2

theorem read16_write32_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h1 : (a2 - a1).toNat ≥ 4) (h2 : (a1 - a2).toNat ≥ 2) :
    (m.write32 a1 v).read16 a2 = m.read16 a2 := by
  apply read16_eq_of_read8; intro i hi
  have ⟨hd1, hd2⟩ := offset_disjoint h1 h2 (by decide) hi
  exact read8_write32_disjoint m a1 (a2 + i) v hd1 hd2

theorem read16_write64_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h1 : (a2 - a1).toNat ≥ 8) (h2 : (a1 - a2).toNat ≥ 2) :
    (m.write64 a1 v).read16 a2 = m.read16 a2 := by
  apply read16_eq_of_read8; intro i hi
  have ⟨hd1, hd2⟩ := offset_disjoint h1 h2 (by decide) hi
  exact read8_write64_disjoint m a1 (a2 + i) v hd1 hd2

theorem read32_write8_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h1 : (a2 - a1).toNat ≥ 1) (h2 : (a1 - a2).toNat ≥ 4) :
    (m.write8 a1 v).read32 a2 = m.read32 a2 := by
  apply read32_eq_of_read8; intro i hi
  have ⟨hd1, hd2⟩ := offset_disjoint h1 h2 (by decide) hi
  exact read8_write8_disjoint m a1 (a2 + i) v hd1 hd2

theorem read32_write16_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h1 : (a2 - a1).toNat ≥ 2) (h2 : (a1 - a2).toNat ≥ 4) :
    (m.write16 a1 v).read32 a2 = m.read32 a2 := by
  apply read32_eq_of_read8; intro i hi
  have ⟨hd1, hd2⟩ := offset_disjoint h1 h2 (by decide) hi
  exact read8_write16_disjoint m a1 (a2 + i) v hd1 hd2

theorem read32_write32_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h1 : (a2 - a1).toNat ≥ 4) (h2 : (a1 - a2).toNat ≥ 4) :
    (m.write32 a1 v).read32 a2 = m.read32 a2 := by
  apply read32_eq_of_read8; intro i hi
  have ⟨hd1, hd2⟩ := offset_disjoint h1 h2 (by decide) hi
  exact read8_write32_disjoint m a1 (a2 + i) v hd1 hd2

theorem read32_write64_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h1 : (a2 - a1).toNat ≥ 8) (h2 : (a1 - a2).toNat ≥ 4) :
    (m.write64 a1 v).read32 a2 = m.read32 a2 := by
  apply read32_eq_of_read8; intro i hi
  have ⟨hd1, hd2⟩ := offset_disjoint h1 h2 (by decide) hi
  exact read8_write64_disjoint m a1 (a2 + i) v hd1 hd2

theorem read64_write8_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h1 : (a2 - a1).toNat ≥ 1) (h2 : (a1 - a2).toNat ≥ 8) :
    (m.write8 a1 v).read64 a2 = m.read64 a2 := by
  apply read64_eq_of_read8; intro i hi
  have ⟨hd1, hd2⟩ := offset_disjoint h1 h2 (by decide) hi
  exact read8_write8_disjoint m a1 (a2 + i) v hd1 hd2

theorem read64_write16_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h1 : (a2 - a1).toNat ≥ 2) (h2 : (a1 - a2).toNat ≥ 8) :
    (m.write16 a1 v).read64 a2 = m.read64 a2 := by
  apply read64_eq_of_read8; intro i hi
  have ⟨hd1, hd2⟩ := offset_disjoint h1 h2 (by decide) hi
  exact read8_write16_disjoint m a1 (a2 + i) v hd1 hd2

theorem read64_write32_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h1 : (a2 - a1).toNat ≥ 4) (h2 : (a1 - a2).toNat ≥ 8) :
    (m.write32 a1 v).read64 a2 = m.read64 a2 := by
  apply read64_eq_of_read8; intro i hi
  have ⟨hd1, hd2⟩ := offset_disjoint h1 h2 (by decide) hi
  exact read8_write32_disjoint m a1 (a2 + i) v hd1 hd2

theorem read64_write64_disjoint (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h1 : (a2 - a1).toNat ≥ 8) (h2 : (a1 - a2).toNat ≥ 8) :
    (m.write64 a1 v).read64 a2 = m.read64 a2 := by
  apply read64_eq_of_read8; intro i hi
  have ⟨hd1, hd2⟩ := offset_disjoint h1 h2 (by decide) hi
  exact read8_write64_disjoint m a1 (a2 + i) v hd1 hd2

/-! ### Constant-Offset Cross-Width Disjoint Read-Over-Write Lemmas (`_base_off_disjoint`, `_base_zero_off`, `_base_off_zero`) -/

@[simp]
theorem read8_write8_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 8)
    (h : decide ((off2 - off1).toNat ≥ 1 ∧ (off1 - off2).toNat ≥ 1) = true) :
    (m.write8 (base + off1) v).read8 (base + off2) = m.read8 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read8_write8_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read8_write8_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 8)
    (h : decide ((0#64 - off).toNat ≥ 1 ∧ (off - 0#64).toNat ≥ 1) = true) :
    (m.write8 (base + off) v).read8 base = m.read8 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read8_write8_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read8_write8_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 8)
    (h : decide ((off - 0#64).toNat ≥ 1 ∧ (0#64 - off).toNat ≥ 1) = true) :
    (m.write8 base v).read8 (base + off) = m.read8 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read8_write8_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read8_write16_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 16)
    (h : decide ((off2 - off1).toNat ≥ 2 ∧ (off1 - off2).toNat ≥ 1) = true) :
    (m.write16 (base + off1) v).read8 (base + off2) = m.read8 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read8_write16_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read8_write16_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 16)
    (h : decide ((0#64 - off).toNat ≥ 2 ∧ (off - 0#64).toNat ≥ 1) = true) :
    (m.write16 (base + off) v).read8 base = m.read8 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read8_write16_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read8_write16_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 16)
    (h : decide ((off - 0#64).toNat ≥ 2 ∧ (0#64 - off).toNat ≥ 1) = true) :
    (m.write16 base v).read8 (base + off) = m.read8 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read8_write16_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read8_write32_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 32)
    (h : decide ((off2 - off1).toNat ≥ 4 ∧ (off1 - off2).toNat ≥ 1) = true) :
    (m.write32 (base + off1) v).read8 (base + off2) = m.read8 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read8_write32_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read8_write32_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 32)
    (h : decide ((0#64 - off).toNat ≥ 4 ∧ (off - 0#64).toNat ≥ 1) = true) :
    (m.write32 (base + off) v).read8 base = m.read8 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read8_write32_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read8_write32_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 32)
    (h : decide ((off - 0#64).toNat ≥ 4 ∧ (0#64 - off).toNat ≥ 1) = true) :
    (m.write32 base v).read8 (base + off) = m.read8 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read8_write32_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read8_write64_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 64)
    (h : decide ((off2 - off1).toNat ≥ 8 ∧ (off1 - off2).toNat ≥ 1) = true) :
    (m.write64 (base + off1) v).read8 (base + off2) = m.read8 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read8_write64_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read8_write64_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide ((0#64 - off).toNat ≥ 8 ∧ (off - 0#64).toNat ≥ 1) = true) :
    (m.write64 (base + off) v).read8 base = m.read8 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read8_write64_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read8_write64_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide ((off - 0#64).toNat ≥ 8 ∧ (0#64 - off).toNat ≥ 1) = true) :
    (m.write64 base v).read8 (base + off) = m.read8 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read8_write64_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read16_write8_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 8)
    (h : decide ((off2 - off1).toNat ≥ 1 ∧ (off1 - off2).toNat ≥ 2) = true) :
    (m.write8 (base + off1) v).read16 (base + off2) = m.read16 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read16_write8_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read16_write8_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 8)
    (h : decide ((0#64 - off).toNat ≥ 1 ∧ (off - 0#64).toNat ≥ 2) = true) :
    (m.write8 (base + off) v).read16 base = m.read16 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read16_write8_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read16_write8_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 8)
    (h : decide ((off - 0#64).toNat ≥ 1 ∧ (0#64 - off).toNat ≥ 2) = true) :
    (m.write8 base v).read16 (base + off) = m.read16 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read16_write8_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read16_write16_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 16)
    (h : decide ((off2 - off1).toNat ≥ 2 ∧ (off1 - off2).toNat ≥ 2) = true) :
    (m.write16 (base + off1) v).read16 (base + off2) = m.read16 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read16_write16_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read16_write16_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 16)
    (h : decide ((0#64 - off).toNat ≥ 2 ∧ (off - 0#64).toNat ≥ 2) = true) :
    (m.write16 (base + off) v).read16 base = m.read16 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read16_write16_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read16_write16_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 16)
    (h : decide ((off - 0#64).toNat ≥ 2 ∧ (0#64 - off).toNat ≥ 2) = true) :
    (m.write16 base v).read16 (base + off) = m.read16 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read16_write16_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read16_write32_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 32)
    (h : decide ((off2 - off1).toNat ≥ 4 ∧ (off1 - off2).toNat ≥ 2) = true) :
    (m.write32 (base + off1) v).read16 (base + off2) = m.read16 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read16_write32_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read16_write32_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 32)
    (h : decide ((0#64 - off).toNat ≥ 4 ∧ (off - 0#64).toNat ≥ 2) = true) :
    (m.write32 (base + off) v).read16 base = m.read16 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read16_write32_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read16_write32_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 32)
    (h : decide ((off - 0#64).toNat ≥ 4 ∧ (0#64 - off).toNat ≥ 2) = true) :
    (m.write32 base v).read16 (base + off) = m.read16 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read16_write32_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read16_write64_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 64)
    (h : decide ((off2 - off1).toNat ≥ 8 ∧ (off1 - off2).toNat ≥ 2) = true) :
    (m.write64 (base + off1) v).read16 (base + off2) = m.read16 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read16_write64_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read16_write64_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide ((0#64 - off).toNat ≥ 8 ∧ (off - 0#64).toNat ≥ 2) = true) :
    (m.write64 (base + off) v).read16 base = m.read16 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read16_write64_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read16_write64_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide ((off - 0#64).toNat ≥ 8 ∧ (0#64 - off).toNat ≥ 2) = true) :
    (m.write64 base v).read16 (base + off) = m.read16 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read16_write64_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read32_write8_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 8)
    (h : decide ((off2 - off1).toNat ≥ 1 ∧ (off1 - off2).toNat ≥ 4) = true) :
    (m.write8 (base + off1) v).read32 (base + off2) = m.read32 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read32_write8_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read32_write8_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 8)
    (h : decide ((0#64 - off).toNat ≥ 1 ∧ (off - 0#64).toNat ≥ 4) = true) :
    (m.write8 (base + off) v).read32 base = m.read32 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read32_write8_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read32_write8_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 8)
    (h : decide ((off - 0#64).toNat ≥ 1 ∧ (0#64 - off).toNat ≥ 4) = true) :
    (m.write8 base v).read32 (base + off) = m.read32 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read32_write8_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read32_write16_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 16)
    (h : decide ((off2 - off1).toNat ≥ 2 ∧ (off1 - off2).toNat ≥ 4) = true) :
    (m.write16 (base + off1) v).read32 (base + off2) = m.read32 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read32_write16_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read32_write16_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 16)
    (h : decide ((0#64 - off).toNat ≥ 2 ∧ (off - 0#64).toNat ≥ 4) = true) :
    (m.write16 (base + off) v).read32 base = m.read32 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read32_write16_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read32_write16_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 16)
    (h : decide ((off - 0#64).toNat ≥ 2 ∧ (0#64 - off).toNat ≥ 4) = true) :
    (m.write16 base v).read32 (base + off) = m.read32 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read32_write16_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read32_write32_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 32)
    (h : decide ((off2 - off1).toNat ≥ 4 ∧ (off1 - off2).toNat ≥ 4) = true) :
    (m.write32 (base + off1) v).read32 (base + off2) = m.read32 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read32_write32_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read32_write32_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 32)
    (h : decide ((0#64 - off).toNat ≥ 4 ∧ (off - 0#64).toNat ≥ 4) = true) :
    (m.write32 (base + off) v).read32 base = m.read32 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read32_write32_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read32_write32_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 32)
    (h : decide ((off - 0#64).toNat ≥ 4 ∧ (0#64 - off).toNat ≥ 4) = true) :
    (m.write32 base v).read32 (base + off) = m.read32 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read32_write32_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read32_write64_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 64)
    (h : decide ((off2 - off1).toNat ≥ 8 ∧ (off1 - off2).toNat ≥ 4) = true) :
    (m.write64 (base + off1) v).read32 (base + off2) = m.read32 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read32_write64_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read32_write64_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide ((0#64 - off).toNat ≥ 8 ∧ (off - 0#64).toNat ≥ 4) = true) :
    (m.write64 (base + off) v).read32 base = m.read32 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read32_write64_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read32_write64_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide ((off - 0#64).toNat ≥ 8 ∧ (0#64 - off).toNat ≥ 4) = true) :
    (m.write64 base v).read32 (base + off) = m.read32 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read32_write64_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read64_write8_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 8)
    (h : decide ((off2 - off1).toNat ≥ 1 ∧ (off1 - off2).toNat ≥ 8) = true) :
    (m.write8 (base + off1) v).read64 (base + off2) = m.read64 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read64_write8_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read64_write8_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 8)
    (h : decide ((0#64 - off).toNat ≥ 1 ∧ (off - 0#64).toNat ≥ 8) = true) :
    (m.write8 (base + off) v).read64 base = m.read64 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read64_write8_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read64_write8_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 8)
    (h : decide ((off - 0#64).toNat ≥ 1 ∧ (0#64 - off).toNat ≥ 8) = true) :
    (m.write8 base v).read64 (base + off) = m.read64 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read64_write8_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read64_write16_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 16)
    (h : decide ((off2 - off1).toNat ≥ 2 ∧ (off1 - off2).toNat ≥ 8) = true) :
    (m.write16 (base + off1) v).read64 (base + off2) = m.read64 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read64_write16_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read64_write16_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 16)
    (h : decide ((0#64 - off).toNat ≥ 2 ∧ (off - 0#64).toNat ≥ 8) = true) :
    (m.write16 (base + off) v).read64 base = m.read64 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read64_write16_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read64_write16_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 16)
    (h : decide ((off - 0#64).toNat ≥ 2 ∧ (0#64 - off).toNat ≥ 8) = true) :
    (m.write16 base v).read64 (base + off) = m.read64 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read64_write16_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

@[simp]
theorem read64_write32_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 32)
    (h : decide ((off2 - off1).toNat ≥ 4 ∧ (off1 - off2).toNat ≥ 8) = true) :
    (m.write32 (base + off1) v).read64 (base + off2) = m.read64 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read64_write32_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read64_write32_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 32)
    (h : decide ((0#64 - off).toNat ≥ 4 ∧ (off - 0#64).toNat ≥ 8) = true) :
    (m.write32 (base + off) v).read64 base = m.read64 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read64_write32_disjoint m (base + off) base v
    (by rw [self_sub_add_left]; exact h1) (by rw [add_sub_self_left_zero]; exact h2)

@[simp]
theorem read64_write32_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 32)
    (h : decide ((off - 0#64).toNat ≥ 4 ∧ (0#64 - off).toNat ≥ 8) = true) :
    (m.write32 base v).read64 (base + off) = m.read64 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read64_write32_disjoint m base (base + off) v
    (by rw [add_sub_self_left_zero]; exact h1) (by rw [self_sub_add_left]; exact h2)

/-- Reading 64 bits at `base + off2` after writing 64 bits at `base + off1` when offsets are separated by at least 8 bytes. -/
theorem read64_write64_base_off_diff (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 64)
    (h1 : (off2 - off1).toNat ≥ 8) (h2 : (off1 - off2).toNat ≥ 8) :
    (m.write64 (base + off1) v).read64 (base + off2) = m.read64 (base + off2) := by
  exact read64_write64_disjoint m (base + off1) (base + off2) v
    (by rw [add_sub_add_left]; exact h1) (by rw [add_sub_add_left]; exact h2)

@[simp]
theorem read64_write64_base_zero_add8 (m : Memory) (base : BitVec 64) (v : BitVec 64) :
    (m.write64 (base + 8#64) v).read64 base = m.read64 base := by
  have h := read64_write64_base_off_diff m base 8#64 0#64 v (by decide) (by decide)
  simpa using h

@[simp]
theorem read64_write64_base_add8_zero (m : Memory) (base : BitVec 64) (v : BitVec 64) :
    (m.write64 base v).read64 (base + 8#64) = m.read64 (base + 8#64) := by
  have h := read64_write64_base_off_diff m base 0#64 8#64 v (by decide) (by decide)
  simpa using h

/-- General constant-offset 64-bit read-over-write simplification when `off1` and `off2` differ by at least 8 bytes. -/
@[simp]
theorem read64_write64_base_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (v : BitVec 64)
    (h : decide ((off2 - off1).toNat ≥ 8 ∧ (off1 - off2).toNat ≥ 8) = true) :
    (m.write64 (base + off1) v).read64 (base + off2) = m.read64 (base + off2) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  exact read64_write64_base_off_diff m base off1 off2 v h1 h2

@[simp]
theorem read64_write64_base_zero_off (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide ((0#64 - off).toNat ≥ 8 ∧ (off - 0#64).toNat ≥ 8) = true) :
    (m.write64 (base + off) v).read64 base = m.read64 base := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  have hdiff := read64_write64_base_off_diff m base off 0#64 v h1 h2
  simpa using hdiff

@[simp]
theorem read64_write64_base_off_zero (m : Memory) (base off : BitVec 64) (v : BitVec 64)
    (h : decide ((off - 0#64).toNat ≥ 8 ∧ (0#64 - off).toNat ≥ 8) = true) :
    (m.write64 base v).read64 (base + off) = m.read64 (base + off) := by
  have ⟨h1, h2⟩ := of_decide_eq_true h
  have hdiff := read64_write64_base_off_diff m base 0#64 off v h1 h2
  simpa using hdiff

/-! ### `DisjointRegions`, `Disjoint64`, and `Disjoint128` Read-Over-Write Lemmas -/

/-- Disjointness of two 8-byte (64-bit) memory regions `[a1, a1 + 8)` and `[a2, a2 + 8)`. -/
def Disjoint64 (a1 a2 : BitVec 64) : Prop :=
  (a2 - a1).toNat ≥ 8 ∧ (a1 - a2).toNat ≥ 8

/-- Disjointness of two 16-byte (128-bit) memory regions `[a1, a1 + 16)` and `[a2, a2 + 16)`. -/
def Disjoint128 (a1 a2 : BitVec 64) : Prop :=
  (a2 - a1).toNat ≥ 16 ∧ (a1 - a2).toNat ≥ 16

@[simp]
theorem read8_write8_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a1 1 a2 1) :
    (m.write8 a1 v).read8 a2 = m.read8 a2 :=
  read8_write8_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read8_write8_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a2 1 a1 1) :
    (m.write8 a1 v).read8 a2 = m.read8 a2 :=
  read8_write8_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read8_write16_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a1 2 a2 1) :
    (m.write16 a1 v).read8 a2 = m.read8 a2 :=
  read8_write16_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read8_write16_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a2 1 a1 2) :
    (m.write16 a1 v).read8 a2 = m.read8 a2 :=
  read8_write16_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read8_write32_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a1 4 a2 1) :
    (m.write32 a1 v).read8 a2 = m.read8 a2 :=
  read8_write32_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read8_write32_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a2 1 a1 4) :
    (m.write32 a1 v).read8 a2 = m.read8 a2 :=
  read8_write32_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read8_write64_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 8 a2 1) :
    (m.write64 a1 v).read8 a2 = m.read8 a2 :=
  read8_write64_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read8_write64_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 1 a1 8) :
    (m.write64 a1 v).read8 a2 = m.read8 a2 :=
  read8_write64_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read16_write8_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a1 1 a2 2) :
    (m.write8 a1 v).read16 a2 = m.read16 a2 :=
  read16_write8_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read16_write8_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a2 2 a1 1) :
    (m.write8 a1 v).read16 a2 = m.read16 a2 :=
  read16_write8_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read16_write16_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a1 2 a2 2) :
    (m.write16 a1 v).read16 a2 = m.read16 a2 :=
  read16_write16_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read16_write16_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a2 2 a1 2) :
    (m.write16 a1 v).read16 a2 = m.read16 a2 :=
  read16_write16_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read16_write32_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a1 4 a2 2) :
    (m.write32 a1 v).read16 a2 = m.read16 a2 :=
  read16_write32_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read16_write32_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a2 2 a1 4) :
    (m.write32 a1 v).read16 a2 = m.read16 a2 :=
  read16_write32_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read16_write64_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 8 a2 2) :
    (m.write64 a1 v).read16 a2 = m.read16 a2 :=
  read16_write64_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read16_write64_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 2 a1 8) :
    (m.write64 a1 v).read16 a2 = m.read16 a2 :=
  read16_write64_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read32_write8_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a1 1 a2 4) :
    (m.write8 a1 v).read32 a2 = m.read32 a2 :=
  read32_write8_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read32_write8_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a2 4 a1 1) :
    (m.write8 a1 v).read32 a2 = m.read32 a2 :=
  read32_write8_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read32_write16_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a1 2 a2 4) :
    (m.write16 a1 v).read32 a2 = m.read32 a2 :=
  read32_write16_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read32_write16_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a2 4 a1 2) :
    (m.write16 a1 v).read32 a2 = m.read32 a2 :=
  read32_write16_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read32_write32_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a1 4 a2 4) :
    (m.write32 a1 v).read32 a2 = m.read32 a2 :=
  read32_write32_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read32_write32_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a2 4 a1 4) :
    (m.write32 a1 v).read32 a2 = m.read32 a2 :=
  read32_write32_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read32_write64_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 8 a2 4) :
    (m.write64 a1 v).read32 a2 = m.read32 a2 :=
  read32_write64_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read32_write64_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 4 a1 8) :
    (m.write64 a1 v).read32 a2 = m.read32 a2 :=
  read32_write64_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read64_write8_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a1 1 a2 8) :
    (m.write8 a1 v).read64 a2 = m.read64 a2 :=
  read64_write8_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read64_write8_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a2 8 a1 1) :
    (m.write8 a1 v).read64 a2 = m.read64 a2 :=
  read64_write8_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read64_write16_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a1 2 a2 8) :
    (m.write16 a1 v).read64 a2 = m.read64 a2 :=
  read64_write16_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read64_write16_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a2 8 a1 2) :
    (m.write16 a1 v).read64 a2 = m.read64 a2 :=
  read64_write16_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read64_write32_of_disjointRegions_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a1 4 a2 8) :
    (m.write32 a1 v).read64 a2 = m.read64 a2 :=
  read64_write32_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read64_write32_of_disjointRegions_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a2 8 a1 4) :
    (m.write32 a1 v).read64 a2 = m.read64 a2 :=
  read64_write32_disjoint m a1 a2 v h.2 h.1

@[simp]
theorem read64_write64_of_disjoint64_left (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : Disjoint64 a1 a2) :
    (m.write64 a1 v).read64 a2 = m.read64 a2 :=
  read64_write64_disjoint m a1 a2 v h.1 h.2

@[simp]
theorem read64_write64_of_disjoint64_right (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : Disjoint64 a2 a1) :
    (m.write64 a1 v).read64 a2 = m.read64 a2 :=
  read64_write64_disjoint m a1 a2 v h.2 h.1

/-! ### 128-Bit Cross-Width `DisjointRegions` Lemmas (for unfolded `read128` / `write128`) -/

private theorem disjointRegions_add8_left {a1 a2 : BitVec 64} {r : Nat}
    (h : DisjointRegions a1 16 a2 r) (hr : r ≤ 8) :
    DisjointRegions (a1 + 8#64) 8 a2 r := by
  rcases h with ⟨h1, h2⟩
  exact ⟨by bv_arith, by bv_arith⟩

private theorem disjointRegions_add8_right {a1 a2 : BitVec 64} {w : Nat}
    (h : DisjointRegions a1 w a2 16) (hw : w ≤ 8) :
    DisjointRegions a1 w (a2 + 8#64) 8 := by
  rcases h with ⟨h1, h2⟩
  exact ⟨by bv_arith, by bv_arith⟩

@[simp]
theorem read8_write64_of_disjointRegions128_0_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 16 a2 1) :
    (m.write64 a1 v).read8 a2 = m.read8 a2 :=
  read8_write64_disjoint m a1 a2 v (Nat.le_trans (by decide) h.1) h.2

@[simp]
theorem read8_write64_of_disjointRegions128_0_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 1 a1 16) :
    (m.write64 a1 v).read8 a2 = m.read8 a2 :=
  read8_write64_disjoint m a1 a2 v (Nat.le_trans (by decide) h.2) h.1

@[simp]
theorem read8_write64_of_disjointRegions128_8_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 16 a2 1) :
    (m.write64 (a1 + 8#64) v).read8 a2 = m.read8 a2 :=
  read8_write64_of_disjointRegions_left m (a1 + 8#64) a2 v (disjointRegions_add8_left h (by decide))

@[simp]
theorem read8_write64_of_disjointRegions128_8_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 1 a1 16) :
    (m.write64 (a1 + 8#64) v).read8 a2 = m.read8 a2 :=
  read8_write64_of_disjointRegions_right m (a1 + 8#64) a2 v (disjointRegions_add8_right h (by decide))

@[simp]
theorem read16_write64_of_disjointRegions128_0_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 16 a2 2) :
    (m.write64 a1 v).read16 a2 = m.read16 a2 :=
  read16_write64_disjoint m a1 a2 v (Nat.le_trans (by decide) h.1) h.2

@[simp]
theorem read16_write64_of_disjointRegions128_0_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 2 a1 16) :
    (m.write64 a1 v).read16 a2 = m.read16 a2 :=
  read16_write64_disjoint m a1 a2 v (Nat.le_trans (by decide) h.2) h.1

@[simp]
theorem read16_write64_of_disjointRegions128_8_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 16 a2 2) :
    (m.write64 (a1 + 8#64) v).read16 a2 = m.read16 a2 :=
  read16_write64_of_disjointRegions_left m (a1 + 8#64) a2 v (disjointRegions_add8_left h (by decide))

@[simp]
theorem read16_write64_of_disjointRegions128_8_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 2 a1 16) :
    (m.write64 (a1 + 8#64) v).read16 a2 = m.read16 a2 :=
  read16_write64_of_disjointRegions_right m (a1 + 8#64) a2 v (disjointRegions_add8_right h (by decide))

@[simp]
theorem read32_write64_of_disjointRegions128_0_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 16 a2 4) :
    (m.write64 a1 v).read32 a2 = m.read32 a2 :=
  read32_write64_disjoint m a1 a2 v (Nat.le_trans (by decide) h.1) h.2

@[simp]
theorem read32_write64_of_disjointRegions128_0_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 4 a1 16) :
    (m.write64 a1 v).read32 a2 = m.read32 a2 :=
  read32_write64_disjoint m a1 a2 v (Nat.le_trans (by decide) h.2) h.1

@[simp]
theorem read32_write64_of_disjointRegions128_8_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 16 a2 4) :
    (m.write64 (a1 + 8#64) v).read32 a2 = m.read32 a2 :=
  read32_write64_of_disjointRegions_left m (a1 + 8#64) a2 v (disjointRegions_add8_left h (by decide))

@[simp]
theorem read32_write64_of_disjointRegions128_8_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 4 a1 16) :
    (m.write64 (a1 + 8#64) v).read32 a2 = m.read32 a2 :=
  read32_write64_of_disjointRegions_right m (a1 + 8#64) a2 v (disjointRegions_add8_right h (by decide))

@[simp]
theorem read64_write64_of_disjointRegions128_8_0_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 16 a2 8) :
    (m.write64 a1 v).read64 a2 = m.read64 a2 :=
  read64_write64_disjoint m a1 a2 v (Nat.le_trans (by decide) h.1) h.2

@[simp]
theorem read64_write64_of_disjointRegions128_8_0_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 8 a1 16) :
    (m.write64 a1 v).read64 a2 = m.read64 a2 :=
  read64_write64_disjoint m a1 a2 v (Nat.le_trans (by decide) h.2) h.1

@[simp]
theorem read64_write64_of_disjointRegions128_8_8_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 16 a2 8) :
    (m.write64 (a1 + 8#64) v).read64 a2 = m.read64 a2 :=
  read64_write64_of_disjoint64_left m (a1 + 8#64) a2 v (disjointRegions_add8_left h (by decide))

@[simp]
theorem read64_write64_of_disjointRegions128_8_8_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 8 a1 16) :
    (m.write64 (a1 + 8#64) v).read64 a2 = m.read64 a2 :=
  read64_write64_of_disjoint64_right m (a1 + 8#64) a2 v (disjointRegions_add8_right h (by decide))

@[simp]
theorem read64_write8_of_disjointRegions128_0_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a1 1 a2 16) :
    (m.write8 a1 v).read64 a2 = m.read64 a2 :=
  read64_write8_disjoint m a1 a2 v h.1 (Nat.le_trans (by decide) h.2)

@[simp]
theorem read64_write8_of_disjointRegions128_0_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a2 16 a1 1) :
    (m.write8 a1 v).read64 a2 = m.read64 a2 :=
  read64_write8_disjoint m a1 a2 v h.2 (Nat.le_trans (by decide) h.1)

@[simp]
theorem read64_write8_of_disjointRegions128_8_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a1 1 a2 16) :
    (m.write8 a1 v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) :=
  read64_write8_of_disjointRegions_left m a1 (a2 + 8#64) v (disjointRegions_add8_right h (by decide))

@[simp]
theorem read64_write8_of_disjointRegions128_8_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a2 16 a1 1) :
    (m.write8 a1 v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) :=
  read64_write8_of_disjointRegions_right m a1 (a2 + 8#64) v (disjointRegions_add8_left h (by decide))

@[simp]
theorem read64_write16_of_disjointRegions128_0_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a1 2 a2 16) :
    (m.write16 a1 v).read64 a2 = m.read64 a2 :=
  read64_write16_disjoint m a1 a2 v h.1 (Nat.le_trans (by decide) h.2)

@[simp]
theorem read64_write16_of_disjointRegions128_0_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a2 16 a1 2) :
    (m.write16 a1 v).read64 a2 = m.read64 a2 :=
  read64_write16_disjoint m a1 a2 v h.2 (Nat.le_trans (by decide) h.1)

@[simp]
theorem read64_write16_of_disjointRegions128_8_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a1 2 a2 16) :
    (m.write16 a1 v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) :=
  read64_write16_of_disjointRegions_left m a1 (a2 + 8#64) v (disjointRegions_add8_right h (by decide))

@[simp]
theorem read64_write16_of_disjointRegions128_8_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a2 16 a1 2) :
    (m.write16 a1 v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) :=
  read64_write16_of_disjointRegions_right m a1 (a2 + 8#64) v (disjointRegions_add8_left h (by decide))

@[simp]
theorem read64_write32_of_disjointRegions128_0_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a1 4 a2 16) :
    (m.write32 a1 v).read64 a2 = m.read64 a2 :=
  read64_write32_disjoint m a1 a2 v h.1 (Nat.le_trans (by decide) h.2)

@[simp]
theorem read64_write32_of_disjointRegions128_0_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a2 16 a1 4) :
    (m.write32 a1 v).read64 a2 = m.read64 a2 :=
  read64_write32_disjoint m a1 a2 v h.2 (Nat.le_trans (by decide) h.1)

@[simp]
theorem read64_write32_of_disjointRegions128_8_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a1 4 a2 16) :
    (m.write32 a1 v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) :=
  read64_write32_of_disjointRegions_left m a1 (a2 + 8#64) v (disjointRegions_add8_right h (by decide))

@[simp]
theorem read64_write32_of_disjointRegions128_8_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a2 16 a1 4) :
    (m.write32 a1 v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) :=
  read64_write32_of_disjointRegions_right m a1 (a2 + 8#64) v (disjointRegions_add8_left h (by decide))

@[simp]
theorem read64_write64_of_disjointRegions8_128_0_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 8 a2 16) :
    (m.write64 a1 v).read64 a2 = m.read64 a2 :=
  read64_write64_disjoint m a1 a2 v h.1 (Nat.le_trans (by decide) h.2)

@[simp]
theorem read64_write64_of_disjointRegions8_128_0_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 16 a1 8) :
    (m.write64 a1 v).read64 a2 = m.read64 a2 :=
  read64_write64_disjoint m a1 a2 v h.2 (Nat.le_trans (by decide) h.1)

@[simp]
theorem read64_write64_of_disjointRegions8_128_8_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 8 a2 16) :
    (m.write64 a1 v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) :=
  read64_write64_of_disjoint64_left m a1 (a2 + 8#64) v (disjointRegions_add8_right h (by decide))

@[simp]
theorem read64_write64_of_disjointRegions8_128_8_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 16 a1 8) :
    (m.write64 a1 v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) :=
  read64_write64_of_disjoint64_right m a1 (a2 + 8#64) v (disjointRegions_add8_left h (by decide))

theorem Disjoint128.disjoint64_0_0 {a1 a2 : BitVec 64} (h : Disjoint128 a1 a2) : Disjoint64 a1 a2 :=
  ⟨Nat.le_trans (by decide) h.1, Nat.le_trans (by decide) h.2⟩

theorem Disjoint128.disjoint64_8_0 {a1 a2 : BitVec 64} (h : Disjoint128 a1 a2) : Disjoint64 (a1 + 8#64) a2 :=
  disjointRegions_add8_left ⟨h.1, Nat.le_trans (by decide) h.2⟩ (by decide)

theorem Disjoint128.disjoint64_0_8 {a1 a2 : BitVec 64} (h : Disjoint128 a1 a2) : Disjoint64 a1 (a2 + 8#64) :=
  disjointRegions_add8_right ⟨Nat.le_trans (by decide) h.1, h.2⟩ (by decide)

theorem Disjoint128.disjoint64_8_8 {a1 a2 : BitVec 64} (h : Disjoint128 a1 a2) : Disjoint64 (a1 + 8#64) (a2 + 8#64) := by
  rcases h with ⟨h1, h2⟩
  constructor <;> bv_arith

@[simp]
theorem read64_write64_of_disjoint128_0_0_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64) (h : Disjoint128 a1 a2) :
    (m.write64 a1 v).read64 a2 = m.read64 a2 :=
  read64_write64_of_disjoint64_left m a1 a2 v h.disjoint64_0_0

@[simp]
theorem read64_write64_of_disjoint128_0_0_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64) (h : Disjoint128 a2 a1) :
    (m.write64 a1 v).read64 a2 = m.read64 a2 :=
  read64_write64_of_disjoint64_right m a1 a2 v h.disjoint64_0_0

@[simp]
theorem read64_write64_of_disjoint128_8_0_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64) (h : Disjoint128 a1 a2) :
    (m.write64 (a1 + 8#64) v).read64 a2 = m.read64 a2 :=
  read64_write64_of_disjoint64_left m (a1 + 8#64) a2 v h.disjoint64_8_0

@[simp]
theorem read64_write64_of_disjoint128_8_0_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64) (h : Disjoint128 a2 a1) :
    (m.write64 (a1 + 8#64) v).read64 a2 = m.read64 a2 :=
  read64_write64_of_disjoint64_right m (a1 + 8#64) a2 v h.disjoint64_0_8

@[simp]
theorem read64_write64_of_disjoint128_0_8_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64) (h : Disjoint128 a1 a2) :
    (m.write64 a1 v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) :=
  read64_write64_of_disjoint64_left m a1 (a2 + 8#64) v h.disjoint64_0_8

@[simp]
theorem read64_write64_of_disjoint128_0_8_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64) (h : Disjoint128 a2 a1) :
    (m.write64 a1 v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) :=
  read64_write64_of_disjoint64_right m a1 (a2 + 8#64) v h.disjoint64_8_0

@[simp]
theorem read64_write64_of_disjoint128_8_8_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64) (h : Disjoint128 a1 a2) :
    (m.write64 (a1 + 8#64) v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) :=
  read64_write64_of_disjoint64_left m (a1 + 8#64) (a2 + 8#64) v h.disjoint64_8_8

@[simp]
theorem read64_write64_of_disjoint128_8_8_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64) (h : Disjoint128 a2 a1) :
    (m.write64 (a1 + 8#64) v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) :=
  read64_write64_of_disjoint64_right m (a1 + 8#64) (a2 + 8#64) v h.disjoint64_8_8

end Memory

/-! ## Register File and Architectural State Simplification Lemmas -/

namespace RegFile

@[simp]
theorem read_write (rf : RegFile) (idx1 idx2 : BitVec 5) (val : BitVec 64) :
    (rf.write idx1 val).read idx2 = if idx2 = idx1 then val else rf.read idx2 := rfl

@[simp]
theorem read_write_same (rf : RegFile) (idx : BitVec 5) (val : BitVec 64) :
    (rf.write idx val).read idx = val := by
  simp [read, write]

end RegFile

namespace VRegFile

@[simp]
theorem read_write (vf : VRegFile) (idx1 idx2 : BitVec 5) (val : BitVec 128) :
    (vf.write idx1 val).read idx2 = if idx2 = idx1 then val else vf.read idx2 := rfl

@[simp]
theorem read_write_same (vf : VRegFile) (idx : BitVec 5) (val : BitVec 128) :
    (vf.write idx val).read idx = val := by
  simp [read, write]

end VRegFile

namespace State

@[simp]
theorem readReg64_xzr (s : State) : s.readReg64 .xzr = 0#64 := by
  cases s; rfl

@[simp]
theorem readReg64_sp (s : State) : s.readReg64 .sp = s.sp := by
  cases s; rfl

@[simp, arm64_norm]
theorem writeReg64_xzr (s : State) (v : BitVec 64) :
    s.writeReg64 .xzr v = s := by
  cases s; simp [State.writeReg64]

theorem writeReg64_sp (s : State) (v : BitVec 64) : s.writeReg64 .sp v = { s with sp := v } := by
  cases s; rfl

@[simp]
theorem readReg32_xzr (s : State) : s.readReg32 .xzr = 0#32 := by
  cases s; rfl

@[simp, arm64_norm]
theorem writeReg32_xzr (s : State) (v : BitVec 32) :
    s.writeReg32 .xzr v = s := by
  cases s; simp [State.writeReg32, State.writeReg64]

@[simp]
theorem pc_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).pc = s.pc := by
  cases s; cases r <;> rfl

@[simp]
theorem pc_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).pc = s.pc :=
  pc_writeReg64 s r (v.zeroExtend 64)

@[simp]
theorem pc_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).pc = s.pc := by
  cases w <;> exact pc_writeReg64 s r _

@[simp]
theorem pstate_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).pstate = s.pstate := by
  cases s; cases r <;> rfl

@[simp]
theorem pstate_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).pstate = s.pstate :=
  pstate_writeReg64 s r (v.zeroExtend 64)

@[simp]
theorem pstate_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).pstate = s.pstate := by
  cases w <;> exact pstate_writeReg64 s r _

@[simp]
theorem mem_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by
  cases s; cases r <;> rfl

@[simp]
theorem mem_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).mem = s.mem :=
  mem_writeReg64 s r (v.zeroExtend 64)

@[simp]
theorem mem_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).mem = s.mem := by
  cases w <;> exact mem_writeReg64 s r _

@[simp]
theorem status_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).status = s.status := by
  cases s; cases r <;> rfl

@[simp]
theorem status_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).status = s.status :=
  status_writeReg64 s r (v.zeroExtend 64)

@[simp]
theorem status_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).status = s.status := by
  cases w <;> exact status_writeReg64 s r _

@[simp]
theorem sp_writeReg64_gpr (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr idx) v).sp = s.sp := by
  cases s; rfl

@[simp]
theorem readReg64_advancePC (s : State) (r : Reg) :
    s.advancePC.readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[simp]
theorem readReg64_setPC (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[simp]
theorem readReg64_setPState (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[simp]
theorem readReg64_setMem (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[simp]
theorem readReg64_writeReg64 (s : State) (r1 r2 : Reg) (v : BitVec 64) :
    (s.writeReg64 r1 v).readReg64 r2 =
      if r1 = .xzr ∨ r2 = .xzr ∨ r1 = .gpr 31#5 ∨ r2 = .gpr 31#5 then s.readReg64 r2
      else if r2 = r1 then v
      else s.readReg64 r2 := by
  cases r1 with
  | xzr =>
    cases r2 <;> simp [readReg64]
  | sp =>
    cases r2 with
    | xzr => simp [readReg64]
    | sp => simp [writeReg64, readReg64]
    | gpr idx2 =>
      by_cases h2 : idx2 = 31#5 <;> simp [h2, writeReg64, readReg64]
  | gpr idx1 =>
    by_cases h1 : idx1 = 31#5
    · subst h1
      cases r2 <;> simp [writeReg64, readReg64]
    · cases r2 with
      | xzr => simp [h1, readReg64]
      | sp => simp [h1, writeReg64, readReg64]
      | gpr idx2 =>
        by_cases h2 : idx2 = 31#5
        · subst h2; simp [h1, readReg64]
        · by_cases heq : idx2 = idx1
          · subst heq; simp [h1, writeReg64, readReg64]
          · simp [h1, h2, heq, writeReg64, readReg64]

/-- Read-after-write of the same register (not `xzr`, not the `gpr 31` alias). -/
theorem readReg64_writeReg64_same (s : State) (r : Reg) (v : BitVec 64)
    (hzr : r ≠ .xzr) (h31 : r ≠ .gpr 31#5) :
    (s.writeReg64 r v).readReg64 r = v := by
  simp [readReg64_writeReg64, hzr, h31]

/-- Read-after-write of a different register: the write is invisible. -/
theorem readReg64_writeReg64_ne (s : State) (r1 r2 : Reg) (v : BitVec 64) (hne : r2 ≠ r1) :
    (s.writeReg64 r1 v).readReg64 r2 = s.readReg64 r2 := by
  simp [readReg64_writeReg64, hne]

/-! ### `fpsr` Projections & `setFpsr` / `orFpsr` Algebra -/

@[simp, arm64_norm, wp_norm]
theorem fpsr_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).fpsr = f := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem fpsr_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).fpsr = s.fpsr ||| f := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem orFpsr_zero (s : State) : s.orFpsr 0#32 = s := by
  cases s; simp [State.orFpsr]

@[simp, arm64_norm, wp_norm]
theorem orFpsr_orFpsr (s : State) (f1 f2 : BitVec 32) :
    (s.orFpsr f1).orFpsr f2 = s.orFpsr (f1 ||| f2) := by
  cases s; simp [State.orFpsr, BitVec.or_assoc]

@[simp, arm64_norm, wp_norm]
theorem setFpsr_orFpsr (s : State) (f1 f2 : BitVec 32) :
    (s.setFpsr f1).orFpsr f2 = s.setFpsr (f1 ||| f2) := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem setFpsr_setFpsr (s : State) (f1 f2 : BitVec 32) :
    (s.setFpsr f1).setFpsr f2 = s.setFpsr f2 := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem orFpsr_setFpsr (s : State) (f1 f2 : BitVec 32) :
    (s.orFpsr f1).setFpsr f2 = s.setFpsr f2 := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem pc_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).pc = s.pc := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem pc_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).pc = s.pc := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sp_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).sp = s.sp := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sp_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).sp = s.sp := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem pstate_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).pstate = s.pstate := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem pstate_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).pstate = s.pstate := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem mem_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).mem = s.mem := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem mem_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).mem = s.mem := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem status_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).status = s.status := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem status_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).status = s.status := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem readReg64_setFpsr (s : State) (f : BitVec 32) (r : Reg) :
    (s.setFpsr f).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem readReg64_orFpsr (s : State) (f : BitVec 32) (r : Reg) :
    (s.orFpsr f).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem readReg32_setFpsr (s : State) (f : BitVec 32) (r : Reg) :
    (s.setFpsr f).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem readReg32_orFpsr (s : State) (f : BitVec 32) (r : Reg) :
    (s.orFpsr f).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem readReg_setFpsr (s : State) (f : BitVec 32) (w : Width) (r : Reg) :
    (s.setFpsr f).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem readReg_orFpsr (s : State) (f : BitVec 32) (w : Width) (r : Reg) :
    (s.orFpsr f).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem readVReg128_setFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) :
    (s.setFpsr f).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem readVReg128_orFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) :
    (s.orFpsr f).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem readVReg64_setFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) :
    (s.setFpsr f).readVReg64 idx = s.readVReg64 idx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem readVReg64_orFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) :
    (s.orFpsr f).readVReg64 idx = s.readVReg64 idx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem readVReg32_setFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) :
    (s.setFpsr f).readVReg32 idx = s.readVReg32 idx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem readVReg32_orFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) :
    (s.orFpsr f).readVReg32 idx = s.readVReg32 idx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem tpidrEl0_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem tpidrEl0_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem brk_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).brk = s.brk := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem brk_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).brk = s.brk := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem brkStart_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).brkStart = s.brkStart := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem brkStart_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).brkStart = s.brkStart := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fs_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fs_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem oracle_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).oracle = s.oracle := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem oracle_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).oracle = s.oracle := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem oracleIdx_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem oracleIdx_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem trace_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).trace = s.trace := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem trace_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).trace = s.trace := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem fpsr_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).fpsr = s.fpsr := by
  cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem fpsr_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).fpsr = s.fpsr :=
  fpsr_writeReg64 s r (v.zeroExtend 64)
@[simp, arm64_norm, wp_norm]
theorem fpsr_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).fpsr = s.fpsr := by
  cases w <;> exact fpsr_writeReg64 s r _
@[simp, arm64_norm, wp_norm]
theorem fpsr_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) : (s.writeVReg128 idx v).fpsr = s.fpsr := by
  cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fpsr_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) : (s.writeVReg64 idx v).fpsr = s.fpsr :=
  fpsr_writeVReg128 s idx (v.zeroExtend 128)
@[simp, arm64_norm, wp_norm]
theorem fpsr_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) : (s.writeVReg32 idx v).fpsr = s.fpsr :=
  fpsr_writeVReg128 s idx (v.zeroExtend 128)
@[simp, arm64_norm, wp_norm]
theorem fpsr_advancePC (s : State) : s.advancePC.fpsr = s.fpsr := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fpsr_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).fpsr = s.fpsr := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fpsr_setPState (s : State) (ps : PState) : (s.setPState ps).fpsr = s.fpsr := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fpsr_setMem (s : State) (m : Memory) : (s.setMem m).fpsr = s.fpsr := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fpsr_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).fpsr = s.fpsr := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fpsr_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).fpsr = s.fpsr := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fpsr_setFs (s : State) (f : FsState) : (s.setFs f).fpsr = s.fpsr := by cases s; rfl
/-- Consume all leading `true` entries (spurious store-exclusive failures) and the succeeding
    decision (`false` or end-of-list) from `s.exclFails`, corresponding to the post-loop
    `exclFails` after an LL/SC retry loop succeeds. -/
def stepExclLoop (s : State) : State :=
  { s with exclFails := (s.exclFails.dropWhile (· == true)).tail }

@[simp, arm64_norm, wp_norm]
theorem fpsr_nextOracle (s : State) : s.nextOracle.fpsr = s.fpsr := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fpsr_stepExclOracle (s : State) : s.stepExclOracle.fpsr = s.fpsr := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fpsr_stepExclLoop (s : State) : s.stepExclLoop.fpsr = s.fpsr := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem symtab_stepExclLoop (s : State) : s.stepExclLoop.symtab = s.symtab := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sym_stepExclLoop (s : State) (o n : String) : s.stepExclLoop.sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_stepExclLoop]
@[simp, arm64_norm, wp_norm]
theorem fpsr_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).fpsr = s.fpsr := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem regs_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).regs = s.regs := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem vregs_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).vregs = s.vregs := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem readReg64_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) (r : Reg) :
    (s.setSigAction sig act).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem readReg32_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) (r : Reg) :
    (s.setSigAction sig act).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem readReg_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) (w : Width) (r : Reg) :
    (s.setSigAction sig act).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem readVReg128_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) (idx : BitVec 5) :
    (s.setSigAction sig act).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem readVReg64_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) (idx : BitVec 5) :
    (s.setSigAction sig act).readVReg64 idx = s.readVReg64 idx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem readVReg32_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) (idx : BitVec 5) :
    (s.setSigAction sig act).readVReg32 idx = s.readVReg32 idx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sp_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).sp = s.sp := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem spAligned_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).spAligned = s.spAligned := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem pc_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).pc = s.pc := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem pstate_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).pstate = s.pstate := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem mem_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).mem = s.mem := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem tpidrEl0_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fpsr_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).fpsr = s.fpsr := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem brkStart_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).brkStart = s.brkStart := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem brk_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).brk = s.brk := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fs_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem oracle_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).oracle = s.oracle := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem oracleIdx_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem exclFails_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem exclWillFail_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).exclWillFail = s.exclWillFail := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem trace_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).trace = s.trace := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem status_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).status = s.status := by cases s; rfl
attribute [wp_norm] State.symtab_setSigAction State.sym_setSigAction

@[simp, arm64_norm, wp_norm]
theorem getSigAction_setSigAction (s : State) (sig sig' : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).getSigAction sig' =
      if sig' = sig then act else s.getSigAction sig' := by
  cases s; unfold State.setSigAction State.getSigAction
  by_cases h : sig' = sig <;> simp [h]

@[simp, arm64_norm, wp_norm]
theorem sigActions_setSigAction (s : State) (sig sig' : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).sigActions sig' =
      if sig' = sig then act else s.sigActions sig' := by
  cases s; unfold State.setSigAction
  by_cases h : sig' = sig <;> simp [h]

@[simp, arm64_norm, wp_norm]
theorem setSigAction_setSigAction_same (s : State) (sig : BitVec 32) (a1 a2 : SigAction) :
    (s.setSigAction sig a1).setSigAction sig a2 = s.setSigAction sig a2 := by
  cases s; unfold State.setSigAction; congr; funext k
  by_cases h : k = sig <;> simp [h]

@[simp, arm64_norm, wp_norm]
theorem getSigAction_writeReg64 (s : State) (r : Reg) (v : BitVec 64) (sig : BitVec 32) :
    (s.writeReg64 r v).getSigAction sig = s.getSigAction sig := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_writeReg32 (s : State) (r : Reg) (v : BitVec 32) (sig : BitVec 32) :
    (s.writeReg32 r v).getSigAction sig = s.getSigAction sig :=
  getSigAction_writeReg64 s r (v.zeroExtend 64) sig
@[simp, arm64_norm, wp_norm]
theorem getSigAction_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) (sig : BitVec 32) :
    (s.writeReg w r v).getSigAction sig = s.getSigAction sig := by
  cases w <;> exact getSigAction_writeReg64 s r _ sig
@[simp, arm64_norm, wp_norm]
theorem getSigAction_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) (sig : BitVec 32) :
    (s.writeVReg128 idx v).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) (sig : BitVec 32) :
    (s.writeVReg64 idx v).getSigAction sig = s.getSigAction sig :=
  getSigAction_writeVReg128 s idx (v.zeroExtend 128) sig
@[simp, arm64_norm, wp_norm]
theorem getSigAction_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) (sig : BitVec 32) :
    (s.writeVReg32 idx v).getSigAction sig = s.getSigAction sig :=
  getSigAction_writeVReg128 s idx (v.zeroExtend 128) sig
@[simp, arm64_norm, wp_norm]
theorem getSigAction_advancePC (s : State) (sig : BitVec 32) :
    s.advancePC.getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_setPC (s : State) (pc : BitVec 64) (sig : BitVec 32) :
    (s.setPC pc).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_setPState (s : State) (ps : PState) (sig : BitVec 32) :
    (s.setPState ps).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_setMem (s : State) (m : Memory) (sig : BitVec 32) :
    (s.setMem m).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_setStatus (s : State) (st : ExecStatus) (sig : BitVec 32) :
    (s.setStatus st).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_setBrk (s : State) (b : BitVec 64) (sig : BitVec 32) :
    (s.setBrk b).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_setFs (s : State) (f : FsState) (sig : BitVec 32) :
    (s.setFs f).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_setFpsr (s : State) (f : BitVec 32) (sig : BitVec 32) :
    (s.setFpsr f).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_orFpsr (s : State) (f : BitVec 32) (sig : BitVec 32) :
    (s.orFpsr f).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_nextOracle (s : State) (sig : BitVec 32) :
    s.nextOracle.getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_stepExclOracle (s : State) (sig : BitVec 32) :
    s.stepExclOracle.getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_stepExclLoop (s : State) (sig : BitVec 32) :
    s.stepExclLoop.getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_appendTrace (s : State) (evs : List TraceEvent) (sig : BitVec 32) :
    (s.appendTrace evs).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem getSigAction_setSigAltStack (s : State) (sas : SigAltStack) (sig : BitVec 32) :
    (s.setSigAltStack sas).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem regs_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).regs = s.regs := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem vregs_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).vregs = s.vregs := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem readReg64_setSigAltStack (s : State) (sas : SigAltStack) (r : Reg) :
    (s.setSigAltStack sas).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem readReg32_setSigAltStack (s : State) (sas : SigAltStack) (r : Reg) :
    (s.setSigAltStack sas).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem readReg_setSigAltStack (s : State) (sas : SigAltStack) (w : Width) (r : Reg) :
    (s.setSigAltStack sas).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem readVReg128_setSigAltStack (s : State) (sas : SigAltStack) (idx : BitVec 5) :
    (s.setSigAltStack sas).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem readVReg64_setSigAltStack (s : State) (sas : SigAltStack) (idx : BitVec 5) :
    (s.setSigAltStack sas).readVReg64 idx = s.readVReg64 idx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem readVReg32_setSigAltStack (s : State) (sas : SigAltStack) (idx : BitVec 5) :
    (s.setSigAltStack sas).readVReg32 idx = s.readVReg32 idx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sp_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).sp = s.sp := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem spAligned_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).spAligned = s.spAligned := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem pc_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).pc = s.pc := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem pstate_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).pstate = s.pstate := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem mem_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).mem = s.mem := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem tpidrEl0_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fpsr_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).fpsr = s.fpsr := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem brkStart_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).brkStart = s.brkStart := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem brk_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).brk = s.brk := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem fs_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem oracle_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).oracle = s.oracle := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem oracleIdx_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem exclFails_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem exclWillFail_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).exclWillFail = s.exclWillFail := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem trace_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).trace = s.trace := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem status_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).status = s.status := by cases s; rfl
attribute [wp_norm] State.symtab_setSigAltStack State.sym_setSigAltStack

@[simp, arm64_norm, wp_norm]
theorem sigAltStack_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).sigAltStack = sas := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem setSigAltStack_setSigAltStack (s : State) (sas1 sas2 : SigAltStack) :
    (s.setSigAltStack sas1).setSigAltStack sas2 = s.setSigAltStack sas2 := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem sigAltStack_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).sigAltStack = s.sigAltStack := by cases s; rfl

end State

/-! ## Small-Step Operational Semantics Lemmas -/

namespace Steps


theorem trans {prog : Program} {s1 s2 s3 : State}
    (h1 : Steps prog s1 s2) (h2 : Steps prog s2 s3) : Steps prog s1 s3 := by
  induction h1 with
  | refl _ => exact h2
  | step hs _ ih => exact Steps.step hs (ih h2)

end Steps


/-- Every `Step` requires the source state to be `.Running`. -/
theorem Step.status_running {prog : Program} {s s' : State}
    (h : Step prog s s') : s.status = .Running := by
  cases h <;> assumption

/-- The small-step transition relation `Step` is deterministic. -/
theorem Step.deterministic {prog : Program} {s s1 s2 : State}
    (h1 : Step prog s s1) (h2 : Step prog s s2) : s1 = s2 := by
  cases h1 with
  | exec _ hf1 =>
    cases h2 with
    | exec _ hf2 =>
      rw [hf1] at hf2
      injection hf2 with hinst
      subst hinst
      rfl
    | halt_unmapped _ hf2 _ =>
      rw [hf1] at hf2
      contradiction
    | extern _ he2 _ =>
      rw [Program.fetchMem_eq_none_of_externs he2] at hf1
      contradiction
    | extern_fault _ he2 _ =>
      rw [Program.fetchMem_eq_none_of_externs he2] at hf1
      contradiction
  | halt_unmapped _ hf1 he1 =>
    cases h2 with
    | exec _ hf2 =>
      rw [hf1] at hf2
      contradiction
    | halt_unmapped _ _ _ =>
      rfl
    | extern _ he2 _ =>
      rw [he1] at he2
      contradiction
    | extern_fault _ he2 _ =>
      rw [he1] at he2
      contradiction
  | extern _ he1 hk1 hsym1 =>
    cases h2 with
    | exec _ hf2 =>
      rw [Program.fetchMem_eq_none_of_externs he1] at hf2
      contradiction
    | halt_unmapped _ _ he2 =>
      rw [he1] at he2
      contradiction
    | extern _ he2 _ _ =>
      rw [he1] at he2
      injection he2 with hf
      subst hf
      rfl
    | extern_fault _ he2 hk2 =>
      rw [he1] at he2
      injection he2 with hf
      subst hf
      exact absurd ⟨hk1, hsym1⟩ hk2
  | extern_fault _ he1 hk1 =>
    cases h2 with
    | exec _ hf2 =>
      rw [Program.fetchMem_eq_none_of_externs he1] at hf2
      contradiction
    | halt_unmapped _ _ he2 =>
      rw [he1] at he2
      contradiction
    | extern _ he2 hk2 hsym2 =>
      rw [he1] at he2
      injection he2 with hf
      subst hf
      exact absurd ⟨hk2, hsym2⟩ hk1
    | extern_fault _ _ _ =>
      rfl

namespace StepsUntil

/-- Every `StepsUntil` execution is a valid `Steps` execution. -/
theorem toSteps {prog : Program} {stop : State → Prop} {s1 s2 : State}
    (h : StepsUntil prog stop s1 s2) : Steps prog s1 s2 := by
  induction h with
  | refl s => exact Steps.refl s
  | step _ hstep _ ih => exact Steps.step hstep ih

/-- Any two executions from `s0` that stop at the first state satisfying `stop` reach the exact same state. -/
theorem deterministic {prog : Program} {stop : State → Prop} {s0 s1 s2 : State}
    (h1 : StepsUntil prog stop s0 s1) (hstop1 : stop s1)
    (h2 : StepsUntil prog stop s0 s2) (hstop2 : stop s2) :
    s1 = s2 := by
  induction h1 with
  | refl s =>
    cases h2 with
    | refl _ => rfl
    | step hne _ _ => exact False.elim (hne hstop1)
  | step hne1 hstep1 _ ih =>
    cases h2 with
    | refl _ => exact False.elim (hne1 hstop2)
    | step _ hstep2 hrest2 =>
      cases Step.deterministic hstep1 hstep2
      exact ih hstop1 hrest2

end StepsUntil

/-- Reflexive-transitive execution of `prog` that stops as soon as `pc = target_pc`:
    no intermediate state prior to the final state has `pc = target_pc`. -/
abbrev StepsUntilPC (prog : Program) (target_pc : BitVec 64) : State → State → Prop :=
  StepsUntil prog (fun s => s.pc = target_pc)

namespace StepsUntilPC

/-- Every `StepsUntilPC` execution is a valid `Steps` execution. -/
abbrev toSteps {prog : Program} {target_pc : BitVec 64} {s1 s2 : State}
    (h : StepsUntilPC prog target_pc s1 s2) : Steps prog s1 s2 :=
  StepsUntil.toSteps h

/-- Any two executions from `s0` that stop at the first visit to `target_pc` reach the exact same state. -/
abbrev deterministic {prog : Program} {target_pc : BitVec 64} {s0 s1 s2 : State}
    (h1 : StepsUntilPC prog target_pc s0 s1) (hpc1 : s1.pc = target_pc)
    (h2 : StepsUntilPC prog target_pc s0 s2) (hpc2 : s2.pc = target_pc) :
    s1 = s2 :=
  StepsUntil.deterministic h1 hpc1 h2 hpc2

end StepsUntilPC

/-- Any multi-step execution `Steps prog s0 sf` reaching `stop sf` factors through
    a first stopping state `sm` (`StepsUntil prog stop s0 sm ∧ stop sm ∧ Steps prog sm sf`). -/
theorem Steps.toStepsUntil {prog : Program} {stop : State → Prop} {s0 sf : State}
    (h : Steps prog s0 sf) (hstop : stop sf) :
    ∃ sm, StepsUntil prog stop s0 sm ∧ stop sm ∧ Steps prog sm sf := by
  induction h with
  | refl s =>
    exact ⟨s, StepsUntil.refl s, hstop, Steps.refl s⟩
  | @step s1 s2 s3 h1 h2 ih =>
    by_cases h1_stop : stop s1
    · exact ⟨s1, StepsUntil.refl s1, h1_stop, Steps.step h1 h2⟩
    · rcases ih hstop with ⟨sm, h_until, hsm_stop, h_rest⟩
      exact ⟨sm, StepsUntil.step h1_stop h1 h_until, hsm_stop, h_rest⟩

/-- Any multi-step execution `Steps prog s0 sf` reaching `sf.pc = target_pc` factors through
    a first visit `sm` (`StepsUntilPC prog target_pc s0 sm ∧ sm.pc = target_pc ∧ Steps prog sm sf`). -/
theorem Steps.toStepsUntilPC {prog : Program} {target_pc : BitVec 64} {s0 sf : State}
    (h : Steps prog s0 sf) (hpc : sf.pc = target_pc) :
    ∃ sm, StepsUntilPC prog target_pc s0 sm ∧ sm.pc = target_pc ∧ Steps prog sm sf :=
  h.toStepsUntil hpc

/-! ## Stack Preservation, Calling Convention, and Hoare Logic Lemmas -/

namespace StackPreserved

@[simp]
theorem rfl {m : Memory} {sp0 : BitVec 64} {len : Nat} :
    StackPreserved m m sp0 len :=
  fun _ _ => Eq.refl _

@[simp]
theorem refl_iff (m : Memory) (sp0 : BitVec 64) (len : Nat) :
    StackPreserved m m sp0 len ↔ True :=
  ⟨fun _ => trivial, fun _ => rfl⟩

theorem trans {m0 m1 m2 : Memory} {sp0 : BitVec 64} {len : Nat}
    (h01 : StackPreserved m0 m1 sp0 len)
    (h12 : StackPreserved m1 m2 sp0 len) :
    StackPreserved m0 m2 sp0 len :=
  fun a ha => (h12 a ha).trans (h01 a ha)


theorem write8 {m0 m : Memory} {sp0 addr : BitVec 64} {len : Nat} {val : BitVec 8}
    (h_disj : DisjointRegions addr 1 sp0 len)
    (h_prev : StackPreserved m0 m sp0 len) :
    StackPreserved m0 (m.write8 addr val) sp0 len := by
  intro a ha
  have h1 := h_disj.1
  have h2 := h_disj.2
  simp only [InRegion] at ha
  have hne : a ≠ addr := by bv_arith
  simp only [Memory.read8_write8, hne, ↓reduceIte]
  exact h_prev a ha

theorem write16 {m0 m : Memory} {sp0 addr : BitVec 64} {len : Nat} {val : BitVec 16}
    (h_disj : DisjointRegions addr 2 sp0 len)
    (h_prev : StackPreserved m0 m sp0 len) :
    StackPreserved m0 (m.write16 addr val) sp0 len := by
  intro a ha
  have h1 := h_disj.1
  have h2 := h_disj.2
  simp only [InRegion] at ha
  have hne : ∀ j : BitVec 64, j.toNat < 2 → a ≠ addr + j := by
    intro j hj; bv_arith
  have h_ite : ∀ {α : Type} {c : Prop} [Decidable c] (t e : α), ¬c → (if c then t else e) = e :=
    fun _ _ hc => ite_eq_right_iff.mpr (fun h => False.elim (hc h))
  simp only [Memory.write16, Memory.read8_write8]
  repeat' (rw [h_ite _ _ (hne _ (by decide))])
  exact h_prev a ha

theorem write32 {m0 m : Memory} {sp0 addr : BitVec 64} {len : Nat} {val : BitVec 32}
    (h_disj : DisjointRegions addr 4 sp0 len)
    (h_prev : StackPreserved m0 m sp0 len) :
    StackPreserved m0 (m.write32 addr val) sp0 len := by
  intro a ha
  have h1 := h_disj.1
  have h2 := h_disj.2
  simp only [InRegion] at ha
  have hne : ∀ j : BitVec 64, j.toNat < 4 → a ≠ addr + j := by
    intro j hj; bv_arith
  have h_ite : ∀ {α : Type} {c : Prop} [Decidable c] (t e : α), ¬c → (if c then t else e) = e :=
    fun _ _ hc => ite_eq_right_iff.mpr (fun h => False.elim (hc h))
  simp only [Memory.write32, Memory.read8_write8]
  repeat' (rw [h_ite _ _ (hne _ (by decide))])
  exact h_prev a ha

theorem write64 {m0 m : Memory} {sp0 addr : BitVec 64} {len : Nat} {val : BitVec 64}
    (h_disj : DisjointRegions addr 8 sp0 len)
    (h_prev : StackPreserved m0 m sp0 len) :
    StackPreserved m0 (m.write64 addr val) sp0 len := by
  intro a ha
  have h1 := h_disj.1
  have h2 := h_disj.2
  simp only [InRegion] at ha
  have hne : ∀ j : BitVec 64, j.toNat < 8 → a ≠ addr + j := by
    intro j hj; bv_arith
  have h_ite : ∀ {α : Type} {c : Prop} [Decidable c] (t e : α), ¬c → (if c then t else e) = e :=
    fun _ _ hc => ite_eq_right_iff.mpr (fun h => False.elim (hc h))
  simp only [Memory.write64, Memory.read8_write8]
  repeat' (rw [h_ite _ _ (hne _ (by decide))])
  exact h_prev a ha

theorem write128 {m0 m : Memory} {sp0 addr : BitVec 64} {len : Nat} {val : BitVec 128}
    (h_disj : DisjointRegions addr 16 sp0 len)
    (h_prev : StackPreserved m0 m sp0 len) :
    StackPreserved m0 (m.write128 addr val) sp0 len := by
  have h1 := h_disj.1
  have h2 := h_disj.2
  have hd_lo : DisjointRegions addr 8 sp0 len := ⟨by omega, h2⟩
  have hd_hi : DisjointRegions (addr + 8#64) 8 sp0 len := by
    simp only [DisjointRegions]
    bv_arith
  exact write64 hd_hi (write64 hd_lo h_prev)




end StackPreserved

theorem sub_add_left_cancel (a b : BitVec 64) : a - (a + b) = -b := by
  bv_arith

theorem sub_add_add_left_cancel (a b c : BitVec 64) : a - (a + b + c) = -(b + c) := by
  bv_arith

theorem sub_sub_left_cancel (a b : BitVec 64) : a - (a - b) = b := by
  bv_arith

theorem sub_sub_add_left_cancel (a b c : BitVec 64) : a - (a - b + c) = b - c := by
  bv_arith

@[simp]
theorem bitvec_add_zero {n : Nat} (x : BitVec n) : x + 0#n = x :=
  BitVec.add_zero x

theorem bitvec_add_sub_assoc (x y z : BitVec 64) : (x + y) - z = x + (y - z) := by
  bv_arith

/-- Any `width`-byte write inside the downward stack frame `[sp0 - stack_bound, sp0)` is disjoint
    from the caller's parent stack `[sp0, sp0 + parent_len)` whenever `parent_len + stack_bound ≤ 2^64`. -/
theorem DisjointRegions.of_stack_frame_bv {sp0 addr : BitVec 64} {width stack_bound parent_len : Nat}
    (h_bound : parent_len + stack_bound ≤ 2 ^ 64)
    (h_sub : decide (0 < width ∧ width ≤ stack_bound ∧ stack_bound < 2 ^ 64) = true)
    (h_in : (BitVec.ule (BitVec.ofNat 64 width) (sp0 - addr) &&
             BitVec.ule (sp0 - addr) (BitVec.ofNat 64 stack_bound)) = true) :
    DisjointRegions addr width sp0 parent_len := by
  have ⟨hw0, hw, hsb⟩ := of_decide_eq_true h_sub
  rcases Bool.and_eq_true_iff.mp h_in with ⟨h_lo, h_hi⟩
  have h1 : width ≤ (sp0 - addr).toNat := by
    have h_lo' : (BitVec.ofNat 64 width).toNat ≤ (sp0 - addr).toNat := by
      simpa [BitVec.ule] using h_lo
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h_lo'
    exact h_lo'
  have h2 : (sp0 - addr).toNat ≤ stack_bound := by
    have h_hi' : (sp0 - addr).toNat ≤ (BitVec.ofNat 64 stack_bound).toNat := by
      simpa [BitVec.ule] using h_hi
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsb] at h_hi'
    exact h_hi'
  simp only [DisjointRegions]
  bv_arith

namespace CalleeSavedVRegsPreserved

@[simp]
theorem rfl (s : State) : CalleeSavedVRegsPreserved s s := by
  cases s; rfl

theorem trans {s0 s1 s2 : State}
    (h01 : CalleeSavedVRegsPreserved s0 s1)
    (h12 : CalleeSavedVRegsPreserved s1 s2) :
    CalleeSavedVRegsPreserved s0 s2 :=
  Eq.trans h12 h01

end CalleeSavedVRegsPreserved

/-- Whether SIMD register index `v` (`V0..V31`) is AAPCS64 callee-saved (`V8..V15`).
    Defined via boolean equality (`==`) so `arm64_norm` and kernel reduction evaluate
    `cond (isCalleeSavedVReg 0#5) ... (calleeSavedVRegs s)` directly to `calleeSavedVRegs s`
    without expanding the `true` branch. -/
@[simp, arm64_norm, wp_norm]
def isCalleeSavedVReg (v : BitVec 5) : Bool :=
  (v == 8#5) || (v == 9#5) || (v == 10#5) || (v == 11#5) ||
  (v == 12#5) || (v == 13#5) || (v == 14#5) || (v == 15#5)

@[arm64_norm, wp_norm]
theorem arm64_cond_false {α : Type _} (a b : α) : (bif false then a else b) = b := rfl

@[arm64_norm, wp_norm]
theorem arm64_cond_true {α : Type _} (a b : α) : (bif true then a else b) = a := rfl

private theorem ne_of_isCalleeSavedVReg_false {v : BitVec 5}
    (hv : isCalleeSavedVReg v = false) (i : BitVec 5) (hi : isCalleeSavedVReg i = true) :
    i ≠ v := by
  intro heq; subst heq; rw [hv] at hi; exact Bool.false_ne_true hi

theorem CalleeSavedVRegsPreserved.readVReg64 {s0 sf : State}
    (h : CalleeSavedVRegsPreserved s0 sf) (idx : BitVec 5)
    (hidx : isCalleeSavedVReg idx = true) :
    sf.readVReg64 idx = s0.readVReg64 idx := by
  simp only [CalleeSavedVRegsPreserved, calleeSavedVRegs, VRegFile.calleeSaved, Prod.mk.injEq] at h
  rcases h with ⟨h8, h9, h10, h11, h12, h13, h14, h15⟩
  if hc8 : idx = 8#5 then subst hc8; exact h8
  else if hc9 : idx = 9#5 then subst hc9; exact h9
  else if hc10 : idx = 10#5 then subst hc10; exact h10
  else if hc11 : idx = 11#5 then subst hc11; exact h11
  else if hc12 : idx = 12#5 then subst hc12; exact h12

  else if hc13 : idx = 13#5 then subst hc13; exact h13
  else if hc14 : idx = 14#5 then subst hc14; exact h14
  else if hc15 : idx = 15#5 then subst hc15; exact h15
  else exact absurd hidx (by revert hc8 hc9 hc10 hc11 hc12 hc13 hc14 hc15 idx; decide)

@[simp, arm64_norm, wp_norm]
theorem BitVec.truncate64_zeroExtend128 (x : BitVec 64) :
    BitVec.truncate 64 (BitVec.zeroExtend 128 x) = x := by
  ext i hi; simp

@[simp, arm64_norm, wp_norm]
theorem BitVec.extractLsb'_0_64_eq_truncate (v : BitVec 128) :
    BitVec.extractLsb' 0 64 v = BitVec.truncate 64 v := by
  ext i hi; simp

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_advancePC (s : State) :
    calleeSavedVRegs s.advancePC = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_setPC (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_setMem (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_setPState (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_writeReg64 (s : State) (r : Reg) (val : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r val) = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_writeReg32 (s : State) (r : Reg) (val : BitVec 32) :
    calleeSavedVRegs (s.writeReg32 r val) = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_writeReg (s : State) (w : Width) (r : Reg) (val : BitVec 64) :
    calleeSavedVRegs (s.writeReg w r val) = calleeSavedVRegs s := by
  cases s; rfl

theorem calleeSavedVRegs_writeVReg128 (s : State) (v : BitVec 5) (val : BitVec 128)
    (h : isCalleeSavedVReg v = false := by decide) :
    calleeSavedVRegs (s.writeVReg128 v val) = calleeSavedVRegs s := by
  have hne : ∀ i : BitVec 5, isCalleeSavedVReg i = true →
      ((s.writeVReg128 v val).vregs.read i).truncate 64 = (s.vregs.read i).truncate 64 :=
    fun i hi => by
      simp [State.writeVReg128, VRegFile.read, VRegFile.write, ne_of_isCalleeSavedVReg_false h i hi]
  unfold calleeSavedVRegs VRegFile.calleeSaved
  rw [hne 8#5 (by decide), hne 9#5 (by decide), hne 10#5 (by decide), hne 11#5 (by decide),
      hne 12#5 (by decide), hne 13#5 (by decide), hne 14#5 (by decide), hne 15#5 (by decide)]

theorem calleeSavedVRegs_writeVReg64 (s : State) (v : BitVec 5) (val : BitVec 64)
    (h : isCalleeSavedVReg v = false := by decide) :
    calleeSavedVRegs (s.writeVReg64 v val) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s v (val.zeroExtend 128) h

theorem calleeSavedVRegs_writeVReg32 (s : State) (v : BitVec 5) (val : BitVec 32)
    (h : isCalleeSavedVReg v = false := by decide) :
    calleeSavedVRegs (s.writeVReg32 v val) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s v (val.zeroExtend 128) h

/-- Update lane `v` of an 8-lane callee-saved SIMD snapshot tuple (`D8..D15`). -/
@[simp, arm64_norm, wp_norm]
def updateCalleeSavedVRegs (v : BitVec 5) (val : BitVec 64)
    (r : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  (cond (v == 8#5) val r.1,
   cond (v == 9#5) val r.2.1,
   cond (v == 10#5) val r.2.2.1,
   cond (v == 11#5) val r.2.2.2.1,
   cond (v == 12#5) val r.2.2.2.2.1,
   cond (v == 13#5) val r.2.2.2.2.2.1,
   cond (v == 14#5) val r.2.2.2.2.2.2.1,
   cond (v == 15#5) val r.2.2.2.2.2.2.2)

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_writeVReg128_ite (s : State) (v : BitVec 5) (val : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 v val) =
      cond (isCalleeSavedVReg v)
        (updateCalleeSavedVRegs v (val.truncate 64) (calleeSavedVRegs s))
        (calleeSavedVRegs s) := by
  by_cases h : isCalleeSavedVReg v = true
  · simp only [h, Bool.cond_true, calleeSavedVRegs, VRegFile.calleeSaved, updateCalleeSavedVRegs]
    have hlane : ∀ i : BitVec 5,
        ((s.writeVReg128 v val).vregs.read i).truncate 64 =
          cond (v == i) (val.truncate 64) ((s.vregs.read i).truncate 64) := fun i => by
      by_cases hi : v = i
      · subst hi; simp [State.writeVReg128, VRegFile.read, VRegFile.write]
      · have hvi : i ≠ v := fun h' => hi h'.symm
        simp [State.writeVReg128, VRegFile.read, VRegFile.write, hi, hvi]
    rw [hlane 8#5, hlane 9#5, hlane 10#5, hlane 11#5,
        hlane 12#5, hlane 13#5, hlane 14#5, hlane 15#5]
  · have hf : isCalleeSavedVReg v = false := Bool.eq_false_iff.mpr h
    simp only [hf, Bool.cond_false]
    exact calleeSavedVRegs_writeVReg128 s v val hf

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_writeVReg64_ite (s : State) (v : BitVec 5) (val : BitVec 64) :
    calleeSavedVRegs (s.writeVReg64 v val) =
      calleeSavedVRegs (s.writeVReg128 v (val.zeroExtend 128)) := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_writeVReg32_ite (s : State) (v : BitVec 5) (val : BitVec 32) :
    calleeSavedVRegs (s.writeVReg32 v val) =
      calleeSavedVRegs (s.writeVReg128 v (val.zeroExtend 128)) := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_setBrk (s : State) (b : BitVec 64) :
    calleeSavedVRegs (s.setBrk b) = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_nextOracle (s : State) :
    calleeSavedVRegs s.nextOracle = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_stepExclOracle (s : State) :
    calleeSavedVRegs s.stepExclOracle = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_stepExclLoop (s : State) :
    calleeSavedVRegs s.stepExclLoop = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_appendTrace (s : State) (evs : List TraceEvent) :
    calleeSavedVRegs (s.appendTrace evs) = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_setStatus (s : State) (st : ExecStatus) :
    calleeSavedVRegs (s.setStatus st) = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_setFpsr (s : State) (f : BitVec 32) :
    calleeSavedVRegs (s.setFpsr f) = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_orFpsr (s : State) (f : BitVec 32) :
    calleeSavedVRegs (s.orFpsr f) = calleeSavedVRegs s := by
  cases s; rfl




















namespace CalleeSavedPreserved

@[simp]
theorem rfl (s : State) : CalleeSavedPreserved s s :=
  ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _,
   Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩

/-- Alias of `CalleeSavedPreserved.rfl`. -/
@[deprecated CalleeSavedPreserved.rfl (since := "2026-10-26")]
theorem refl (s : State) : CalleeSavedPreserved s s :=
  rfl s

theorem trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1)
    (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  rcases h01 with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gfp, gv⟩
  rcases h12 with ⟨g19', g20', g21', g22', g23', g24', g25', g26', g27', g28', gfp', gv'⟩
  exact ⟨g19'.trans g19, g20'.trans g20, g21'.trans g21, g22'.trans g22, g23'.trans g23,
         g24'.trans g24, g25'.trans g25, g26'.trans g26, g27'.trans g27, g28'.trans g28,
         gfp'.trans gfp, gv'.trans gv⟩

@[callee_saved_split]
theorem iff_regs (s0 sf : State) :
    CalleeSavedPreserved s0 sf ↔
      sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) ∧
      sf.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) ∧
      sf.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
      sf.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
      sf.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
      sf.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
      sf.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
      sf.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
      sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
      sf.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
      sf.readReg64 Reg.fp = s0.readReg64 Reg.fp ∧
      calleeSavedVRegs sf = calleeSavedVRegs s0 := Iff.rfl

@[callee_saved_split] theorem readReg64_x19 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := h.1
@[callee_saved_split] theorem readReg64_x20 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := h.2.1
@[callee_saved_split] theorem readReg64_x21 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) := h.2.2.1
@[callee_saved_split] theorem readReg64_x22 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) := h.2.2.2.1
@[callee_saved_split] theorem readReg64_x23 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) := h.2.2.2.2.1
@[callee_saved_split] theorem readReg64_x24 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) := h.2.2.2.2.2.1
@[callee_saved_split] theorem readReg64_x25 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) := h.2.2.2.2.2.2.1
@[callee_saved_split] theorem readReg64_x26 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) := h.2.2.2.2.2.2.2.1
@[callee_saved_split] theorem readReg64_x27 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) := h.2.2.2.2.2.2.2.2.1
@[callee_saved_split] theorem readReg64_x28 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) := h.2.2.2.2.2.2.2.2.2.1
@[callee_saved_split] theorem readReg64_fp {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg64 Reg.fp = s0.readReg64 Reg.fp := h.2.2.2.2.2.2.2.2.2.2.1
@[callee_saved_split] theorem vregs {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    calleeSavedVRegs sf = calleeSavedVRegs s0 := h.2.2.2.2.2.2.2.2.2.2.2
theorem readReg64_x29 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := h.readReg64_fp

@[callee_saved_split] theorem readReg32_x19 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg32 (.gpr 19#5) = s0.readReg32 (.gpr 19#5) := by simp [State.readReg32, h.readReg64_x19]
@[callee_saved_split] theorem readReg32_x20 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg32 (.gpr 20#5) = s0.readReg32 (.gpr 20#5) := by simp [State.readReg32, h.readReg64_x20]
@[callee_saved_split] theorem readReg32_x21 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg32 (.gpr 21#5) = s0.readReg32 (.gpr 21#5) := by simp [State.readReg32, h.readReg64_x21]
@[callee_saved_split] theorem readReg32_x22 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg32 (.gpr 22#5) = s0.readReg32 (.gpr 22#5) := by simp [State.readReg32, h.readReg64_x22]
@[callee_saved_split] theorem readReg32_x23 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg32 (.gpr 23#5) = s0.readReg32 (.gpr 23#5) := by simp [State.readReg32, h.readReg64_x23]
@[callee_saved_split] theorem readReg32_x24 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg32 (.gpr 24#5) = s0.readReg32 (.gpr 24#5) := by simp [State.readReg32, h.readReg64_x24]
@[callee_saved_split] theorem readReg32_x25 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg32 (.gpr 25#5) = s0.readReg32 (.gpr 25#5) := by simp [State.readReg32, h.readReg64_x25]
@[callee_saved_split] theorem readReg32_x26 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg32 (.gpr 26#5) = s0.readReg32 (.gpr 26#5) := by simp [State.readReg32, h.readReg64_x26]
@[callee_saved_split] theorem readReg32_x27 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg32 (.gpr 27#5) = s0.readReg32 (.gpr 27#5) := by simp [State.readReg32, h.readReg64_x27]
@[callee_saved_split] theorem readReg32_x28 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg32 (.gpr 28#5) = s0.readReg32 (.gpr 28#5) := by simp [State.readReg32, h.readReg64_x28]
@[callee_saved_split] theorem readReg32_fp {s0 sf : State} (h : CalleeSavedPreserved s0 sf) :
    sf.readReg32 Reg.fp = s0.readReg32 Reg.fp := by simp [State.readReg32, h.readReg64_fp]

end CalleeSavedPreserved

namespace CallingConventionPreserved

@[simp]
theorem rfl (s : State) :
    CallingConventionPreserved s s :=
  ⟨Eq.refl _, CalleeSavedPreserved.rfl s⟩

theorem trans {s0 s1 s2 : State}
    (h01 : CallingConventionPreserved s0 s1)
    (h12 : CallingConventionPreserved s1 s2) :
    CallingConventionPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h01.2.trans h12.2⟩

@[callee_saved_split]
theorem iff_sp_and_regs (s0 sf : State) :
    CallingConventionPreserved s0 sf ↔ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := Iff.rfl

@[callee_saved_split]
theorem sp_eq {s0 sf : State} (h : CallingConventionPreserved s0 sf) : sf.sp = s0.sp := h.1

theorem calleeSaved {s0 sf : State} (h : CallingConventionPreserved s0 sf) :
    CalleeSavedPreserved s0 sf := h.2

theorem vregs {s0 sf : State} (h : CallingConventionPreserved s0 sf) :
    calleeSavedVRegs sf = calleeSavedVRegs s0 := h.2.vregs

end CallingConventionPreserved

/-- `m ⊨ ⌜False⌝ ∗ R` is always false. -/
theorem not_satisfies_false_sepConj {R : SepProp} {m : Memory}
    (h : m ⊨ (⌜False⌝ : SepProp) ∗ R) : False := by
  obtain ⟨_, hh, _⟩ := SepProp.satisfies_iff.mp h
  obtain ⟨_, _, _, _, hp, _⟩ := SepProp.holds_sepConj_iff.mp hh
  exact (SepProp.holds_pure_iff.mp hp).2

/-- Weakening the left conjunct of `m ⊨ P ∗ R` to `⌜True⌝`. -/
theorem satisfies_true_sepConj {P R : SepProp} {m : Memory}
    (h : m ⊨ P ∗ R) : m ⊨ (⌜True⌝ : SepProp) ∗ R := by
  obtain ⟨_, hh, hm⟩ := SepProp.satisfies_iff.mp h
  obtain ⟨h₁, h₂, hd, rfl, _, hr⟩ := SepProp.holds_sepConj_iff.mp hh
  have hdisj : Heap.empty.Disjoint h₂ :=
    ⟨fun _ => Or.inl rfl, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl,
      fun _ _ _ _ h => by rcases h with ⟨⟨⟩, _⟩ | ⟨_, ⟨⟩⟩,
      fun _ => Or.inl rfl⟩
  have hunion : Heap.empty.union h₂ = h₂ := by cases h₂; rfl
  refine SepProp.satisfies_iff.mpr ⟨h₂, SepProp.holds_sepConj_iff.mpr
    ⟨Heap.empty, h₂, hdisj, hunion.symm, SepProp.holds_pure_iff.mpr ⟨rfl, trivial⟩, hr⟩,
    fun a c h2 => ?_, ?_,
    fun a h2 => hm.2.2 a (by dsimp [Heap.union]; rw [h2, Bool.or_true])⟩
  · apply hm.1 a c
    dsimp [Heap.union]
    rcases hd.1 a with h1 | h2' | ⟨b, h1, h2'⟩
    · rw [h1, h2]
    · rw [h2'] at h2; contradiction
    · rw [h2'] at h2; cases h2; rw [h1]
  · rcases hm.2.1 with ⟨b, hb⟩
    refine ⟨b, fun γ hγ k => ⟨?_, ?_⟩⟩
    · have ⟨ha, _⟩ := hb γ hγ k
      dsimp [Heap.union] at ha
      cases h1 : h₁.auth γ k <;> simp_all
    · have ⟨_, hf⟩ := hb γ hγ k
      dsimp [Heap.union] at hf
      cases h1 : h₁.frag γ k <;> simp_all

/-- Reflexive rule for `reaches_pc`: when `s.pc = target_pc` and `s.status = .Running`, `post s` suffices. -/
theorem reaches_pc_refl {prog : Program} {target_pc : BitVec 64} {s : State} {post : State → Prop}
    {oom : State → Prop}
    (h_pc : s.pc = target_pc)
    (h_run : s.status = .Running)
    (h_post : post s) :
    reaches_pc prog target_pc s post oom :=
  fun _ => ⟨s, Steps.refl s, Or.inl ⟨h_pc, h_run, h_post⟩⟩

/-- Reflexive out-of-memory rule for `reaches_pc`: when `s.status = .OutOfMemory`, `oom s` suffices. -/
theorem reaches_pc_oom {prog : Program} {target_pc : BitVec 64} {s : State} {post : State → Prop}
    {oom : State → Prop}
    (h_oom : s.status = .OutOfMemory)
    (h_post : oom s := by trivial) :
    reaches_pc prog target_pc s post oom :=
  fun _ => ⟨s, Steps.refl s, Or.inr ⟨h_oom, h_post⟩⟩

/-- Symbolic instruction step rule for `reaches_pc`. -/
theorem reaches_pc_step {prog : Program} {target_pc : BitVec 64} {s : State} {inst : Instr}
    {post : State → Prop} {oom : State → Prop}
    (h_run : s.status = .Running)
    (h_fetch : prog.fetch s.pc = some inst)
    (h_next : reaches_pc prog target_pc (prog.evalInst inst s) post oom) :
    reaches_pc prog target_pc s post oom := by
  intro hL
  have hs := Step.exec h_run (Program.fetchMem_of_fetch hL h_fetch)
  rcases h_next (hs.codeLoaded hL) with ⟨sf, hsteps, hout⟩
  exact ⟨sf, Steps.step hs hsteps, hout⟩

/-- Extern call step rule for `reaches_pc`: at an extern entry point the next state is `f s`,
    provided the hook keeps frozen memory (`h_keep`) and preserves `symtab` (`h_symtab`). -/
theorem reaches_pc_extern {prog : Program} {target_pc : BitVec 64} {s : State}
    {f : State → State} {post : State → Prop} {oom : State → Prop}
    (h_run : s.status = .Running)
    (h_ext : prog.externAt? s.pc = some f)
    (h_keep : s.mem.KeepsFrozen (f s).mem)
    (h_next : reaches_pc prog target_pc (f s) post oom)
    (h_symtab : (f s).symtab = s.symtab := by rfl) :
    reaches_pc prog target_pc s post oom := by
  intro hL
  have hs := Step.extern h_run h_ext h_keep h_symtab
  rcases h_next (hs.codeLoaded hL) with ⟨sf, hsteps, hout⟩
  exact ⟨sf, Steps.step hs hsteps, hout⟩

/-- Prepend a multi-step transition `Steps prog s s'` to `reaches_pc prog target_pc s' post oom`. -/
theorem reaches_pc_steps {prog : Program} {target_pc : BitVec 64} {s s' : State}
    {post : State → Prop} {oom : State → Prop}
    (h_steps : Steps prog s s')
    (h_next : reaches_pc prog target_pc s' post oom) :
    reaches_pc prog target_pc s post oom := by
  intro hL
  rcases h_next (h_steps.codeLoaded hL) with ⟨sf, hsteps2, hout⟩
  exact ⟨sf, h_steps.trans hsteps2, hout⟩

/-- Construct `reaches_pc` from a multi-step execution `Steps prog s sf` reaching `target_pc`. -/
theorem reaches_pc_of_steps {prog : Program} {target_pc : BitVec 64} {s sf : State}
    {post : State → Prop} {oom : State → Prop}
    (h_steps : Steps prog s sf)
    (h_pc : sf.pc = target_pc)
    (h_run : sf.status = .Running)
    (h_post : post sf) :
    reaches_pc prog target_pc s post oom :=
  fun _ => ⟨sf, h_steps, Or.inl ⟨h_pc, h_run, h_post⟩⟩

/-- Symbolic conditional branch splitting rule for `reaches_pc`. -/
theorem reaches_pc_ite {prog : Program} {target_pc : BitVec 64} {c : Prop} [Decidable c]
    {s1 s2 : State} {post : State → Prop} {oom : State → Prop}
    (h1 : c → reaches_pc prog target_pc s1 post oom)
    (h2 : ¬c → reaches_pc prog target_pc s2 post oom) :
    reaches_pc prog target_pc (if c then s1 else s2) post oom := by
  split
  · rename_i hc; exact h1 hc
  · rename_i hnc; exact h2 hnc

/-- Consequence rule for `reaches_pc`. -/
theorem reaches_pc_mono {prog : Program} {target_pc : BitVec 64} {s0 : State} {P Q : State → Prop}
    {oom1 oom2 : State → Prop}
    (h : reaches_pc prog target_pc s0 P oom1)
    (h_imp : ∀ sf, sf.pc = target_pc → sf.status = .Running → P sf → Q sf)
    (h_oom : ∀ sf, sf.status = .OutOfMemory → oom1 sf → oom2 sf := by
      intro _ _ ho; first | exact ho | exact False.elim ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    reaches_pc prog target_pc s0 Q oom2 := by
  intro hL
  rcases h hL with ⟨sf, hsteps, ⟨hpc, hrun, hp⟩ | ⟨hoom, hpo⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, h_imp sf hpc hrun hp⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hoom, h_oom sf hoom hpo⟩⟩

/-- Sequential composition rule for `reaches_pc` across intermediate program counter `mid_pc`. -/
theorem reaches_pc_seq {prog : Program} {mid_pc exit_pc : BitVec 64} {s0 : State}
    {Mid Post : State → Prop} {oom1 oom2 : State → Prop}
    (h1 : reaches_pc prog mid_pc s0 Mid oom1)
    (h2 : ∀ sm, sm.pc = mid_pc → sm.status = .Running → Mid sm → reaches_pc prog exit_pc sm Post oom2)
    (h_oom : ∀ sf, sf.status = .OutOfMemory → oom1 sf → oom2 sf := by
      intro _ _ ho; first | exact ho | exact False.elim ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    reaches_pc prog exit_pc s0 Post oom2 := by
  intro hL
  rcases h1 hL with ⟨sm, hsteps1, ⟨hpc1, hrun1, hmid⟩ | ⟨hoom, hpo⟩⟩
  · rcases h2 sm hpc1 hrun1 hmid (hsteps1.codeLoaded hL) with ⟨sf, hsteps2, hout2⟩
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hoom, h_oom sm hoom hpo⟩⟩

/-- Reflexive rule for `exits_with`: when `s.status = .Exited code`, `post s` suffices. -/
theorem exits_with_refl {prog : Program} {code : BitVec 64} {s : State} {post : State → Prop}
    {oom : State → Prop}
    (h_exit : s.status = .Exited code)
    (h_post : post s) :
    exits_with prog code s post oom :=
  fun _ => ⟨s, Steps.refl s, Or.inl ⟨h_exit, h_post⟩⟩

/-- Reflexive out-of-memory rule for `exits_with`: when `s.status = .OutOfMemory`, `oom s` suffices. -/
theorem exits_with_oom {prog : Program} {code : BitVec 64} {s : State} {post : State → Prop}
    {oom : State → Prop}
    (h_oom : s.status = .OutOfMemory)
    (h_post : oom s := by trivial) :
    exits_with prog code s post oom :=
  fun _ => ⟨s, Steps.refl s, Or.inr ⟨h_oom, h_post⟩⟩

/-- Symbolic instruction step rule for `exits_with`. -/
theorem exits_with_step {prog : Program} {code : BitVec 64} {s : State} {inst : Instr}
    {post : State → Prop} {oom : State → Prop}
    (h_run : s.status = .Running)
    (h_fetch : prog.fetch s.pc = some inst)
    (h_next : exits_with prog code (prog.evalInst inst s) post oom) :
    exits_with prog code s post oom := by
  intro hL
  have hs := Step.exec h_run (Program.fetchMem_of_fetch hL h_fetch)
  rcases h_next (hs.codeLoaded hL) with ⟨sf, hsteps, hout⟩
  exact ⟨sf, Steps.step hs hsteps, hout⟩

/-- Symbolic conditional branch splitting rule for `exits_with`. -/
theorem exits_with_ite {prog : Program} {code : BitVec 64} {c : Prop} [Decidable c]
    {s1 s2 : State} {post : State → Prop} {oom : State → Prop}
    (h1 : c → exits_with prog code s1 post oom)
    (h2 : ¬c → exits_with prog code s2 post oom) :
    exits_with prog code (if c then s1 else s2) post oom := by
  split
  · rename_i hc; exact h1 hc
  · rename_i hnc; exact h2 hnc

/-- Consequence rule for `exits_with`. -/
theorem exits_with_mono {prog : Program} {code : BitVec 64} {s0 : State} {P Q : State → Prop}
    {oom1 oom2 : State → Prop}
    (h : exits_with prog code s0 P oom1)
    (h_imp : ∀ sf, sf.status = .Exited code → P sf → Q sf)
    (h_oom : ∀ sf, sf.status = .OutOfMemory → oom1 sf → oom2 sf := by
      intro _ _ ho; first | exact ho | exact False.elim ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    exits_with prog code s0 Q oom2 := by
  intro hL
  rcases h hL with ⟨sf, hsteps, ⟨hexit, hp⟩ | ⟨hoom, hpo⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hexit, h_imp sf hexit hp⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hoom, h_oom sf hoom hpo⟩⟩

/-- Compose a `reaches_pc` execution prefix reaching `mid_pc` with an `exits_with` continuation. -/
theorem exits_with_of_reaches_pc {prog : Program} {mid_pc : BitVec 64} {code : BitVec 64}
    {s0 : State} {Mid Post : State → Prop} {oom1 oom2 : State → Prop}
    (h1 : reaches_pc prog mid_pc s0 Mid oom1)
    (h2 : ∀ sm, sm.pc = mid_pc → sm.status = .Running → Mid sm → exits_with prog code sm Post oom2)
    (h_oom : ∀ sf, sf.status = .OutOfMemory → oom1 sf → oom2 sf := by
      intro _ _ ho; first | exact ho | exact False.elim ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    exits_with prog code s0 Post oom2 := by
  intro hL
  rcases h1 hL with ⟨sm, hsteps1, ⟨hpc1, hrun1, hmid⟩ | ⟨hoom, hpo⟩⟩
  · rcases h2 sm hpc1 hrun1 hmid (hsteps1.codeLoaded hL) with ⟨sf, hsteps2, hout2⟩
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hoom, h_oom sm hoom hpo⟩⟩

/-- Introduction rule for `exit_ok`. -/
theorem exit_ok_intro {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {code : α → BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry_pc → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      exits_with prog (code x) s0
        (fun sf => sf.mem ⊨ spec.post x s0 sf ∗ R)
        (fun sf => sf.mem ⊨ spec.onOom x s0 sf ∗ R)) :
    exit_ok prog entry_pc code spec := h

/-- Introduction rule for `code_ok`. -/
theorem code_ok_intro {α : Type} {prog : Program} {entry_pc exit_pc : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry_pc → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      reaches_pc prog exit_pc s0
        (fun sf => sf.mem ⊨ spec.post x s0 sf ∗ R)
        (fun sf => sf.mem ⊨ spec.onOom x s0 sf ∗ R)) :
    code_ok prog entry_pc exit_pc spec := h

/-- Elimination rule for `code_ok`: apply a verified code block contract at a concrete state `s0`. -/
theorem code_ok_apply {α : Type} {prog : Program} {entry_pc exit_pc : BitVec 64} {spec : Spec α}
    (h : code_ok prog entry_pc exit_pc spec) (x : α) (R : SepProp) {s0 : State}
    (hpc : s0.pc = entry_pc) (hrun : s0.status = .Running) (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) :
    reaches_pc prog exit_pc s0
      (fun sf => sf.mem ⊨ spec.post x s0 sf ∗ R)
      (fun sf => sf.mem ⊨ spec.onOom x s0 sf ∗ R) :=
  h x R s0 hpc hrun hpre

/-- Monotonicity rule for `code_ok`: weaken postcondition and strengthen precondition. -/
theorem code_ok_mono {α : Type} {prog : Program} {entry_pc exit_pc : BitVec 64}
    {spec spec' : Spec α}
    (h : code_ok prog entry_pc exit_pc spec)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec'.pre x s0 ∗ R) → (s0.mem ⊨ spec.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, (sf.mem ⊨ spec.post x s0 sf ∗ R) → (sf.mem ⊨ spec'.post x s0 sf ∗ R))
    (hoom : ∀ x R s0 sf, (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → (sf.mem ⊨ spec'.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    code_ok prog entry_pc exit_pc spec' :=
  code_ok_intro fun x R s0 hpc hrun hp =>
    reaches_pc_mono (code_ok_apply h x R hpc hrun (hpre x R s0 hp))
      (fun sf _ _ hq => hpost x R s0 sf hq)
      (fun sf _ ho => hoom x R s0 sf ho)

/-- Framed subroutine postcondition at the return point (`sf.pc = s0.readReg64 Reg.lr`):
    `sf.mem ⊨ spec.post x s0 sf ∗ R` and `CallingConventionPreserved s0 sf`. -/
def SubroutinePost {α : Type} (spec : Spec α) (x : α) (R : SepProp) (s0 sf : State) : Prop :=
  (sf.mem ⊨ spec.post x s0 sf ∗ R) ∧ CallingConventionPreserved s0 sf

/-- Reflexive return rule for `reaches_outcome`: when `s.pc = s0.readReg64 Reg.lr` and
    `s.status = .Running`, `SubroutinePost spec x R s0 s` suffices. -/
theorem reaches_outcome_refl_return {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {s0 s : State}
    (h_pc : s.pc = s0.readReg64 Reg.lr)
    (h_run : s.status = .Running)
    (h_post : SubroutinePost spec x R s0 s) :
    reaches_outcome prog spec x R s0 s :=
  reaches_outcome_iff.2 fun _ => ⟨s, Steps.refl s, Or.inl ⟨⟨h_pc, h_post.2.1, h_run⟩, h_post.2, h_post.1⟩⟩

/-- Reflexive process-exit rule for `reaches_outcome`: when `s.status = .Exited code`,
    `s.mem ⊨ spec.onExit x code s0 s ∗ R` suffices. -/
theorem reaches_outcome_refl_exit {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {code : BitVec 64} {s0 s : State}
    (h_exit : s.status = .Exited code)
    (h_post : s.mem ⊨ spec.onExit x code s0 s ∗ R) :
    reaches_outcome prog spec x R s0 s :=
  reaches_outcome_iff.2 fun _ => ⟨s, Steps.refl s, Or.inr (Or.inr (Or.inl ⟨code, h_exit, h_post⟩))⟩

/-- Reflexive panic rule for `reaches_outcome`: when `s.status = .Panicked`,
    `s.mem ⊨ spec.onPanic x s0 s ∗ R` suffices. -/
theorem reaches_outcome_refl_panic {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {s0 s : State}
    (h_panic : s.status = .Panicked)
    (h_post : s.mem ⊨ spec.onPanic x s0 s ∗ R) :
    reaches_outcome prog spec x R s0 s :=
  reaches_outcome_iff.2 fun _ => ⟨s, Steps.refl s, Or.inr (Or.inl ⟨h_panic, h_post⟩)⟩

/-- Reflexive out-of-memory rule for `reaches_outcome`: when `s.status = .OutOfMemory`,
    `s.mem ⊨ spec.onOom x s0 s ∗ R` suffices. -/
theorem reaches_outcome_refl_oom {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {s0 s : State}
    (h_oom : s.status = .OutOfMemory)
    (h_post : s.mem ⊨ spec.onOom x s0 s ∗ R) :
    reaches_outcome prog spec x R s0 s :=
  reaches_outcome_iff.2 fun _ => ⟨s, Steps.refl s, Or.inr (Or.inr (Or.inr ⟨h_oom, h_post⟩))⟩

/-- Extern call rule for `reaches_outcome`: at a hooked entry point the next state is `f s`,
    provided the hook keeps frozen memory (`h_keep`) and preserves `symtab` (`h_symtab`). -/
theorem reaches_outcome_extern {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {s0 s : State} {f : State → State}
    (h_run : s.status = .Running) (h_ext : prog.externAt? s.pc = some f)
    (h_keep : s.mem.KeepsFrozen (f s).mem)
    (h_next : reaches_outcome prog spec x R s0 (f s))
    (h_symtab : (f s).symtab = s.symtab := by rfl) : reaches_outcome prog spec x R s0 s := by
  rw [reaches_outcome_iff]
  intro hL
  have hs := Step.extern h_run h_ext h_keep h_symtab
  rcases reaches_outcome_iff.1 h_next (hs.codeLoaded hL) with ⟨sf, hsteps, hout⟩
  exact ⟨sf, Steps.step hs hsteps, hout⟩

/-- Extern call rule for `Rust.panicked` in `reaches_outcome`: at a hooked panic entry point
    (`prog.externAt? s.pc = some Rust.panicked`), execution transitions in one step to `.Panicked`
    without modifying memory or `symtab`. -/
theorem reaches_outcome_rust_panicked {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {s0 s : State}
    (h_run : s.status = .Running := by
      simp (config := { decide := true }) only [arm64_norm, *])
    (h_ext : prog.externAt? s.pc = some Rust.panicked := by
      simp only [arm64_norm, *])
    (h_post : s.mem ⊨ spec.onPanic x s0 (Rust.panicked s) ∗ R) :
    reaches_outcome prog spec x R s0 s :=
  reaches_outcome_extern h_run h_ext (Memory.KeepsFrozen.refl s.mem)
    (reaches_outcome_refl_panic rfl h_post) rfl


/-- Symbolic instruction step rule for `reaches_outcome`. -/
theorem reaches_outcome_step {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {s0 s : State} {inst : Instr}
    (h_run : s.status = .Running)
    (h_fetch : prog.fetch s.pc = some inst)
    (h_next : reaches_outcome prog spec x R s0 (prog.evalInst inst s)) :
    reaches_outcome prog spec x R s0 s := by
  rw [reaches_outcome_iff]
  intro hL
  have hs := Step.exec h_run (Program.fetchMem_of_fetch hL h_fetch)
  rcases reaches_outcome_iff.1 h_next (hs.codeLoaded hL) with ⟨sf, hsteps, hout⟩
  exact ⟨sf, Steps.step hs hsteps, hout⟩

/-- Prepend a multi-step transition `Steps prog s s'` to `reaches_outcome prog spec x R s0 s'`. -/
theorem reaches_outcome_steps {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {s0 s s' : State}
    (h_steps : Steps prog s s')
    (h_next : reaches_outcome prog spec x R s0 s') :
    reaches_outcome prog spec x R s0 s := by
  rw [reaches_outcome_iff]
  intro hL
  rcases reaches_outcome_iff.1 h_next (h_steps.codeLoaded hL) with ⟨sf, hsteps2, hout⟩
  exact ⟨sf, h_steps.trans hsteps2, hout⟩

/-- Symbolic conditional branch splitting rule for `reaches_outcome`. -/
theorem reaches_outcome_ite {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {c : Prop} [Decidable c] {s0 s1 s2 : State}
    (h1 : c → reaches_outcome prog spec x R s0 s1)
    (h2 : ¬c → reaches_outcome prog spec x R s0 s2) :
    reaches_outcome prog spec x R s0 (if c then s1 else s2) := by
  split
  · rename_i hc; exact h1 hc
  · rename_i hnc; exact h2 hnc

/-- Every `reaches_pc prog (s0.readReg64 Reg.lr) s (SubroutinePost spec x R s0) oom` execution
    satisfies `reaches_outcome prog spec x R s0 s`. -/
theorem reaches_outcome_of_reaches_pc {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {s0 s : State} {oom : State → Prop}
    (h : reaches_pc prog (s0.readReg64 Reg.lr) s (SubroutinePost spec x R s0) oom)
    (h_oom : ∀ sf, sf.status = .OutOfMemory → oom sf → (sf.mem ⊨ spec.onOom x s0 sf ∗ R) := by
      intro _ _ ho; first | exact ho | exact False.elim ho | exact False.elim (not_satisfies_false_sepConj ho)) :
    reaches_outcome prog spec x R s0 s := by
  rw [reaches_outcome_iff]
  intro hL
  rcases h hL with ⟨sf, hsteps, ⟨hpc, hrun, hpost, hcc⟩ | ⟨hoom, hpo⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hcc.1, hrun⟩, hcc, hpost⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom, h_oom sf hoom hpo⟩))⟩

/-- Every `exits_with prog code s (fun sf => sf.mem ⊨ spec.onExit x code s0 sf ∗ R) oom` execution
    satisfies `reaches_outcome prog spec x R s0 s`. -/
theorem reaches_outcome_of_exits_with {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {code : BitVec 64} {s0 s : State} {oom : State → Prop}
    (h : exits_with prog code s (fun sf => sf.mem ⊨ spec.onExit x code s0 sf ∗ R) oom)
    (h_oom : ∀ sf, sf.status = .OutOfMemory → oom sf → (sf.mem ⊨ spec.onOom x s0 sf ∗ R) := by
      intro _ _ ho; first | exact ho | exact False.elim ho | exact False.elim (not_satisfies_false_sepConj ho)) :
    reaches_outcome prog spec x R s0 s := by
  rw [reaches_outcome_iff]
  intro hL
  rcases h hL with ⟨sf, hsteps, ⟨hexit, hpost⟩ | ⟨hoom, hpo⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨code, hexit, hpost⟩))⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom, h_oom sf hoom hpo⟩))⟩

/-- When neither `spec.onPanic` nor `spec.onExit` is satisfiable on `sf`, `reaches_outcome` implies
    `reaches_pc prog (s0.readReg64 Reg.lr) s (SubroutinePost spec x R s0) oom`. -/
theorem reaches_pc_of_reaches_outcome {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {s0 s : State} {oom : State → Prop}
    (h : reaches_outcome prog spec x R s0 s)
    (h_no_panic : ∀ sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R) := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ sf, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → oom sf := by
      intro _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    reaches_pc prog (s0.readReg64 Reg.lr) s (SubroutinePost spec x R s0) oom := by
  intro hL
  rcases reaches_outcome_iff.1 h hL with ⟨sf, hsteps, ⟨⟨hpc, _, hrun⟩, hcc, hpost⟩ | ⟨hpanic, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨hoom, hpo⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hpost, hcc⟩⟩
  · exact False.elim (h_no_panic sf hpanic hpost)
  · exact False.elim (h_no_exit code sf hexit hpost)
  · exact ⟨sf, hsteps, Or.inr ⟨hoom, h_oom sf hoom hpo⟩⟩

/-- Introduction rule for `raw_subroutine_ok` (low-level subroutine contract without `s0.spAligned`). -/
theorem raw_subroutine_ok_intro {α : Type} {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry_pc → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      reaches_pc prog (s0.readReg64 Reg.lr) s0 (SubroutinePost spec x R s0)
        (fun sf => sf.mem ⊨ spec.onOom x s0 sf ∗ R)) :
    raw_subroutine_ok prog entry_pc spec :=
  raw_subroutine_ok_iff.2 fun x R s0 hpc hrun hpre => reaches_outcome_of_reaches_pc (h x R s0 hpc hrun hpre)




/-- Introduction rule for `subroutine_ok` from `reaches_pc` (`SubroutinePost`). -/
theorem subroutine_ok_intro {α : Type} {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry_pc → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      s0.spAligned = true →
      reaches_pc prog (s0.readReg64 Reg.lr) s0 (SubroutinePost spec x R s0)
        (fun sf => sf.mem ⊨ spec.onOom x s0 sf ∗ R)) :
    subroutine_ok prog entry_pc spec :=
  subroutine_ok_iff.2 fun x R s0 hpc hrun hpre hsp => reaches_outcome_of_reaches_pc (h x R s0 hpc hrun hpre hsp)

/-- Introduction rule for `subroutine_ok` from `reaches_outcome` (supporting normal return to `X30`,
    panic via `spec.onPanic`, and process termination via `spec.onExit`). -/
theorem subroutine_ok_outcome_intro {α : Type} {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry_pc → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      s0.spAligned = true →
      reaches_outcome prog spec x R s0 s0) :
    subroutine_ok prog entry_pc spec := subroutine_ok_iff.2 h

/-- General elimination rule for `subroutine_ok` producing `reaches_outcome prog spec x R s0 s0`. -/
theorem subroutine_ok_apply_outcome {α : Type} {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry_pc spec) (x : α) (R : SepProp) {s0 : State}
    (hpc : s0.pc = entry_pc) (hrun : s0.status = .Running) (hpre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (h_sp_align : s0.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]) :
    reaches_outcome prog spec x R s0 s0 :=
  subroutine_ok_iff.1 h x R s0 hpc hrun hpre h_sp_align

/-- Full elimination rule for `subroutine_ok`: returns both `sf.mem ⊨ spec.post x s0 sf ∗ R` and
    `CallingConventionPreserved s0 sf` when `spec.onPanic` and `spec.onExit` are unsatisfiable
    (e.g. default `⌜False⌝`). -/
theorem subroutine_ok_apply_full {α : Type} {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    {oom : State → Prop}
    (h : subroutine_ok prog entry_pc spec) (x : α) (R : SepProp) {s0 : State}
    (hpc : s0.pc = entry_pc) (hrun : s0.status = .Running) (hpre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (h_sp_align : s0.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *])
    (h_no_panic : ∀ sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R) := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ sf, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → oom sf := by
      intro _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    reaches_pc prog (s0.readReg64 Reg.lr) s0 (SubroutinePost spec x R s0) oom :=
  reaches_pc_of_reaches_outcome (subroutine_ok_iff.1 h x R s0 hpc hrun hpre h_sp_align) h_no_panic h_no_exit h_oom

/-- Elimination rule for `subroutine_ok` on inputs where `spec.onPanic` and `spec.onExit` cannot hold. -/
theorem subroutine_ok_apply_running {α : Type} {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    {oom : State → Prop}
    (h : subroutine_ok prog entry_pc spec) (x : α) (R : SepProp) {s0 : State}
    (hpc : s0.pc = entry_pc) (hrun : s0.status = .Running) (hpre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (h_no_panic : ∀ sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R) := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_sp_align : s0.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *])
    (h_oom : ∀ sf, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → oom sf := by
      intro _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    reaches_pc prog (s0.readReg64 Reg.lr) s0 (SubroutinePost spec x R s0) oom :=
  subroutine_ok_apply_full h x R hpc hrun hpre h_sp_align h_no_panic h_no_exit h_oom

/-- Elimination rule for `subroutine_ok` on inputs where `spec.post` (normal return),
    `spec.onExit`, and `spec.onOom` cannot hold, concluding that execution panics
    (`prog.CodeLoaded s0.mem → ∃ sf, Steps prog s0 sf ∧ sf.status = .Panicked`). -/
theorem subroutine_ok_apply_panics {α : Type} {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry_pc spec) (x : α) (R : SepProp) {s0 : State}
    (hpc : s0.pc = entry_pc) (hrun : s0.status = .Running) (hpre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (h_no_return : ∀ sf, Returned s0 sf → ¬(sf.mem ⊨ spec.post x s0 sf ∗ R) := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R) := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R) := by
      intro _ _ ho; exact not_satisfies_false_sepConj ho)
    (h_sp_align : s0.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]) :
    prog.CodeLoaded s0.mem →
      ∃ sf, Steps prog s0 sf ∧ sf.status = .Panicked := by
  intro hL
  rcases reaches_outcome_iff.1 (subroutine_ok_iff.1 h x R s0 hpc hrun hpre h_sp_align) hL with
    ⟨sf, hsteps, ⟨hret, _, hpost⟩ | ⟨hpanic, _⟩ | ⟨code, hexit, hpost⟩ | ⟨hoom, hpost⟩⟩
  · exact False.elim (h_no_return sf hret hpost)
  · exact ⟨sf, hsteps, hpanic⟩
  · exact False.elim (h_no_exit code sf hexit hpost)
  · exact False.elim (h_no_oom sf hoom hpost)

/-- Elimination rule for `subroutine_ok` projecting `sf.mem ⊨ spec.post x s0 sf ∗ R`. -/
theorem subroutine_ok_apply {α : Type} {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    {oom : State → Prop}
    (h : subroutine_ok prog entry_pc spec) (x : α) (R : SepProp) {s0 : State}
    (hpc : s0.pc = entry_pc) (hrun : s0.status = .Running) (hpre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (h_sp_align : s0.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *])
    (h_no_panic : ∀ sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R) := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ sf, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → oom sf := by
      intro _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    reaches_pc prog (s0.readReg64 Reg.lr) s0 (fun sf => sf.mem ⊨ spec.post x s0 sf ∗ R) oom :=
  reaches_pc_mono (subroutine_ok_apply_full h x R hpc hrun hpre h_sp_align h_no_panic h_no_exit h_oom) (fun _ _ _ hp => hp.1)

/-- Monotonicity rule for `subroutine_ok`: weaken postcondition / panic / exit / OOM postconditions and
    strengthen precondition. -/
theorem subroutine_ok_mono {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec spec' : Spec α}
    (h : subroutine_ok prog entry_pc spec)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec'.pre x s0 ∗ R) → (s0.mem ⊨ spec.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, (sf.mem ⊨ spec.post x s0 sf ∗ R) → (sf.mem ⊨ spec'.post x s0 sf ∗ R))
    (hpanic : ∀ x R s0 sf, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) → (sf.mem ⊨ spec'.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; first | exact hp | exact False.elim (not_satisfies_false_sepConj hp))
    (hexit : ∀ x code R s0 sf, (sf.mem ⊨ spec.onExit x code s0 sf ∗ R) → (sf.mem ⊨ spec'.onExit x code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; first | exact he | exact False.elim (not_satisfies_false_sepConj he))
    (hoom : ∀ x R s0 sf, (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → (sf.mem ⊨ spec'.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    subroutine_ok prog entry_pc spec' := by
  simp only [subroutine_ok_iff, reaches_outcome_iff] at h ⊢
  intro x R s0 hpc hrun hp hsp_align hL
  rcases h x R s0 hpc hrun (hpre x R s0 hp) hsp_align hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom_st, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hcc, hpost x R s0 sf hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic x R s0 sf hq⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨code, hex, hexit x code R s0 sf hq⟩))⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom x R s0 sf hq⟩))⟩

/-- A contract `spec'` follows from `spec` if every `spec'` precondition is a `spec`
    precondition for some ghost `x` (chosen from the entry memory) whose postcondition implies
    the `spec'` postcondition. -/
theorem subroutine_ok_refine {α β : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry_pc spec)
    (href : ∀ y R (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ x, (s0.mem ⊨ spec.pre x s0 ∗ R) ∧
        ∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R) → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (hpanic : ∀ x R (s0 sf : State), ¬ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hexit : ∀ x code R (s0 sf : State), ¬ (sf.mem ⊨ spec.onExit x code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ x y R (s0 sf : State), (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R) := by
      intro _ _ _ _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    subroutine_ok prog entry_pc spec' := by
  simp only [subroutine_ok_iff, reaches_outcome_iff] at h ⊢
  intro y R s0 hpc hrun hp hsp hL
  obtain ⟨x, hx, hpost⟩ := href y R s0 hp
  rcases h x R s0 hpc hrun hx hsp hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨code, _, hq⟩ | ⟨hoom_st, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hcc, hpost sf hq⟩⟩
  · exact absurd hq (hpanic x R s0 sf)
  · exact absurd hq (hexit x code R s0 sf)
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom x y R s0 sf hq⟩))⟩


/-- General consequence rule for `subroutine_ok` (prefer `subroutine_ok_refine`,
    `subroutine_ok_refine_entails`, `subroutine_ok_refine_frame`, or `subroutine_ok_mono_sp`). -/
theorem subroutine_ok_conseq {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α} {pre' : α → State → SepProp} {post' : α → State → State → SepProp}
    (h : subroutine_ok prog entry_pc spec)
    (hpre : ∀ x R s0, (s0.mem ⊨ pre' x s0 ∗ R) → (s0.mem ⊨ spec.pre x s0 ∗ R))
    (hpost : ∀ x R (s0 sf : State), sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
      SubroutinePost spec x R s0 sf → (sf.mem ⊨ post' x s0 sf ∗ R)) :
    subroutine_ok prog entry_pc { spec with pre := pre', post := post' } :=
  subroutine_ok_iff.2 fun x R s0 hpc hrun hp hsp => reaches_outcome_iff.2 fun hL =>
    (reaches_outcome_iff.1 (subroutine_ok_iff.1 h x R s0 hpc hrun (hpre x R s0 hp) hsp) hL).imp fun sf ⟨hsteps, hout⟩ =>
      ⟨hsteps, hout.imp (fun ⟨hret, hcc, hq⟩ => ⟨hret, hcc, hpost x R s0 sf hret.1 hret.2.2 ⟨hq, hcc⟩⟩) id⟩


/-- Compositional non-tail call rule for `reaches_pc`. -/
theorem reaches_pc_call_subroutine {α_callee : Type} {prog : Program}
    {callee_addr ret_pc exit_pc : BitVec 64}
    {callee_spec : Spec α_callee}
    (h_callee : subroutine_ok prog callee_addr callee_spec)
    (x_callee : α_callee) (R_callee : SepProp)
    {s_call : State} {post : State → Prop} {oom : State → Prop}
    (h_pc : s_call.pc = callee_addr)
    (h_run : s_call.status = .Running)
    (h_lr : s_call.readReg64 Reg.lr = ret_pc)
    (h_pre : s_call.mem ⊨ callee_spec.pre x_callee s_call ∗ R_callee)
    (h_cont : ∀ s_ret : State,
      s_ret.pc = ret_pc →
      s_ret.status = .Running →
      s_ret.sp = s_call.sp →
      CalleeSavedPreserved s_call s_ret →
      (s_ret.mem ⊨ callee_spec.post x_callee s_call s_ret ∗ R_callee) →
      reaches_pc prog exit_pc s_ret post oom)
    (h_sp_align : s_call.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *])
    (h_no_panic : ∀ sf, sf.status = .Panicked → ¬(sf.mem ⊨ callee_spec.onPanic x_callee s_call sf ∗ R_callee) := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ code sf, sf.status = .Exited code → ¬(sf.mem ⊨ callee_spec.onExit x_callee code s_call sf ∗ R_callee) := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ sf, sf.status = .OutOfMemory → (sf.mem ⊨ callee_spec.onOom x_callee s_call sf ∗ R_callee) → oom sf := by
      intro _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho)) :
    reaches_pc prog exit_pc s_call post oom := by
  have h_reach := subroutine_ok_apply_full h_callee x_callee R_callee h_pc h_run h_pre h_sp_align h_no_panic h_no_exit h_oom
  rw [h_lr] at h_reach
  refine reaches_pc_seq h_reach fun s_ret h_ret_pc h_ret_run ⟨h_post_callee, h_sp_ret, h_cs_ret⟩ => ?_
  exact h_cont s_ret h_ret_pc h_ret_run h_sp_ret h_cs_ret h_post_callee

/-- Subtracting any `16`-byte-aligned byte count `n` (`16 ∣ n`) from a `16`-byte-aligned stack
    pointer `sp` preserves `16`-byte alignment (`((sp - BitVec.ofNat 64 n) &&& 15#64 == 0#64) = true`). -/
theorem spAligned_sub_of_dvd (sp : BitVec 64) (n : Nat)
    (hsp : (sp &&& 15#64 == 0#64) = true)
    (hdvd : 16 ∣ n := by first | decide | omega) :
    ((sp - BitVec.ofNat 64 n) &&& 15#64 == 0#64) = true := by
  obtain ⟨k, rfl⟩ := hdvd
  rw [BitVec.ofNat_mul]
  generalize BitVec.ofNat 64 k = q
  revert hsp
  bv_bits

/-- Subtracting any `16`-byte-aligned byte count `n` (`16 ∣ n`) from `s.sp` when
    `s.spAligned = true` preserves `16`-byte alignment. -/
theorem _root_.Arm64.State.spAligned_sub_of_dvd (s : State) (n : Nat)
    (hsp : s.spAligned = true)
    (hdvd : 16 ∣ n := by first | decide | omega) :
    ((s.sp - BitVec.ofNat 64 n) &&& 15#64 == 0#64) = true :=
  Arm64.spAligned_sub_of_dvd s.sp n hsp hdvd


/-- Compositional tail-call rule for `reaches_pc`. -/
theorem reaches_pc_tailcall_subroutine {α_callee α_caller : Type} {prog : Program}
    {callee_addr : BitVec 64}
    {callee_spec : Spec α_callee} {caller_spec : Spec α_caller}
    (h_callee : subroutine_ok prog callee_addr callee_spec)
    (x_callee : α_callee) (x_caller : α_caller)
    {R_callee R_caller : SepProp}
    {s0 s_call : State}
    {oom : State → Prop}
    (h_pc : s_call.pc = callee_addr)
    (h_run : s_call.status = .Running)
    (h_lr : s_call.readReg64 Reg.lr = s0.readReg64 Reg.lr)
    (h_sp : s_call.sp = s0.sp)
    (h_cs : CalleeSavedPreserved s0 s_call)
    (h_pre : s_call.mem ⊨ callee_spec.pre x_callee s_call ∗ R_callee)
    (h_post : ∀ sf : State,
      sf.pc = s0.readReg64 Reg.lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (sf.mem ⊨ callee_spec.post x_callee s_call sf ∗ R_callee) →
      (sf.mem ⊨ caller_spec.post x_caller s0 sf ∗ R_caller))
    (h_sp_align : s0.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *])
    (h_no_panic : ∀ sf, sf.status = .Panicked → ¬(sf.mem ⊨ callee_spec.onPanic x_callee s_call sf ∗ R_callee) := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ code sf, sf.status = .Exited code → ¬(sf.mem ⊨ callee_spec.onExit x_callee code s_call sf ∗ R_callee) := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ callee_spec.onOom x_callee s_call sf ∗ R_callee) → oom sf := by
      intro _ _ ho; first
        | exact ho
        | exact False.elim (not_satisfies_false_sepConj ho)
        | exact satisfies_true_sepConj _ _) :
    reaches_pc prog (s0.readReg64 Reg.lr) s_call (SubroutinePost caller_spec x_caller R_caller s0) oom := by
  have h_call_align : s_call.spAligned = true := by
    simpa only [State.spAligned, h_sp] using h_sp_align
  have h_reach := subroutine_ok_apply_full h_callee x_callee R_callee h_pc h_run h_pre h_call_align h_no_panic h_no_exit
  rw [h_lr] at h_reach
  refine reaches_pc_mono h_reach (fun sf hpcf hrunf ⟨hpost_callee, hsp_sf, hcs_sf⟩ => ?_) h_oom
  have hsp_final : sf.sp = s0.sp := hsp_sf.trans h_sp
  have hcs_final : CalleeSavedPreserved s0 sf := h_cs.trans hcs_sf
  exact ⟨h_post sf hpcf hrunf hsp_final hcs_final hpost_callee, hsp_final, hcs_final⟩


/-! ## Single-String PC-Range Fetch and Placement-Independence Lifting -/

namespace Program

theorem findSome?_eq_none_of_forall {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = none) → l.findSome? f = none
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.findSome?_cons, h x (List.mem_cons_self ..)]
    exact findSome?_eq_none_of_forall fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- No hook is found at an offset inside a `hookFree` range. -/
theorem hookAtOff?_eq_none_of_hookFree {prog : Program} {off len k : Nat}
    (h : prog.hookFree off len) (hlo : off ≤ k) (hhi : k < off + len) :
    prog.hookAtOff? k = none := by
  rcases h with ⟨h1, h2⟩
  rw [List.all_eq_true] at h1 h2
  have e1 : (prog.stubs.findSome? fun (n, o) => if o == k then prog.externs n else none) = none := by
    apply findSome?_eq_none_of_forall
    rintro ⟨n, o⟩ hmem
    have := h1 _ hmem
    by_cases hk : o = k
    · subst hk
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
        Option.isNone_iff_eq_none] at this
      simp only [beq_self_eq_true, ite_true]
      rcases this with (h | h) | h <;> first | omega | exact h
    · simp [hk]
  have e2 : (prog.symbols.findSome? fun (n, o) => if o == k then prog.overrides n else none) = none := by
    apply findSome?_eq_none_of_forall
    rintro ⟨n, o⟩ hmem
    have := h2 _ hmem
    by_cases hk : o = k
    · subst hk
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
        Option.isNone_iff_eq_none] at this
      simp only [beq_self_eq_true, ite_true]
      rcases this with (h | h) | h <;> first | omega | exact h
    · simp [hk]
  unfold hookAtOff?
  rw [e1, e2]
  rfl

/-- No hook is found anywhere when neither `externs` nor `overrides` define any hook. -/
theorem hookAtOff?_eq_none_of_isNone {prog : Program}
    (h_ext : ∀ sym, (prog.externs sym).isNone = true)
    (h_ovr : ∀ sym, (prog.overrides sym).isNone = true) (k : Nat) :
    prog.hookAtOff? k = none := by
  have e1 : (prog.stubs.findSome? fun (n, o) => if o == k then prog.externs n else none) = none :=
    findSome?_eq_none_of_forall fun ⟨n, _⟩ _ => by
      simp [Option.isNone_iff_eq_none.mp (h_ext n)]
  have e2 : (prog.symbols.findSome? fun (n, o) => if o == k then prog.overrides n else none) = none :=
    findSome?_eq_none_of_forall fun ⟨n, _⟩ _ => by
      simp [Option.isNone_iff_eq_none.mp (h_ovr n)]
  unfold hookAtOff?
  rw [e1, e2]
  rfl




theorem add_ofNat_sub_self (b : BitVec 64) (k : Nat) :
    b + BitVec.ofNat 64 k - b = BitVec.ofNat 64 k := by
  rw [BitVec.add_comm]; exact BitVec.add_sub_cancel _ _

/-- `fetch` at `base + off` in terms of the code offset `off`. -/
theorem fetch_base_add {prog : Program} {off : Nat} (h_off : off < 2 ^ 64) :
    prog.fetch (prog.base + BitVec.ofNat 64 off) =
      if (prog.hookAtOff? off).isSome then none else (prog.readWordOff off).bind decode := by
  have h : (prog.base + BitVec.ofNat 64 off - prog.base).toNat = off := by
    rw [add_ofNat_sub_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_off]
  unfold fetch externAt?
  rw [h]

theorem fetch_of_readWordOff {prog : Program} {off : Nat} {w : BitVec 32}
    (h_off : off < 2 ^ 64) (h_hook : prog.hookAtOff? off = none)
    (h_read : prog.readWordOff off = some w) :
    prog.fetch (prog.base + BitVec.ofNat 64 off) = decode w := by
  rw [fetch_base_add h_off, h_hook, h_read]
  rfl

/-- `pc` is `prog.base` plus its code offset. -/
theorem base_add_sub_toNat (base pc : BitVec 64) :
    base + BitVec.ofNat 64 (pc - base).toNat = pc := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_arith

theorem fetch_of_hasWordsOff {prog : Program} {off : Nat} {words : List (BitVec 32)}
    (h : prog.hasWordsOff off words) (i : Nat) (hi : i < words.length) :
    prog.fetch (prog.base + BitVec.ofNat 64 (off + 4 * i)) = decode (words[i]'hi) :=
  fetch_of_readWordOff (by have := h.1; omega)
    (hookAtOff?_eq_none_of_hookFree h.2.2 (by omega) (by omega)) (h.2.1 i hi)

theorem fetch_of_hasWords {prog : Program} {addr : BitVec 64} {words : List (BitVec 32)}
    (h : prog.hasWords addr words) (i : Nat) (hi : i < words.length) :
    prog.fetch (addr + BitVec.ofNat 64 (4 * i)) = decode (words[i]'hi) := by
  have h_eq : addr + BitVec.ofNat 64 (4 * i) =
      prog.base + BitVec.ofNat 64 ((addr - prog.base).toNat + 4 * i) := by
    have := h.1
    have h1 : 4 * i < 2 ^ 64 := by omega
    have h2 := base_add_sub_toNat prog.base addr
    generalize 4 * i = k at *
    bv_arith
  rw [h_eq]
  exact fetch_of_hasWordsOff h i hi


/-- Decode the `i`-th 32-bit instruction word of `words`. -/
def decodeWordAt (words : List (BitVec 32)) (i : Nat) : Option Instr :=
  match words[i]? with
  | some w => decode w
  | none => none

/-- Decode the `i`-th 32-bit instruction word of `hex`. -/
def decodeHexWordAt (hex : List (BitVec 32)) (i : Nat) : Option Instr :=
  decodeWordAt hex i

theorem fetch_of_hasWords_decodeAt {prog : Program} {addr pc : BitVec 64}
    {words : List (BitVec 32)} (i : Nat) {inst : Instr}
    (h : prog.hasWords addr words)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_dec : decodeWordAt words i = some inst) :
    prog.fetch pc = some inst := by
  unfold decodeWordAt at h_dec
  split at h_dec
  · rename_i w hw
    rw [List.getElem?_eq_some_iff] at hw
    rcases hw with ⟨hi, rfl⟩
    rw [h_pc, fetch_of_hasWords h i hi, h_dec]
  · contradiction

theorem fetch_of_hasCode_decodeAt {prog : Program} {addr pc : BitVec 64}
    {hex : List (BitVec 32)} (i : Nat) {inst : Instr}
    (h : prog.hasCode addr hex)
    (h_pc : pc = addr + BitVec.ofNat 64 (4 * i))
    (h_dec : decodeHexWordAt hex i = some inst) :
    prog.fetch pc = some inst :=
  fetch_of_hasWords_decodeAt i h h_pc h_dec

/-- `codeAt` gives `hasCode` at the absolute entry address `fnAddr name`. -/
theorem hasCode_fnAddr_of_codeAt {prog : Program} {name : String} {hex : List (BitVec 32)}
    (h : prog.codeAt name hex) : prog.hasCode (prog.fnAddr name) hex := by
  unfold hasCode hasWords fnAddr
  rw [add_ofNat_sub_self, BitVec.toNat_ofNat]
  rcases h with ⟨h_len, h_rd, h_free⟩
  rcases Nat.eq_zero_or_pos hex.length with h0 | hpos
  · refine ⟨by omega, fun i hi => absurd hi (by omega), ?_⟩
    rw [h0]
    exact ⟨List.all_eq_true.mpr fun _ _ => by simp; omega,
           List.all_eq_true.mpr fun _ _ => by simp; omega⟩
  · rw [Nat.mod_eq_of_lt (by omega)]
    exact ⟨h_len, h_rd, h_free⟩

theorem eq_wordToBytesLE_of_append {b0 b1 b2 b3 : BitVec 8} {v : BitVec 32}
    (h : b3 ++ b2 ++ b1 ++ b0 = v) :
    b0 = v.extractLsb' 0 8 ∧
    b1 = v.extractLsb' 8 8 ∧
    b2 = v.extractLsb' 16 8 ∧
    b3 = v.extractLsb' 24 8 := by
  subst h
  refine ⟨by bv_decide, by bv_decide, by bv_decide, by bv_decide⟩

/-- `readWordOff` only reads at 4-byte aligned offsets. -/
theorem readWordOff_aligned {p : Program} {off : Nat} {w : BitVec 32}
    (h : p.readWordOff off = some w) : off % 4 = 0 := by
  unfold readWordOff at h
  split at h
  · contradiction
  · omega

theorem readWordOff_eq_some_iff (p : Program) (off : Nat) (w : BitVec 32) (h_al : off % 4 = 0) :
    p.readWordOff off = some w ↔
      p.code[off]? = some (w.extractLsb' 0 8) ∧
      p.code[off + 1]? = some (w.extractLsb' 8 8) ∧
      p.code[off + 2]? = some (w.extractLsb' 16 8) ∧
      p.code[off + 3]? = some (w.extractLsb' 24 8) := by
  unfold readWordOff
  have h_al' : ¬(off % 4 ≠ 0) := by omega
  simp only [h_al', ↓reduceIte]
  have h0 : (p.code.drop off)[0]? = p.code[off]? := by simp
  have h1 : (p.code.drop off)[1]? = p.code[off + 1]? := by simp
  have h2 : (p.code.drop off)[2]? = p.code[off + 2]? := by simp
  have h3 : (p.code.drop off)[3]? = p.code[off + 3]? := by simp
  rw [← h0, ← h1, ← h2, ← h3]
  match p.code.drop off with
  | b0 :: b1 :: b2 :: b3 :: _ =>
    simp only [Option.some.injEq, List.getElem?_cons_zero, List.getElem?_cons_succ]
    constructor
    · intro h_eq
      exact eq_wordToBytesLE_of_append h_eq
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      exact Memory.concat_bytes_32 w
  | [] | [_] | [_, _] | [_, _, _] =>
    simp

theorem getElem?_flatMap_wordToBytesLE (words : List (BitVec 32)) (i r : Nat)
    (hi : i < words.length) (hr : r < 4) :
    (words.flatMap wordToBytesLE)[4 * i + r]? = some ((words[i]'hi).extractLsb' (8 * r) 8) := by
  induction words generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons w0 ws ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, wordToBytesLE, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      match r, hr with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | 3, _ => rfl
    | succ i' =>
      have hi' : i' < ws.length := Nat.lt_of_succ_lt_succ hi
      have h_idx : 4 * (i' + 1) + r = (4 * i' + r) + 1 + 1 + 1 + 1 := by omega
      simp only [List.flatMap_cons, wordToBytesLE, h_idx, List.getElem_cons_succ]
      exact ih i' hi'

theorem length_flatMap_wordToBytesLE (words : List (BitVec 32)) :
    (words.flatMap wordToBytesLE).length = 4 * words.length := by
  induction words with
  | nil => rfl
  | cons w0 ws ih =>
    simp only [List.flatMap_cons, wordToBytesLE, List.length_append, List.length_cons,
               List.length_nil, ih]
    omega

theorem code_getElem?_of_hasWordsOff {prog : Program} {off : Nat} {words : List (BitVec 32)}
    (h_words : prog.hasWordsOff off words) (m : Nat) (hm : m < 4 * words.length) :
    prog.code[off + m]? = (words.flatMap wordToBytesLE)[m]? := by
  have hi : m / 4 < words.length := by omega
  have hm_eq : 4 * (m / 4) + m % 4 = m := by omega
  have hw := h_words.2.1 (m / 4) hi
  have h_read := (readWordOff_eq_some_iff prog _ _ (readWordOff_aligned hw)).mp hw
  have h_get := getElem?_flatMap_wordToBytesLE words (m / 4) (m % 4) hi (by omega)
  rw [hm_eq] at h_get
  rw [h_get]
  rcases h_read with ⟨hb0, hb1, hb2, hb3⟩
  have h_idx : off + m = off + 4 * (m / 4) + m % 4 := by omega
  rw [h_idx]
  have h_rem : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases h_rem with h | h | h | h <;> rw [h] <;> simpa using ‹_›

/-! ### Symbol-Table Lookup Steps -/

/-- Fast `find?` step when the head entry matches `name`. -/
theorem find?_name_cons_eq (name : String) (off : Nat) (rest : List (String × Nat)) :
    (((name, off) :: rest).find? (·.1 == name)) = some (name, off) := by
  simp

/-- Fast `find?` step when the head entry `s` differs from `name` via `List Char` inequality. -/
theorem find?_name_cons_ne {s name : String} {cs1 cs2 : List Char}
    (off : Nat) (rest : List (String × Nat))
    (hs : s = String.ofList cs1) (hname : name = String.ofList cs2)
    (hne : (cs1 == cs2) = false) :
    (((s, off) :: rest).find? (·.1 == name)) = rest.find? (·.1 == name) := by
  have hbeq : (s == name) = false := by
    rw [hs, hname, beq_eq_false_iff_ne, ne_eq, String.ofList_inj]
    exact beq_eq_false_iff_ne.mp hne
  simp [List.find?, hbeq]

/-- `find?` on an empty symbol table. -/
theorem find?_name_nil (name : String) :
    (([] : List (String × Nat)).find? (·.1 == name)) = none := rfl

/-- `fnAddr` from `fnOff`. -/
theorem fnAddr_eq_of_fnOff_eq {prog : Program} {name : String} {off : Nat}
    (h : prog.fnOff name = off) : prog.fnAddr name = prog.base + BitVec.ofNat 64 off := by
  rw [fnAddr, h]

/-- `fnOff` from a symbol-table hit. -/
theorem fnOff_of_symbols_find? {prog : Program} {name : String} {off : Nat}
    (h : prog.symbols.find? (·.1 == name) = some (name, off)) :
    prog.fnOff name = off := by
  simp only [fnOff, findSymbol?, h, Option.orElse_some, Option.map_some, Option.getD_some]

/-- `fnOff` from a stub-table hit when `name` is not a defined symbol. -/
theorem fnOff_of_stubs_find? {prog : Program} {name : String} {off : Nat}
    (h_sym : prog.symbols.find? (·.1 == name) = none)
    (h : prog.stubs.find? (·.1 == name) = some (name, off)) :
    prog.fnOff name = off := by
  simp only [fnOff, findSymbol?, h_sym, h, Option.orElse_none, Option.map_some, Option.getD_some]


/-- Single-pass linear-time check that `bs` starts with the little-endian byte encodings of `words`
    and `4 * words.length ≤ rem`. -/
def checkBytesWordsBound : Nat → List (BitVec 8) → List (BitVec 32) → Bool
  | _, _, [] => true
  | rem, b0 :: b1 :: b2 :: b3 :: bs, w :: ws =>
    decide (4 ≤ rem) && (b3 ++ b2 ++ b1 ++ b0 == w) && checkBytesWordsBound (rem - 4) bs ws
  | _, _, _ :: _ => false

theorem checkBytesWordsBound_bound {rem : Nat} {bs : List (BitVec 8)} {words : List (BitVec 32)}
    (h : checkBytesWordsBound rem bs words = true) :
    4 * words.length ≤ rem := by
  induction words generalizing rem bs with
  | nil => simp
  | cons w ws ih =>
    match bs with
    | [] | [_] | [_, _] | [_, _, _] => simp [checkBytesWordsBound] at h
    | b0 :: b1 :: b2 :: b3 :: rest =>
      simp only [checkBytesWordsBound, Bool.and_eq_true, decide_eq_true_eq] at h
      have h_ih := ih h.2
      simp only [List.length_cons]
      omega

theorem checkBytesWordsBound_drop {rem : Nat} {bs : List (BitVec 8)} {words : List (BitVec 32)}
    (h : checkBytesWordsBound rem bs words = true) (i : Nat) (hi : i < words.length) :
    ∃ b0 b1 b2 b3 rest,
      bs.drop (4 * i) = b0 :: b1 :: b2 :: b3 :: rest ∧
      b3 ++ b2 ++ b1 ++ b0 = words[i]'hi := by
  induction words generalizing rem bs i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons w ws ih =>
    match bs with
    | [] | [_] | [_, _] | [_, _, _] => simp [checkBytesWordsBound] at h
    | b0 :: b1 :: b2 :: b3 :: rest =>
      simp only [checkBytesWordsBound, Bool.and_eq_true, beq_iff_eq] at h
      cases i with
      | zero =>
        exact ⟨b0, b1, b2, b3, rest, rfl, h.1.2⟩
      | succ i' =>
        have hi' : i' < ws.length := Nat.lt_of_succ_lt_succ hi
        have h_drop : (b0 :: b1 :: b2 :: b3 :: rest).drop (4 * (i' + 1)) = rest.drop (4 * i') := by
          have : 4 * (i' + 1) = 4 * i' + 1 + 1 + 1 + 1 := by omega
          rw [this]
          rfl
        rw [h_drop]
        exact ih h.2 i' hi'

/-- Prove `prog.hasWordsOff off words` in a single pass over `words` and `prog.code.drop off`,
    plus a decidable `hookFree` check. `off` must be 4-byte aligned (`readWordOff`). -/
theorem hasWordsOff_of_checkBytesWordsBound {prog : Program} {off : Nat}
    {words : List (BitVec 32)}
    (h_al : off % 4 = 0)
    (h_off : off ≤ 2 ^ 64)
    (h_check : (decide (prog.hookFree off (4 * words.length)) &&
      checkBytesWordsBound (2 ^ 64 - off) (prog.code.drop off) words) = true) :
    prog.hasWordsOff off words := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_check
  rcases h_check with ⟨h_free, h_cb⟩
  have h_len := checkBytesWordsBound_bound h_cb
  refine ⟨by omega, fun i hi => ?_, h_free⟩
  rcases checkBytesWordsBound_drop h_cb i hi with ⟨b0, b1, b2, b3, rest, h_drop, h_word⟩
  rw [List.drop_drop] at h_drop
  unfold readWordOff
  have h_al' : ¬((off + 4 * i) % 4 ≠ 0) := by omega
  simp only [h_al', ↓reduceIte]
  rw [h_drop]; exact congrArg some h_word

/-- `prog.hasWords addr words` via `hasWordsOff_of_checkBytesWordsBound`. -/
theorem hasWords_of_checkBytesWordsBound {prog : Program} {addr : BitVec 64}
    {words : List (BitVec 32)}
    (h_check : (decide ((addr - prog.base).toNat % 4 = 0) &&
      (decide (prog.hookFree (addr - prog.base).toNat (4 * words.length)) &&
      checkBytesWordsBound (2 ^ 64 - (addr - prog.base).toNat)
        (prog.code.drop (addr - prog.base).toNat) words)) = true) :
    prog.hasWords addr words := by
  rw [Bool.and_eq_true, decide_eq_true_eq] at h_check
  exact hasWordsOff_of_checkBytesWordsBound h_check.1 (Nat.le_of_lt (BitVec.isLt _)) h_check.2

/-- `hasWordsOff_of_checkBytesWordsBound` with `off % 4 = 0` and `off ≤ 2 ^ 64` folded into
    the single kernel-evaluated boolean check. -/
theorem hasWordsOff_of_check {prog : Program} {off : Nat}
    {words : List (BitVec 32)}
    (h_check : (decide (off % 4 = 0) && (decide (off ≤ 2 ^ 64) && decide (prog.hookFree off
        (4 * words.length)) &&
      checkBytesWordsBound (2 ^ 64 - off) (prog.code.drop off) words)) = true) :
    prog.hasWordsOff off words := by
  rw [Bool.and_eq_true, decide_eq_true_eq] at h_check
  obtain ⟨h_al, h_check⟩ := h_check
  rw [Bool.and_assoc, Bool.and_eq_true, decide_eq_true_eq] at h_check
  exact hasWordsOff_of_checkBytesWordsBound h_al h_check.1 h_check.2

/-- Prove `prog.hasCode addr hex` in a single pass via `checkBytesWordsBound`. -/
theorem hasCode_of_checkBytesWordsBound {prog : Program} {addr : BitVec 64}
    {hex : List (BitVec 32)}
    (h_check : (decide ((addr - prog.base).toNat % 4 = 0) &&
      (decide (prog.hookFree (addr - prog.base).toNat (4 * hex.length)) &&
      checkBytesWordsBound (2 ^ 64 - (addr - prog.base).toNat)
        (prog.code.drop (addr - prog.base).toNat) hex)) = true) :
    prog.hasCode addr hex :=
  hasWords_of_checkBytesWordsBound h_check

theorem codeAt_of_fnOff_eq {prog : Program} {name : String} {off : Nat} {hex : List (BitVec 32)}
    (h_off : prog.fnOff name = off)
    (h_code : prog.hasWordsOff off hex) :
    prog.codeAt name hex := by
  unfold codeAt
  rw [h_off]
  exact h_code



theorem hasCode_fnAddr_of_fnOff_eq {prog : Program} {name : String} {off : Nat} {hex : List (BitVec 32)}
    (h_off : prog.fnOff name = off)
    (h_code : prog.hasWordsOff off hex) :
    prog.hasCode (prog.fnAddr name) hex :=
  hasCode_fnAddr_of_codeAt (codeAt_of_fnOff_eq h_off h_code)




end Program

/-- Any `Step` requires the starting state to be `.Running`. -/
theorem Step.running_of_step {prog : Program} {s1 s2 : State} (h : Step prog s1 s2) :
    s1.status = .Running := by
  cases h <;> assumption



/-- No step can be taken from a `.Halted` state. -/
theorem Steps.eq_of_halted {prog : Program} {s1 s2 : State}
    (h : Steps prog s1 s2) (h_halt : s1.status = .Halted) :
    s2 = s1 := by
  cases h with
  | refl => rfl
  | step hs _ =>
    have hrun := hs.running_of_step
    rw [h_halt] at hrun
    contradiction

/-! ## Core Separation Logic Algebraic and Pure-Extraction Lemmas -/

namespace Heap

theorem Disjoint.symm {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) : h₂.Disjoint h₁ := by
  refine ⟨fun a => ?_, fun γ k => (hd.2.1 γ k).symm, fun γ k => (hd.2.2.1 γ k).symm,
    fun γ k oa v h => hd.2.2.2.1 γ k oa v h.symm, fun a => (hd.2.2.2.2 a).symm⟩
  rcases hd.1 a with h1 | h2 | ⟨b, h1, h2⟩
  · exact Or.inr (Or.inl h1)
  · exact Or.inl h2
  · exact Or.inr (Or.inr ⟨b, h2, h1⟩)

theorem Disjoint.of_phys_left {h₁ h₂ : Heap}
    (ha : h₁.auth = fun _ _ => none := by rfl)
    (hf : h₁.frag = fun _ _ => none := by rfl)
    (hp : ∀ a, h₁.phys a = none ∨ h₂.phys a = none ∨
      ∃ b, h₁.phys a = some (.ro b) ∧ h₂.phys a = some (.ro b))
    (hm : h₁.mapped = fun _ => false := by rfl) :
    h₁.Disjoint h₂ := by
  refine ⟨hp, fun γ k => Or.inl (congrFun (congrFun ha γ) k),
    fun γ k => Or.inl (congrFun (congrFun hf γ) k), fun γ k oa v h => ?_,
    fun a => Or.inl (congrFun hm a)⟩
  rcases h with ⟨h1, _⟩ | ⟨_, h1⟩
  · rw [congrFun (congrFun ha γ) k] at h1; contradiction
  · rw [congrFun (congrFun hf γ) k] at h1; contradiction

theorem Disjoint.of_phys_right {h₁ h₂ : Heap}
    (ha : h₂.auth = fun _ _ => none := by rfl)
    (hf : h₂.frag = fun _ _ => none := by rfl)
    (hp : ∀ a, h₁.phys a = none ∨ h₂.phys a = none ∨
      ∃ b, h₁.phys a = some (.ro b) ∧ h₂.phys a = some (.ro b))
    (hm : h₂.mapped = fun _ => false := by rfl) :
    h₁.Disjoint h₂ := by
  refine (Disjoint.of_phys_left ha hf (fun a => ?_) hm).symm
  rcases hp a with h1 | h2 | ⟨b, h1, h2⟩
  · exact Or.inr (Or.inl h1)
  · exact Or.inl h2
  · exact Or.inr (Or.inr ⟨b, h2, h1⟩)

@[simp, arm64_norm]
theorem disjoint_empty_left (h : Heap) : Heap.empty.Disjoint h :=
  Disjoint.of_phys_left rfl rfl (fun _ => Or.inl rfl)

@[simp, arm64_norm]
theorem disjoint_empty_right (h : Heap) : h.Disjoint Heap.empty :=
  (disjoint_empty_left h).symm

@[simp, arm64_norm]
theorem union_empty_left (h : Heap) : Heap.empty.union h = h := by
  cases h; rfl

@[simp, arm64_norm]
theorem union_empty_right (h : Heap) : h.union Heap.empty = h := by
  apply Heap.ext
  · funext a; dsimp [union, empty]; cases h.phys a <;> rfl
  · funext γ k; dsimp [union, empty]; cases h.auth γ k <;> rfl
  · funext γ k; dsimp [union, empty]; cases h.frag γ k <;> rfl
  · funext a; dsimp [union, empty]; cases h.mapped a <;> rfl

theorem union_comm_of_disjoint {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) :
    h₁.union h₂ = h₂.union h₁ := by
  apply Heap.ext
  · funext a; dsimp [union]
    rcases hd.1 a with h1 | h2 | ⟨b, h1, h2⟩
    · rw [h1]; cases h₂.phys a <;> rfl
    · rw [h2]; cases h₁.phys a <;> rfl
    · rw [h1, h2]
  · funext γ k; dsimp [union]
    rcases hd.2.1 γ k with h1 | h2
    · rw [h1]; cases h₂.auth γ k <;> rfl
    · rw [h2]; cases h₁.auth γ k <;> rfl
  · funext γ k; dsimp [union]
    rcases hd.2.2.1 γ k with h1 | h2
    · rw [h1]; cases h₂.frag γ k <;> rfl
    · rw [h2]; cases h₁.frag γ k <;> rfl
  · funext a; dsimp [union]
    rcases hd.2.2.2.2 a with h1 | h2
    · rw [h1]; cases h₂.mapped a <;> rfl
    · rw [h2]; cases h₁.mapped a <;> rfl

theorem union_assoc (h₁ h₂ h₃ : Heap) :
    (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃) := by
  apply Heap.ext
  · funext a; dsimp [union]; cases h₁.phys a <;> rfl
  · funext γ k; dsimp [union]; cases h₁.auth γ k <;> rfl
  · funext γ k; dsimp [union]; cases h₁.frag γ k <;> rfl
  · funext a; dsimp [union]; cases h₁.mapped a <;> rfl

theorem disjoint_union_left {h₁ h₂ h₃ : Heap} (hd12 : h₁.Disjoint h₂) :
    (h₁.union h₂).Disjoint h₃ ↔ h₁.Disjoint h₃ ∧ h₂.Disjoint h₃ := by
  constructor
  · intro hd
    have hphys1 : ∀ a, h₁.phys a = none ∨ h₃.phys a = none ∨
        ∃ b, h₁.phys a = some (.ro b) ∧ h₃.phys a = some (.ro b) := by
      intro a
      rcases hd.1 a with hu | h3 | ⟨b, hu, h3⟩
      · dsimp [union] at hu; cases h : h₁.phys a <;> simp_all
      · exact Or.inr (Or.inl h3)
      · dsimp [union] at hu
        cases h : h₁.phys a with
        | none => exact Or.inl rfl
        | some c => rw [h] at hu; exact Or.inr (Or.inr ⟨b, hu, h3⟩)
    have hphys2 : ∀ a, h₂.phys a = none ∨ h₃.phys a = none ∨
        ∃ b, h₂.phys a = some (.ro b) ∧ h₃.phys a = some (.ro b) := by
      intro a
      rcases hd.1 a with hu | h3 | ⟨b, hu, h3⟩
      · dsimp [union] at hu; cases h : h₁.phys a <;> simp_all
      · exact Or.inr (Or.inl h3)
      · dsimp [union] at hu
        cases h : h₁.phys a with
        | none => rw [h] at hu; exact Or.inr (Or.inr ⟨b, hu, h3⟩)
        | some c =>
          rw [h] at hu
          rcases hd12.1 a with h1 | h2 | ⟨b', h1, h2⟩
          · rw [h] at h1; contradiction
          · exact Or.inl h2
          · rw [h1] at h; cases h; cases hu; exact Or.inr (Or.inr ⟨b, h2, h3⟩)
    have hauth1 : ∀ γ k, h₁.auth γ k = none ∨ h₃.auth γ k = none := by
      intro γ k
      rcases hd.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.auth γ k <;> simp_all
      · exact Or.inr h3
    have hauth2 : ∀ γ k, h₂.auth γ k = none ∨ h₃.auth γ k = none := by
      intro γ k
      rcases hd.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.auth γ k <;> simp_all
      · exact Or.inr h3
    have hfrag1 : ∀ γ k, h₁.frag γ k = none ∨ h₃.frag γ k = none := by
      intro γ k
      rcases hd.2.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.frag γ k <;> simp_all
      · exact Or.inr h3
    have hfrag2 : ∀ γ k, h₂.frag γ k = none ∨ h₃.frag γ k = none := by
      intro γ k
      rcases hd.2.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.frag γ k <;> simp_all
      · exact Or.inr h3
    have hcompat1 : ∀ γ k oa v,
        ((h₁.auth γ k = some oa ∧ h₃.frag γ k = some v) ∨
         (h₃.auth γ k = some oa ∧ h₁.frag γ k = some v)) → oa = some v := by
      intro γ k oa v h
      apply hd.2.2.2.1 γ k oa v
      rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      ·exact Or.inl ⟨by dsimp [union]; rw [ha], hf⟩
      · exact Or.inr ⟨ha, by dsimp [union]; rw [hf]⟩
    have hcompat2 : ∀ γ k oa v,
        ((h₂.auth γ k = some oa ∧ h₃.frag γ k = some v) ∨
         (h₃.auth γ k = some oa ∧ h₂.frag γ k = some v)) → oa = some v := by
      intro γ k oa v h
      apply hd.2.2.2.1 γ k oa v
      rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      · rcases hd12.2.1 γ k with h1 | h2
        · exact Or.inl ⟨by dsimp [union]; rw [h1, ha], hf⟩
        · rw [ha] at h2; contradiction
      · rcases hd12.2.2.1 γ k with h1 | h2
        · exact Or.inr ⟨ha, by dsimp [union]; rw [h1, hf]⟩
        · rw [hf] at h2; contradiction
    have hmapped1 : ∀ a, h₁.mapped a = false ∨ h₃.mapped a = false := by
      intro a
      rcases hd.2.2.2.2 a with hu | h3
      · dsimp [union] at hu; cases h : h₁.mapped a <;> simp_all
      · exact Or.inr h3
    have hmapped2 : ∀ a, h₂.mapped a = false ∨ h₃.mapped a = false := by
      intro a
      rcases hd.2.2.2.2 a with hu | h3
      · dsimp [union] at hu; cases h : h₁.mapped a <;> simp_all
      · exact Or.inr h3
    exact ⟨⟨hphys1, hauth1, hfrag1, hcompat1, hmapped1⟩, ⟨hphys2, hauth2, hfrag2, hcompat2, hmapped2⟩⟩
  · rintro ⟨hd1, hd2⟩
    refine ⟨fun a => ?_, fun γ k => ?_, fun γ k => ?_, fun γ k oa v h => ?_, fun a => ?_⟩
    · dsimp [union]
      cases h : h₁.phys a with
      | none => exact hd2.1 a
      | some c =>
        rcases hd1.1 a with h1 | h3 | ⟨b, h1, h3⟩
        · rw [h] at h1; contradiction
        · exact Or.inr (Or.inl h3)
        · rw [h] at h1; exact Or.inr (Or.inr ⟨b, h1, h3⟩)
    · dsimp [union]
      cases h : h₁.auth γ k with
      | none => exact hd2.2.1 γ k
      | some oa =>
        rcases hd1.2.1 γ k with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3
    · dsimp [union]
      cases h : h₁.frag γ k with
      | none => exact hd2.2.2.1 γ k
      | some v =>
        rcases hd1.2.2.1 γ k with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3
    · rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      · dsimp [union] at ha
        cases h1 : h₁.auth γ k with
        | none =>
          rw [h1] at ha
          exact hd2.2.2.2.1 γ k oa v (Or.inl ⟨ha, hf⟩)
        | some oa' =>
          rw [h1] at ha; cases ha
          exact hd1.2.2.2.1 γ k oa v (Or.inl ⟨h1, hf⟩)
      · dsimp [union] at hf
        cases h1 : h₁.frag γ k with
        | none =>
          rw [h1] at hf
          exact hd2.2.2.2.1 γ k oa v (Or.inr ⟨ha, hf⟩)
        | some v' =>
          rw [h1] at hf; cases hf
          exact hd1.2.2.2.1 γ k oa v (Or.inr ⟨ha, h1⟩)
    · dsimp [union]
      cases h : h₁.mapped a with
      | false => exact hd2.2.2.2.2 a
      | true =>
        rcases hd1.2.2.2.2 a with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3

theorem disjoint_union_right {h₁ h₂ h₃ : Heap} (hd23 : h₂.Disjoint h₃) :
    h₁.Disjoint (h₂.union h₃) ↔ h₁.Disjoint h₂ ∧ h₁.Disjoint h₃ := by
  constructor
  · intro hd
    have hd' := (disjoint_union_left hd23).mp hd.symm
    exact ⟨hd'.1.symm, hd'.2.symm⟩
  · rintro ⟨hd1, hd2⟩
    exact ((disjoint_union_left hd23).mpr ⟨hd1.symm, hd2.symm⟩).symm

/-- Two read-write singleton heaps are disjoint if and only if their addresses are distinct. -/
theorem disjoint_singleton_iff (a₁ a₂ : BitVec 64) (v₁ v₂ : BitVec 8) :
    (Heap.singleton a₁ v₁).Disjoint (Heap.singleton a₂ v₂) ↔ a₁ ≠ a₂ := by
  constructor
  · intro hd heq
    subst heq
    have ha := hd.1 a₁
    simp [Heap.singleton] at ha
  · intro hne
    refine ⟨fun x => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl,
      fun _ _ _ _ h => (by rcases h with ⟨h1, _⟩ | ⟨_, h2⟩ <;> contradiction),
      fun _ => Or.inl rfl⟩
    by_cases hx1 : x = a₁ <;> simp [Heap.singleton, hx1, hne]

theorem GhostValid.of_phys {h : Heap}
    (ha : h.auth = fun _ _ => none := by rfl)
    (hf : h.frag = fun _ _ => none := by rfl) :
    h.GhostValid :=
  ⟨0, fun γ _ k => ⟨congrFun (congrFun ha γ) k, congrFun (congrFun hf γ) k⟩⟩

theorem GhostValid.empty : Heap.empty.GhostValid :=
  GhostValid.of_phys

theorem GhostValid.union {h₁ h₂ : Heap}
    (hv1 : h₁.GhostValid) (hv2 : h₂.GhostValid) :
    (h₁.union h₂).GhostValid := by
  rcases hv1 with ⟨b1, hb1⟩
  rcases hv2 with ⟨b2, hb2⟩
  refine ⟨max b1 b2, fun γ hγ k => ?_⟩
  have ⟨ha1, hf1⟩ := hb1 γ (Nat.le_trans (Nat.le_max_left b1 b2) hγ) k
  have ⟨ha2, hf2⟩ := hb2 γ (Nat.le_trans (Nat.le_max_right b1 b2) hγ) k
  dsimp [Heap.union]
  rw [ha1, ha2, hf1, hf2]
  exact ⟨rfl, rfl⟩

theorem GhostValid.of_union_left {h₁ h₂ : Heap} (hv : (h₁.union h₂).GhostValid) :
    h₁.GhostValid := by
  rcases hv with ⟨b, hb⟩
  refine ⟨b, fun γ hγ k => ?_⟩
  have ⟨hau, hfu⟩ := hb γ hγ k
  dsimp [Heap.union] at hau hfu
  constructor
  · cases h : h₁.auth γ k with
    | none => rfl
    | some _ => rw [h] at hau; contradiction
  · cases h : h₁.frag γ k with
    | none => rfl
    | some _ => rw [h] at hfu; contradiction

theorem GhostValid.of_union_right {h₁ h₂ : Heap} (hv : (h₁.union h₂).GhostValid) :
    h₂.GhostValid := by
  rcases hv with ⟨b, hb⟩
  refine ⟨b, fun γ hγ k => ?_⟩
  have ⟨hau, hfu⟩ := hb γ hγ k
  dsimp [Heap.union] at hau hfu
  constructor
  · cases h1 : h₁.auth γ k with
    | none => rw [h1] at hau; exact hau
    | some _ => rw [h1] at hau; contradiction
  · cases h1 : h₁.frag γ k with
    | none => rw [h1] at hfu; exact hfu
    | some _ => rw [h1] at hfu; contradiction

theorem Matches.of_phys {h : Heap} {m : Memory}
    (ha : h.auth = fun _ _ => none := by rfl)
    (hf : h.frag = fun _ _ => none := by rfl)
    (hp : ∀ a c, h.phys a = some c →
      match c with
      | .rw b => m.read8 a = b ∧ m.perm a = some Perm.rw ∧ m.isLazyFree a = false
      | .ro b => m.read8 a = b ∧ (m.perm a).r = true ∧ m.isLazyFree a = false
      | .protNone b => m.read8 a = b ∧ m.perm a = some Perm.protNone ∧ m.isLazyFree a = false
      | .lazy => m.perm a = some Perm.rw
      | .protNoneLazy => m.perm a = some Perm.protNone)
    (hm : h.mapped = fun _ => false := by rfl) :
    h.Matches m :=
  ⟨hp, GhostValid.of_phys ha hf, fun a hmap => by rw [congrFun hm a] at hmap; contradiction⟩

theorem Matches.empty (m : Memory) : Heap.empty.Matches m :=
  Matches.of_phys rfl rfl (fun _ _ h => by contradiction)

theorem Matches.union {h₁ h₂ : Heap} {m : Memory}
    (hm1 : h₁.Matches m) (hm2 : h₂.Matches m) :
    (h₁.union h₂).Matches m := by
  refine ⟨fun a c h => ?_, GhostValid.union hm1.2.1 hm2.2.1, fun a h => ?_⟩
  · dsimp [Heap.union] at h
    cases h1 : h₁.phys a with
    | none =>
      rw [h1] at h
      exact hm2.1 a c h
    | some c' =>
      rw [h1] at h; cases h
      exact hm1.1 a c h1
  · dsimp [Heap.union] at h
    cases h1 : h₁.mapped a with
    | false =>
      rw [h1, Bool.false_or] at h
      exact hm2.2.2 a h
    | true =>
      exact hm1.2.2 a h1

theorem Matches.of_union_left {h₁ h₂ : Heap} {m : Memory}
    (hm : (h₁.union h₂).Matches m) :
    h₁.Matches m :=
  ⟨fun a c h1 => hm.1 a c (by dsimp [Heap.union]; rw [h1]),
    GhostValid.of_union_left hm.2.1,
    fun a h1 => hm.2.2 a (by dsimp [Heap.union]; rw [h1, Bool.true_or])⟩

theorem Matches.of_union_right {h₁ h₂ : Heap} {m : Memory}
    (hd : h₁.Disjoint h₂) (hm : (h₁.union h₂).Matches m) :
    h₂.Matches m := by
  refine ⟨fun a c h2 => ?_, GhostValid.of_union_right hm.2.1,
    fun a h2 => hm.2.2 a (by dsimp [Heap.union]; rw [h2, Bool.or_true])⟩
  apply hm.1 a c
  rw [union_comm_of_disjoint hd]
  dsimp [Heap.union]; rw [h2]

end Heap

/-- Weakening `m ⊨ P ∗ (F ∗ R)` to `m ⊨ ⌜True⌝ ∗ R`. -/
theorem satisfies_true_sepConj_frame {P F R : SepProp} {m : Memory}
    (h : m ⊨ P ∗ (F ∗ R)) : m ⊨ (⌜True⌝ : SepProp) ∗ R := by
  obtain ⟨_, hh, hm⟩ := SepProp.satisfies_iff.mp h
  obtain ⟨_, _, hd1, rfl, _, h23⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨_, h₃, hd2, rfl, _, hr⟩ := SepProp.holds_sepConj_iff.mp h23
  exact SepProp.satisfies_iff.mpr ⟨h₃, SepProp.holds_sepConj_iff.mpr ⟨Heap.empty, h₃,
    Heap.disjoint_empty_left h₃, (Heap.union_empty_left h₃).symm,
    SepProp.holds_pure_iff.mpr ⟨rfl, trivial⟩, hr⟩,
    Heap.Matches.of_union_right hd2 (Heap.Matches.of_union_right hd1 hm)⟩

/-- Dropping the middle frame `F` in `m ⊨ P ∗ (F ∗ R)` under sub-heap satisfaction. -/
theorem Satisfies.drop_mid {P F R : SepProp} {m : Memory}
    (h : m ⊨ P ∗ (F ∗ R)) : m ⊨ P ∗ R := by
  obtain ⟨_, hh, hm⟩ := SepProp.satisfies_iff.mp h
  obtain ⟨h₁, _, hd1, rfl, hp, h23⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨_, h₃, hd2, rfl, _, hr⟩ := SepProp.holds_sepConj_iff.mp h23
  rcases (Heap.disjoint_union_right hd2).mp hd1 with ⟨_, hd13⟩
  have hm23 := Heap.Matches.of_union_right hd1 hm
  exact SepProp.satisfies_iff.mpr ⟨h₁.union h₃,
    SepProp.holds_sepConj_iff.mpr ⟨h₁, h₃, hd13, rfl, hp, hr⟩,
    Heap.Matches.union (Heap.Matches.of_union_left hm) (Heap.Matches.of_union_right hd2 hm23)⟩

theorem Entails.refl (P : SepProp) : P ⊢ P := SepProp.entails_iff.mpr fun _ h => h

theorem Entails.trans {P Q R : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ R) : P ⊢ R :=
  SepProp.entails_iff.mpr fun h hp => SepProp.entails_iff.mp h2 h (SepProp.entails_iff.mp h1 h hp)

theorem Satisfies.mono {P Q : SepProp} (h : P ⊢ Q) {m : Memory} (hm : m ⊨ P) : m ⊨ Q := by
  rcases SepProp.satisfies_iff.mp hm with ⟨hp, hP, hM⟩
  exact SepProp.satisfies_iff.mpr ⟨hp, SepProp.entails_iff.mp h hp hP, hM⟩

theorem bupd_intro (P : SepProp) : P ⊢ |==> P :=
  SepProp.entails_iff.mpr fun h hp => SepProp.holds_bupd_iff.mpr fun _ _ hd hm => ⟨h, hp, hd, hm⟩

theorem bupd_mono {P Q : SepProp} (h : P ⊢ Q) : (|==> P) ⊢ |==> Q := by
  refine SepProp.entails_iff.mpr fun hp hbp => SepProp.holds_bupd_iff.mpr fun m hf hd hm => ?_
  rcases SepProp.holds_bupd_iff.mp hbp m hf hd hm with ⟨hp', hP, hd', hm'⟩
  exact ⟨hp', SepProp.entails_iff.mp h hp' hP, hd', hm'⟩

theorem bupd_trans (P : SepProp) : (|==> |==> P) ⊢ |==> P := by
  refine SepProp.entails_iff.mpr fun hp hbp => SepProp.holds_bupd_iff.mpr fun m hf hd hm => ?_
  rcases SepProp.holds_bupd_iff.mp hbp m hf hd hm with ⟨hp', hbp', hd', hm'⟩
  exact SepProp.holds_bupd_iff.mp hbp' m hf hd' hm'

theorem bupd_frame_r (P R : SepProp) : ((|==> P) ∗ R) ⊢ |==> (P ∗ R) := by
  refine SepProp.entails_iff.mpr fun h hh => SepProp.holds_bupd_iff.mpr fun m hf hd hm => ?_
  obtain ⟨h₁, h₂, hd12, rfl, hbp, hr⟩ := SepProp.holds_sepConj_iff.mp hh
  have ⟨hd1f, hd2f⟩ := (Heap.disjoint_union_left hd12).mp hd
  have hd1_2f : h₁.Disjoint (h₂.union hf) :=
    (Heap.disjoint_union_right hd2f).mpr ⟨hd12, hd1f⟩
  have hm' : (h₁.union (h₂.union hf)).Matches m := by
    rwa [← Heap.union_assoc]
  rcases SepProp.holds_bupd_iff.mp hbp m (h₂.union hf) hd1_2f hm' with ⟨h₁', hp', hd1'_2f, hm1'⟩
  have ⟨hd1'2, hd1'f⟩ := (Heap.disjoint_union_right hd2f).mp hd1'_2f
  refine ⟨h₁'.union h₂, SepProp.holds_sepConj_iff.mpr ⟨h₁', h₂, hd1'2, rfl, hp', hr⟩,
    (Heap.disjoint_union_left hd1'2).mpr ⟨hd1'f, hd2f⟩, ?_⟩
  rwa [Heap.union_assoc]

@[simp, arm64_norm]
theorem satisfies_bupd (P : SepProp) (m : Memory) : (m ⊨ |==> P) ↔ (m ⊨ P) := by
  constructor
  · intro hs
    obtain ⟨h, hbp, hm⟩ := SepProp.satisfies_iff.mp hs
    have hd : h.Disjoint Heap.empty := Heap.disjoint_empty_right h
    have hmu : (h.union Heap.empty).Matches m := by rwa [Heap.union_empty_right]
    rcases SepProp.holds_bupd_iff.mp hbp m Heap.empty hd hmu with ⟨h', hp', _, hm'⟩
    rw [Heap.union_empty_right] at hm'
    exact SepProp.satisfies_iff.mpr ⟨h', hp', hm'⟩
  · exact Satisfies.mono (bupd_intro P)

theorem sepConj_comm (P Q : SepProp) : (P ∗ Q) = (Q ∗ P) := by
  ext h
  simp only [SepProp.holds_sepConj_iff]
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, hp, hq⟩
    exact ⟨h₂, h₁, hd.symm, Heap.union_comm_of_disjoint hd, hq, hp⟩
  · rintro ⟨h₁, h₂, hd, rfl, hq, hp⟩
    exact ⟨h₂, h₁, hd.symm, Heap.union_comm_of_disjoint hd, hp, hq⟩

theorem bupd_frame_l (R P : SepProp) : (R ∗ (|==> P)) ⊢ |==> (R ∗ P) := by
  rw [sepConj_comm R, sepConj_comm R]
  exact bupd_frame_r P R

@[simp, arm64_norm]
theorem sepConj_assoc (P Q R : SepProp) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  ext h
  simp only [SepProp.holds_sepConj_iff]
  constructor
  · rintro ⟨h₁₂, h₃, hd12_3, rfl, ⟨h₁, h₂, hd1_2, rfl, hp, hq⟩, hr⟩
    have ⟨hd1_3, hd2_3⟩ := (Heap.disjoint_union_left hd1_2).mp hd12_3
    exact ⟨h₁, h₂.union h₃, (Heap.disjoint_union_right hd2_3).mpr ⟨hd1_2, hd1_3⟩,
      Heap.union_assoc h₁ h₂ h₃, hp, ⟨h₂, h₃, hd2_3, rfl, hq, hr⟩⟩
  · rintro ⟨h₁, h₂₃, hd1_23, rfl, hp, ⟨h₂, h₃, hd2_3, rfl, hq, hr⟩⟩
    have ⟨hd1_2, hd1_3⟩ := (Heap.disjoint_union_right hd2_3).mp hd1_23
    exact ⟨h₁.union h₂, h₃, (Heap.disjoint_union_left hd1_2).mpr ⟨hd1_3, hd2_3⟩,
      (Heap.union_assoc h₁ h₂ h₃).symm, ⟨h₁, h₂, hd1_2, rfl, hp, hq⟩, hr⟩

/-- Left commutativity of separating conjunction: `P ∗ (Q ∗ R) = Q ∗ (P ∗ R)`. -/
theorem sepConj_left_comm (P Q R : SepProp) : (P ∗ (Q ∗ R)) = (Q ∗ (P ∗ R)) := by
  rw [← sepConj_assoc, sepConj_comm P Q, sepConj_assoc]

/-- Right commutativity of separating conjunction: `(P ∗ Q) ∗ R = (P ∗ R) ∗ Q`. -/
theorem sepConj_right_comm (P Q R : SepProp) : ((P ∗ Q) ∗ R) = ((P ∗ R) ∗ Q) := by
  rw [sepConj_assoc, sepConj_comm Q R, ← sepConj_assoc]

instance instAssociativeSepConj : Std.Associative SepProp.sepConj where
  assoc := sepConj_assoc

instance instCommutativeSepConj : Std.Commutative SepProp.sepConj where
  comm := sepConj_comm

theorem Entails.of_eq {P Q : SepProp} (heq : P = Q := by ac_rfl) : P ⊢ Q :=
  heq ▸ Entails.refl P

theorem Satisfies.of_eq {P Q : SepProp} {m : Memory}
    (h : m ⊨ P) (heq : P = Q := by ac_rfl) : m ⊨ Q :=
  heq ▸ h

@[simp, arm64_norm]
theorem emp_sepConj (P : SepProp) : (SepProp.emp ∗ P) = P := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_emp_iff]
  constructor
  · rintro ⟨h₁, h₂, _, rfl, rfl, hp⟩
    simpa using hp
  · intro hp
    exact ⟨Heap.empty, h, Heap.disjoint_empty_left h, (Heap.union_empty_left h).symm, rfl, hp⟩

@[simp, arm64_norm]
theorem sepConj_emp (P : SepProp) : (P ∗ SepProp.emp) = P := by
  rw [sepConj_comm, emp_sepConj]

@[simp, arm64_norm]
theorem pure_true : (⌜True⌝ : SepProp) = SepProp.emp := by
  ext h
  simp only [SepProp.holds_pure_iff, SepProp.holds_emp_iff, and_true]

@[simp, arm64_norm]
theorem satisfies_emp (m : Memory) : (m ⊨ SepProp.emp) :=
  SepProp.satisfies_iff.mpr ⟨Heap.empty, SepProp.holds_emp_iff.mpr rfl, Heap.Matches.empty m⟩

@[simp, arm64_norm]
theorem satisfies_pure (φ : Prop) (m : Memory) : (m ⊨ ⌜φ⌝) ↔ φ := by
  simp only [SepProp.satisfies_iff, SepProp.holds_pure_iff]
  constructor
  · rintro ⟨_, ⟨_, hφ⟩, _⟩; exact hφ
  · intro hφ; exact ⟨Heap.empty, ⟨rfl, hφ⟩, Heap.Matches.empty m⟩

theorem pure_sepConj (φ : Prop) (P : SepProp) : (⌜φ⌝ ∗ P) = ⟨fun h => φ ∧ P h⟩ := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_pure_iff]
  constructor
  · rintro ⟨h₁, h₂, _, rfl, ⟨rfl, hφ⟩, hp⟩
    exact ⟨hφ, by simpa using hp⟩
  · rintro ⟨hφ, hp⟩
    exact ⟨Heap.empty, h, Heap.disjoint_empty_left h, (Heap.union_empty_left h).symm, ⟨rfl, hφ⟩, hp⟩

theorem sepConj_pure (P : SepProp) (φ : Prop) : (P ∗ ⌜φ⌝) = ⟨fun h => P h ∧ φ⟩ := by
  rw [sepConj_comm, pure_sepConj]
  ext h
  exact And.comm

@[simp, arm64_norm]
theorem satisfies_pure_sepConj (φ : Prop) (P : SepProp) (m : Memory) :
    (m ⊨ ⌜φ⌝ ∗ P) ↔ (φ ∧ (m ⊨ P)) := by
  simp only [SepProp.satisfies_iff, pure_sepConj]
  constructor
  · rintro ⟨h, ⟨hφ, hp⟩, hm⟩
    exact ⟨hφ, ⟨h, hp, hm⟩⟩
  · rintro ⟨hφ, ⟨h, hp, hm⟩⟩
    exact ⟨h, ⟨hφ, hp⟩, hm⟩

@[simp, arm64_norm]
theorem satisfies_sepConj_pure (P : SepProp) (φ : Prop) (m : Memory) :
    (m ⊨ P ∗ ⌜φ⌝) ↔ ((m ⊨ P) ∧ φ) := by
  rw [sepConj_comm, satisfies_pure_sepConj, And.comm]

@[simp, arm64_norm]
theorem satisfies_sepConj_pure_assoc (P Q : SepProp) (φ : Prop) (m : Memory) :
    (m ⊨ P ∗ (⌜φ⌝ ∗ Q)) ↔ (φ ∧ (m ⊨ P ∗ Q)) := by
  rw [sepConj_left_comm, satisfies_pure_sepConj]

theorem sepConj_mono {P P' Q Q' : SepProp} (hp : P ⊢ P') (hq : Q ⊢ Q') :
    (P ∗ Q) ⊢ (P' ∗ Q') := by
  refine SepProp.entails_iff.mpr fun h hh => ?_
  obtain ⟨h₁, h₂, hd, rfl, h1, h2⟩ := SepProp.holds_sepConj_iff.mp hh
  exact SepProp.holds_sepConj_iff.mpr
    ⟨h₁, h₂, hd, rfl, SepProp.entails_iff.mp hp h₁ h1, SepProp.entails_iff.mp hq h₂ h2⟩

theorem sepConj_mono_left {P P' Q : SepProp} (hp : P ⊢ P') : (P ∗ Q) ⊢ (P' ∗ Q) :=
  sepConj_mono hp (Entails.refl Q)

theorem sepConj_mono_right {P Q Q' : SepProp} (hq : Q ⊢ Q') : (P ∗ Q) ⊢ (P ∗ Q') :=
  sepConj_mono (Entails.refl P) hq

universe u

theorem Entails.sepExists_intro {α : Sort u} {P : α → SepProp} (x : α) :
    P x ⊢ (∃∗ y, P y) :=
  SepProp.entails_iff.mpr fun _ hx => SepProp.holds_sepExists_iff.mpr ⟨x, hx⟩

theorem Entails.sepExists_right {α : Sort u} {P : SepProp} {Q : α → SepProp}
    (x : α) (h : P ⊢ Q x) : P ⊢ (∃∗ y, Q y) :=
  SepProp.entails_iff.mpr fun hp hP =>
    SepProp.holds_sepExists_iff.mpr ⟨x, SepProp.entails_iff.mp h hp hP⟩

theorem Entails.sepExists_elim {α : Sort u} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, P x ⊢ Q) : (∃∗ x, P x) ⊢ Q := by
  refine SepProp.entails_iff.mpr fun hp hh => ?_
  obtain ⟨x, hx⟩ := SepProp.holds_sepExists_iff.mp hh
  exact SepProp.entails_iff.mp (h x) hp hx

@[simp, arm64_norm]
theorem sepExists_sepConj_left {α : Sort u} (P : α → SepProp) (Q : SepProp) :
    ((∃∗ x, P x) ∗ Q) = (∃∗ x, P x ∗ Q) := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_sepExists_iff]
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, ⟨x, hpx⟩, hq⟩
    exact ⟨x, h₁, h₂, hd, rfl, hpx, hq⟩
  · rintro ⟨x, h₁, h₂, hd, rfl, hpx, hq⟩
    exact ⟨h₁, h₂, hd, rfl, ⟨x, hpx⟩, hq⟩

@[simp, arm64_norm]
theorem sepExists_sepConj_right {α : Sort u} (P : SepProp) (Q : α → SepProp) :
    (P ∗ (∃∗ x, Q x)) = (∃∗ x, P ∗ Q x) := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_sepExists_iff]
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, hp, ⟨x, hqx⟩⟩
    exact ⟨x, h₁, h₂, hd, rfl, hp, hqx⟩
  · rintro ⟨x, h₁, h₂, hd, rfl, hp, hqx⟩
    exact ⟨h₁, h₂, hd, rfl, hp, ⟨x, hqx⟩⟩

@[simp, arm64_norm]
theorem satisfies_sepExists {α : Sort u} (P : α → SepProp) (m : Memory) :
    (m ⊨ ∃∗ x, P x) ↔ (∃ x, m ⊨ P x) := by
  simp only [SepProp.satisfies_iff, SepProp.holds_sepExists_iff]
  constructor
  · rintro ⟨h, ⟨x, hpx⟩, hm⟩
    exact ⟨x, h, hpx, hm⟩
  · rintro ⟨x, h, hpx, hm⟩
    exact ⟨h, ⟨x, hpx⟩, hm⟩

theorem Entails.pure_left {φ : Prop} {P Q : SepProp} (h : φ → (P ⊢ Q)) :
    (⌜φ⌝ ∗ P) ⊢ Q := by
  refine SepProp.entails_iff.mpr fun hp hP => ?_
  rw [pure_sepConj] at hP
  exact SepProp.entails_iff.mp (h hP.1) hp hP.2

/-- Pure extraction adjunction for `⌜p⌝ ∗ P ⊢ Q`. -/
theorem pure_extract_iff (p : Prop) (P Q : SepProp) :
    ((⌜p⌝ ∗ P) ⊢ Q) ↔ (p → (P ⊢ Q)) :=
  ⟨fun h hp => SepProp.entails_iff.mpr fun h₀ hP =>
    SepProp.entails_iff.mp h h₀ (by rw [pure_sepConj]; exact ⟨hp, hP⟩), Entails.pure_left⟩

theorem Entails.pure_left_only {φ : Prop} {Q : SepProp} (h : φ → (SepProp.emp ⊢ Q)) :
    ⌜φ⌝ ⊢ Q := by
  refine SepProp.entails_iff.mpr fun hp hh => ?_
  obtain ⟨he, hφ⟩ := SepProp.holds_pure_iff.mp hh
  exact SepProp.entails_iff.mp (h hφ) hp (SepProp.holds_emp_iff.mpr he)

theorem Entails.pure_right {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ (⌜φ⌝ ∗ Q) := by
  refine SepProp.entails_iff.mpr fun hp hP => ?_
  rw [pure_sepConj]
  exact ⟨hφ, SepProp.entails_iff.mp h hp hP⟩

theorem Entails.pure_right_only {φ : Prop} {P : SepProp} (hφ : φ) (h : P ⊢ SepProp.emp) :
    P ⊢ ⌜φ⌝ :=
  SepProp.entails_iff.mpr fun hp hP =>
    SepProp.holds_pure_iff.mpr ⟨SepProp.holds_emp_iff.mp (SepProp.entails_iff.mp h hp hP), hφ⟩

theorem Entails.top_right {P Q : SepProp} (hQ : ∀ h, Q h) : P ⊢ Q :=
  SepProp.entails_iff.mpr fun _ _ => hQ _

section PureSplit
variable {α : Type} {prog : Program} {e : BitVec 64} (spec : Spec α)

/-- Drop a leading trivial pure guard `⌜True⌝ ∗` from a `subroutine_ok` precondition. -/
theorem subroutine_ok_of_pure_true
    (h : subroutine_ok prog e { spec with pre := fun x s => ⌜True⌝ ∗ spec.pre x s }) :
    subroutine_ok prog e spec := by
  refine subroutine_ok_iff.2 fun x R s0 hpc hrun hpre hsp => reaches_outcome_iff.2 fun hL => ?_
  exact (reaches_outcome_iff.1 (subroutine_ok_iff.1 h x R s0 hpc hrun
    (by rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨trivial, hpre⟩) hsp) hL).imp fun _ h => h

/-- Case-split a `subroutine_ok` contract with pure guard `⌜P x⌝` on a proposition `Q x`. -/
theorem subroutine_ok_pure_split (P Q : α → Prop)
    (h1 : subroutine_ok prog e { spec with pre := fun x s => ⌜P x ∧ Q x⌝ ∗ spec.pre x s })
    (h2 : subroutine_ok prog e { spec with pre := fun x s => ⌜P x ∧ ¬Q x⌝ ∗ spec.pre x s }) :
    subroutine_ok prog e { spec with pre := fun x s => ⌜P x⌝ ∗ spec.pre x s } := by
  refine subroutine_ok_iff.2 fun x R s0 hpc hrun hpre hsp => reaches_outcome_iff.2 fun hL => ?_
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  by_cases hq : Q x
  · exact (reaches_outcome_iff.1 (subroutine_ok_iff.1 h1 x R s0 hpc hrun
      (by rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hpre.1, hq⟩, hpre.2⟩) hsp) hL).imp fun _ h => h
  · exact (reaches_outcome_iff.1 (subroutine_ok_iff.1 h2 x R s0 hpc hrun
      (by rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hpre.1, hq⟩, hpre.2⟩) hsp) hL).imp fun _ h => h

/-- Strengthen the pure guard `⌜P x⌝` to `⌜Q x⌝` in a `subroutine_ok` precondition given `∀ x, Q x → P x`. -/
theorem subroutine_ok_pure_weaken (P Q : α → Prop) (hPQ : ∀ x, Q x → P x)
    (h : subroutine_ok prog e { spec with pre := fun x s => ⌜P x⌝ ∗ spec.pre x s }) :
    subroutine_ok prog e { spec with pre := fun x s => ⌜Q x⌝ ∗ spec.pre x s } := by
  refine subroutine_ok_iff.2 fun x R s0 hpc hrun hpre hsp => reaches_outcome_iff.2 fun hL => ?_
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact (reaches_outcome_iff.1 (subroutine_ok_iff.1 h x R s0 hpc hrun
    (by rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hPQ x hpre.1, hpre.2⟩) hsp) hL).imp fun _ h => h

end PureSplit

/-! ## Scalar IEEE-754 Floating-Point Normalization & Algebraic Lemmas -/

@[simp, arm64_norm, wp_norm]
theorem evalFp1Op64_fmov (x : BitVec 64) : evalFp1Op64 0#6 x = x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op64_fabs (x : BitVec 64) : evalFp1Op64 1#6 x = fpAbs64 x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op64_fneg (x : BitVec 64) : evalFp1Op64 2#6 x = fpNeg64 x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op64_fsqrt (x : BitVec 64) : evalFp1Op64 3#6 x = fpSqrt64 x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op64_frintn (x : BitVec 64) : evalFp1Op64 8#6 x = fpRint64 .RNE x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op64_frintp (x : BitVec 64) : evalFp1Op64 9#6 x = fpRint64 .RTP x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op64_frintm (x : BitVec 64) : evalFp1Op64 10#6 x = fpRint64 .RTN x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op64_frintz (x : BitVec 64) : evalFp1Op64 11#6 x = fpRint64 .RTZ x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op64_frinta (x : BitVec 64) : evalFp1Op64 12#6 x = fpRint64 .RNA x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op64_frintx (x : BitVec 64) : evalFp1Op64 14#6 x = fpRint64 .RNE x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op64_frinti (x : BitVec 64) : evalFp1Op64 15#6 x = fpRint64 .RNE x := rfl

@[simp, arm64_norm, wp_norm]
theorem evalFp1Op32_fmov (x : BitVec 32) : evalFp1Op32 0#6 x = x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op32_fabs (x : BitVec 32) : evalFp1Op32 1#6 x = fpAbs32 x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op32_fneg (x : BitVec 32) : evalFp1Op32 2#6 x = fpNeg32 x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op32_fsqrt (x : BitVec 32) : evalFp1Op32 3#6 x = fpSqrt32 x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op32_frintn (x : BitVec 32) : evalFp1Op32 8#6 x = fpRint32 .RNE x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op32_frintp (x : BitVec 32) : evalFp1Op32 9#6 x = fpRint32 .RTP x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op32_frintm (x : BitVec 32) : evalFp1Op32 10#6 x = fpRint32 .RTN x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op32_frintz (x : BitVec 32) : evalFp1Op32 11#6 x = fpRint32 .RTZ x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op32_frinta (x : BitVec 32) : evalFp1Op32 12#6 x = fpRint32 .RNA x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op32_frintx (x : BitVec 32) : evalFp1Op32 14#6 x = fpRint32 .RNE x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1Op32_frinti (x : BitVec 32) : evalFp1Op32 15#6 x = fpRint32 .RNE x := rfl

@[simp, arm64_norm, wp_norm]
theorem evalFp2Op64_fmul (x y : BitVec 64) : evalFp2Op64 0#4 x y = fpMul64 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op64_fdiv (x y : BitVec 64) : evalFp2Op64 1#4 x y = fpDiv64 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op64_fadd (x y : BitVec 64) : evalFp2Op64 2#4 x y = fpAdd64 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op64_fsub (x y : BitVec 64) : evalFp2Op64 3#4 x y = fpSub64 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op64_fmax (x y : BitVec 64) : evalFp2Op64 4#4 x y = fpMax64 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op64_fmin (x y : BitVec 64) : evalFp2Op64 5#4 x y = fpMin64 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op64_fmaxnm (x y : BitVec 64) : evalFp2Op64 6#4 x y = fpMaxNm64 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op64_fminnm (x y : BitVec 64) : evalFp2Op64 7#4 x y = fpMinNm64 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op64_fnmul (x y : BitVec 64) : evalFp2Op64 8#4 x y = fpNMul64 x y := rfl

@[simp, arm64_norm, wp_norm]
theorem evalFp2Op32_fmul (x y : BitVec 32) : evalFp2Op32 0#4 x y = fpMul32 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op32_fdiv (x y : BitVec 32) : evalFp2Op32 1#4 x y = fpDiv32 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op32_fadd (x y : BitVec 32) : evalFp2Op32 2#4 x y = fpAdd32 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op32_fsub (x y : BitVec 32) : evalFp2Op32 3#4 x y = fpSub32 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op32_fmax (x y : BitVec 32) : evalFp2Op32 4#4 x y = fpMax32 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op32_fmin (x y : BitVec 32) : evalFp2Op32 5#4 x y = fpMin32 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op32_fmaxnm (x y : BitVec 32) : evalFp2Op32 6#4 x y = fpMaxNm32 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op32_fminnm (x y : BitVec 32) : evalFp2Op32 7#4 x y = fpMinNm32 x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2Op32_fnmul (x y : BitVec 32) : evalFp2Op32 8#4 x y = fpNMul32 x y := rfl

@[simp, arm64_norm, wp_norm]
theorem evalFp3Op64_fmadd (vn vm va : BitVec 64) :
    evalFp3Op64 false false vn vm va = fpFma64 va vn vm := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp3Op64_fmsub (vn vm va : BitVec 64) :
    evalFp3Op64 false true vn vm va = fpFma64 va (fpNeg64 vn) vm := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp3Op64_fnmadd (vn vm va : BitVec 64) :
    evalFp3Op64 true false vn vm va = fpFma64 (fpNeg64 va) (fpNeg64 vn) vm := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp3Op64_fnmsub (vn vm va : BitVec 64) :
    evalFp3Op64 true true vn vm va = fpFma64 (fpNeg64 va) vn vm := rfl

@[simp, arm64_norm, wp_norm]
theorem evalFp3Op32_fmadd (vn vm va : BitVec 32) :
    evalFp3Op32 false false vn vm va = fpFma32 va vn vm := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp3Op32_fmsub (vn vm va : BitVec 32) :
    evalFp3Op32 false true vn vm va = fpFma32 va (fpNeg32 vn) vm := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp3Op32_fnmadd (vn vm va : BitVec 32) :
    evalFp3Op32 true false vn vm va = fpFma32 (fpNeg32 va) (fpNeg32 vn) vm := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp3Op32_fnmsub (vn vm va : BitVec 32) :
    evalFp3Op32 true true vn vm va = fpFma32 (fpNeg32 va) vn vm := rfl

@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags64_fmov (x : BitVec 64) : evalFp1OpFlags64 0#6 x = 0#32 := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags64_fabs (x : BitVec 64) : evalFp1OpFlags64 1#6 x = 0#32 := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags64_fneg (x : BitVec 64) : evalFp1OpFlags64 2#6 x = 0#32 := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags64_fsqrt (x : BitVec 64) : evalFp1OpFlags64 3#6 x = fpSqrt64Flags x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags64_frintn (x : BitVec 64) : evalFp1OpFlags64 8#6 x = fpRint64Flags false x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags64_frintp (x : BitVec 64) : evalFp1OpFlags64 9#6 x = fpRint64Flags false x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags64_frintm (x : BitVec 64) : evalFp1OpFlags64 10#6 x = fpRint64Flags false x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags64_frintz (x : BitVec 64) : evalFp1OpFlags64 11#6 x = fpRint64Flags false x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags64_frinta (x : BitVec 64) : evalFp1OpFlags64 12#6 x = fpRint64Flags false x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags64_frintx (x : BitVec 64) : evalFp1OpFlags64 14#6 x = fpRint64Flags true x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags64_frinti (x : BitVec 64) : evalFp1OpFlags64 15#6 x = fpRint64Flags false x := rfl

@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags32_fmov (x : BitVec 32) : evalFp1OpFlags32 0#6 x = 0#32 := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags32_fabs (x : BitVec 32) : evalFp1OpFlags32 1#6 x = 0#32 := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags32_fneg (x : BitVec 32) : evalFp1OpFlags32 2#6 x = 0#32 := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags32_fsqrt (x : BitVec 32) : evalFp1OpFlags32 3#6 x = fpSqrt32Flags x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags32_frintn (x : BitVec 32) : evalFp1OpFlags32 8#6 x = fpRint32Flags false x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags32_frintp (x : BitVec 32) : evalFp1OpFlags32 9#6 x = fpRint32Flags false x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags32_frintm (x : BitVec 32) : evalFp1OpFlags32 10#6 x = fpRint32Flags false x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags32_frintz (x : BitVec 32) : evalFp1OpFlags32 11#6 x = fpRint32Flags false x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags32_frinta (x : BitVec 32) : evalFp1OpFlags32 12#6 x = fpRint32Flags false x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags32_frintx (x : BitVec 32) : evalFp1OpFlags32 14#6 x = fpRint32Flags true x := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp1OpFlags32_frinti (x : BitVec 32) : evalFp1OpFlags32 15#6 x = fpRint32Flags false x := rfl

@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags64_fmul (x y : BitVec 64) : evalFp2OpFlags64 0#4 x y = fpMul64Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags64_fdiv (x y : BitVec 64) : evalFp2OpFlags64 1#4 x y = fpDiv64Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags64_fadd (x y : BitVec 64) : evalFp2OpFlags64 2#4 x y = fpAdd64Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags64_fsub (x y : BitVec 64) : evalFp2OpFlags64 3#4 x y = fpSub64Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags64_fmax (x y : BitVec 64) : evalFp2OpFlags64 4#4 x y = fpMinMax64Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags64_fmin (x y : BitVec 64) : evalFp2OpFlags64 5#4 x y = fpMinMax64Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags64_fmaxnm (x y : BitVec 64) : evalFp2OpFlags64 6#4 x y = fpMinMax64Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags64_fminnm (x y : BitVec 64) : evalFp2OpFlags64 7#4 x y = fpMinMax64Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags64_fnmul (x y : BitVec 64) : evalFp2OpFlags64 8#4 x y = fpNMul64Flags x y := rfl

@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags32_fmul (x y : BitVec 32) : evalFp2OpFlags32 0#4 x y = fpMul32Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags32_fdiv (x y : BitVec 32) : evalFp2OpFlags32 1#4 x y = fpDiv32Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags32_fadd (x y : BitVec 32) : evalFp2OpFlags32 2#4 x y = fpAdd32Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags32_fsub (x y : BitVec 32) : evalFp2OpFlags32 3#4 x y = fpSub32Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags32_fmax (x y : BitVec 32) : evalFp2OpFlags32 4#4 x y = fpMinMax32Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags32_fmin (x y : BitVec 32) : evalFp2OpFlags32 5#4 x y = fpMinMax32Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags32_fmaxnm (x y : BitVec 32) : evalFp2OpFlags32 6#4 x y = fpMinMax32Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags32_fminnm (x y : BitVec 32) : evalFp2OpFlags32 7#4 x y = fpMinMax32Flags x y := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp2OpFlags32_fnmul (x y : BitVec 32) : evalFp2OpFlags32 8#4 x y = fpNMul32Flags x y := rfl

@[simp, arm64_norm, wp_norm]
theorem evalFp3OpFlags64_fmadd (vn vm va : BitVec 64) :
    evalFp3OpFlags64 false false vn vm va = fpFma64Flags va vn vm := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp3OpFlags64_fmsub (vn vm va : BitVec 64) :
    evalFp3OpFlags64 false true vn vm va = fpFma64Flags va (fpNeg64 vn) vm := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp3OpFlags64_fnmadd (vn vm va : BitVec 64) :
    evalFp3OpFlags64 true false vn vm va = fpFma64Flags (fpNeg64 va) (fpNeg64 vn) vm := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp3OpFlags64_fnmsub (vn vm va : BitVec 64) :
    evalFp3OpFlags64 true true vn vm va = fpFma64Flags (fpNeg64 va) vn vm := rfl

@[simp, arm64_norm, wp_norm]
theorem evalFp3OpFlags32_fmadd (vn vm va : BitVec 32) :
    evalFp3OpFlags32 false false vn vm va = fpFma32Flags va vn vm := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp3OpFlags32_fmsub (vn vm va : BitVec 32) :
    evalFp3OpFlags32 false true vn vm va = fpFma32Flags va (fpNeg32 vn) vm := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp3OpFlags32_fnmadd (vn vm va : BitVec 32) :
    evalFp3OpFlags32 true false vn vm va = fpFma32Flags (fpNeg32 va) (fpNeg32 vn) vm := rfl
@[simp, arm64_norm, wp_norm]
theorem evalFp3OpFlags32_fnmsub (vn vm va : BitVec 32) :
    evalFp3OpFlags32 true true vn vm va = fpFma32Flags (fpNeg32 va) vn vm := rfl

@[simp, arm64_norm, wp_norm]
theorem fpNeg64_fpNeg64 (x : BitVec 64) : fpNeg64 (fpNeg64 x) = x := by
  change (x ^^^ 0x8000000000000000#64) ^^^ 0x8000000000000000#64 = x
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

@[simp, arm64_norm, wp_norm]
theorem fpAbs64_fpNeg64 (x : BitVec 64) : fpAbs64 (fpNeg64 x) = fpAbs64 x := by
  change (x ^^^ 0x8000000000000000#64) &&& 0x7fffffffffffffff#64 = x &&& 0x7fffffffffffffff#64
  bv_bits

@[simp, arm64_norm, wp_norm]
theorem fpAbs64_fpAbs64 (x : BitVec 64) : fpAbs64 (fpAbs64 x) = fpAbs64 x := by
  change (x &&& 0x7fffffffffffffff#64) &&& 0x7fffffffffffffff#64 = x &&& 0x7fffffffffffffff#64
  rw [BitVec.and_assoc, BitVec.and_self]

@[simp, arm64_norm, wp_norm]
theorem fpNeg32_fpNeg32 (x : BitVec 32) : fpNeg32 (fpNeg32 x) = x := by
  change (x ^^^ 0x80000000#32) ^^^ 0x80000000#32 = x
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

@[simp, arm64_norm, wp_norm]
theorem fpAbs32_fpNeg32 (x : BitVec 32) : fpAbs32 (fpNeg32 x) = fpAbs32 x := by
  change (x ^^^ 0x80000000#32) &&& 0x7fffffff#32 = x &&& 0x7fffffff#32
  bv_bits

@[simp, arm64_norm, wp_norm]
theorem fpAbs32_fpAbs32 (x : BitVec 32) : fpAbs32 (fpAbs32 x) = fpAbs32 x := by
  change (x &&& 0x7fffffff#32) &&& 0x7fffffff#32 = x &&& 0x7fffffff#32
  rw [BitVec.and_assoc, BitVec.and_self]

/-! ### `ConditionHolds` Normalization over `evalFpCmp64` and `evalFpCmp32` -/

/-- Ordered IEEE-754 less-than-or-equal (`a ≤ b`) on 32-bit floats (`false` if either is `NaN`). -/
def fpLe32 (a b : BitVec 32) : Bool :=
  fpEq32 a b || fpLt32 a b

/-- Ordered IEEE-754 less-than-or-equal (`a ≤ b`) on 64-bit floats (`false` if either is `NaN`). -/
def fpLe64 (a b : BitVec 64) : Bool :=
  fpEq64 a b || fpLt64 a b

/-- Ordered IEEE-754 strict greater-than (`a > b`) on 32-bit floats (`false` if either is `NaN`). -/
def fpGt32 (a b : BitVec 32) : Bool :=
  !fpIsNaN32 a && !fpIsNaN32 b && !fpEq32 a b && !fpLt32 a b

/-- Ordered IEEE-754 strict greater-than (`a > b`) on 64-bit floats (`false` if either is `NaN`). -/
def fpGt64 (a b : BitVec 64) : Bool :=
  !fpIsNaN64 a && !fpIsNaN64 b && !fpEq64 a b && !fpLt64 a b

/-- Ordered IEEE-754 greater-than-or-equal (`a ≥ b`) on 32-bit floats (`false` if either is `NaN`). -/
def fpGe32 (a b : BitVec 32) : Bool :=
  !fpIsNaN32 a && !fpIsNaN32 b && !fpLt32 a b

/-- Ordered IEEE-754 greater-than-or-equal (`a ≥ b`) on 64-bit floats (`false` if either is `NaN`). -/
def fpGe64 (a b : BitVec 64) : Bool :=
  !fpIsNaN64 a && !fpIsNaN64 b && !fpLt64 a b

private theorem fpEq64_def (a b : BitVec 64) :
    fpEq64 a b = (!fpIsNaN64 a && !fpIsNaN64 b && ((fpIsZero64 a && fpIsZero64 b) || a == b)) := rfl

private theorem fpLt64_def (a b : BitVec 64) :
    fpLt64 a b =
      (!fpIsNaN64 a && !fpIsNaN64 b && !(fpIsZero64 a && fpIsZero64 b) &&
        (if a.msb != b.msb then a.msb
         else if a.msb then fpAbs64 b < fpAbs64 a
         else fpAbs64 a < fpAbs64 b)) := rfl

private theorem evalFpCmp64_def (sig : Bool) (a b : BitVec 64) :
    evalFpCmp64 sig a b =
      if fpIsNaN64 a || fpIsNaN64 b then
        { n := false, z := false, c := true, v := true }
      else if fpEq64 a b then
        { n := false, z := true, c := true, v := false }
      else if fpLt64 a b then
        { n := true, z := false, c := false, v := false }
      else
        { n := false, z := false, c := true, v := false } := rfl

private theorem fpEq64_not_lt (a b : BitVec 64) : !(fpEq64 a b && fpLt64 a b) = true := by
  rw [fpEq64_def, fpLt64_def]
  by_cases hab : a = b
  · subst hab
    have hlt : decide (fpAbs64 a < fpAbs64 a) = false := by
      rw [decide_eq_false_iff_not]
      exact BitVec.lt_irrefl (fpAbs64 a)
    rw [hlt]
    cases fpIsNaN64 a <;> cases fpIsZero64 a <;> cases (a == a) <;> cases a.msb <;> rfl
  · have hbeq : (a == b) = false := beq_false_of_ne hab
    rw [hbeq]
    cases fpIsNaN64 a <;> cases fpIsNaN64 b <;> cases fpIsZero64 a <;> cases fpIsZero64 b <;> rfl

private theorem fpEq64_of_nan_l {a b : BitVec 64} (h : fpIsNaN64 a = true) : fpEq64 a b = false := by
  simp [fpEq64_def, h]
private theorem fpEq64_of_nan_r {a b : BitVec 64} (h : fpIsNaN64 b = true) : fpEq64 a b = false := by
  simp [fpEq64_def, h]
private theorem fpLt64_of_nan_l {a b : BitVec 64} (h : fpIsNaN64 a = true) : fpLt64 a b = false := by
  simp [fpLt64_def, h]
private theorem fpLt64_of_nan_r {a b : BitVec 64} (h : fpIsNaN64 b = true) : fpLt64 a b = false := by
  simp [fpLt64_def, h]

local macro "fp_cmp64_tac " a:ident b:ident : tactic =>
  `(tactic| (
    have hdisj := fpEq64_not_lt $a $b
    cases hna : fpIsNaN64 $a
    · cases hnb : fpIsNaN64 $b
      · rw [evalFpCmp64_def]
        dsimp only [fpLe64, fpGt64, fpGe64, ConditionHolds]
        rw [hna, hnb]
        revert hdisj
        cases fpEq64 $a $b <;> cases fpLt64 $a $b <;> decide
      · simp [evalFpCmp64_def, fpLe64, fpGt64, fpGe64, ConditionHolds, hna, hnb,
              fpEq64_of_nan_r hnb, fpLt64_of_nan_r hnb]
    · simp [evalFpCmp64_def, fpLe64, fpGt64, fpGe64, ConditionHolds, hna,
            fpEq64_of_nan_l hna, fpLt64_of_nan_l hna]))

@[simp, arm64_norm, wp_norm]
theorem conditionHolds_eq_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .EQ (evalFpCmp64 sig a b) = fpEq64 a b := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_ne_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .NE (evalFpCmp64 sig a b) = !fpEq64 a b := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_cs_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .CS (evalFpCmp64 sig a b) = !fpLt64 a b := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_cc_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .CC (evalFpCmp64 sig a b) = fpLt64 a b := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_mi_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .MI (evalFpCmp64 sig a b) = fpLt64 a b := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_pl_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .PL (evalFpCmp64 sig a b) = !fpLt64 a b := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_vs_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .VS (evalFpCmp64 sig a b) = (fpIsNaN64 a || fpIsNaN64 b) := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_vc_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .VC (evalFpCmp64 sig a b) = (!fpIsNaN64 a && !fpIsNaN64 b) := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_hi_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .HI (evalFpCmp64 sig a b) = !fpLe64 a b := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_ls_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .LS (evalFpCmp64 sig a b) = fpLe64 a b := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_ge_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .GE (evalFpCmp64 sig a b) = fpGe64 a b := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_lt_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .LT (evalFpCmp64 sig a b) = !fpGe64 a b := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_gt_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .GT (evalFpCmp64 sig a b) = fpGt64 a b := by fp_cmp64_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_le_evalFpCmp64 (sig : Bool) (a b : BitVec 64) :
    ConditionHolds .LE (evalFpCmp64 sig a b) = !fpGt64 a b := by fp_cmp64_tac a b

private theorem fpEq32_def (a b : BitVec 32) :
    fpEq32 a b = (!fpIsNaN32 a && !fpIsNaN32 b && ((fpIsZero32 a && fpIsZero32 b) || a == b)) := rfl

private theorem fpLt32_def (a b : BitVec 32) :
    fpLt32 a b =
      (!fpIsNaN32 a && !fpIsNaN32 b && !(fpIsZero32 a && fpIsZero32 b) &&
        (if a.msb != b.msb then a.msb
         else if a.msb then fpAbs32 b < fpAbs32 a
         else fpAbs32 a < fpAbs32 b)) := rfl

private theorem evalFpCmp32_def (sig : Bool) (a b : BitVec 32) :
    evalFpCmp32 sig a b =
      if fpIsNaN32 a || fpIsNaN32 b then
        { n := false, z := false, c := true, v := true }
      else if fpEq32 a b then
        { n := false, z := true, c := true, v := false }
      else if fpLt32 a b then
        { n := true, z := false, c := false, v := false }
      else
        { n := false, z := false, c := true, v := false } := rfl

private theorem fpEq32_not_lt (a b : BitVec 32) : !(fpEq32 a b && fpLt32 a b) = true := by
  rw [fpEq32_def, fpLt32_def]
  by_cases hab : a = b
  · subst hab
    have hlt : decide (fpAbs32 a < fpAbs32 a) = false := by
      rw [decide_eq_false_iff_not]
      exact BitVec.lt_irrefl (fpAbs32 a)
    rw [hlt]
    cases fpIsNaN32 a <;> cases fpIsZero32 a <;> cases (a == a) <;> cases a.msb <;> rfl
  · have hbeq : (a == b) = false := beq_false_of_ne hab
    rw [hbeq]
    cases fpIsNaN32 a <;> cases fpIsNaN32 b <;> cases fpIsZero32 a <;> cases fpIsZero32 b <;> rfl

private theorem fpEq32_of_nan_l {a b : BitVec 32} (h : fpIsNaN32 a = true) : fpEq32 a b = false := by
  simp [fpEq32_def, h]
private theorem fpEq32_of_nan_r {a b : BitVec 32} (h : fpIsNaN32 b = true) : fpEq32 a b = false := by
  simp [fpEq32_def, h]
private theorem fpLt32_of_nan_l {a b : BitVec 32} (h : fpIsNaN32 a = true) : fpLt32 a b = false := by
  simp [fpLt32_def, h]
private theorem fpLt32_of_nan_r {a b : BitVec 32} (h : fpIsNaN32 b = true) : fpLt32 a b = false := by
  simp [fpLt32_def, h]

local macro "fp_cmp32_tac " a:ident b:ident : tactic =>
  `(tactic| (
    have hdisj := fpEq32_not_lt $a $b
    cases hna : fpIsNaN32 $a
    · cases hnb : fpIsNaN32 $b
      · rw [evalFpCmp32_def]
        dsimp only [fpLe32, fpGt32, fpGe32, ConditionHolds]
        rw [hna, hnb]
        revert hdisj
        cases fpEq32 $a $b <;> cases fpLt32 $a $b <;> decide
      · simp [evalFpCmp32_def, fpLe32, fpGt32, fpGe32, ConditionHolds, hna, hnb,
              fpEq32_of_nan_r hnb, fpLt32_of_nan_r hnb]
    · simp [evalFpCmp32_def, fpLe32, fpGt32, fpGe32, ConditionHolds, hna,
            fpEq32_of_nan_l hna, fpLt32_of_nan_l hna]))

@[simp, arm64_norm, wp_norm]
theorem conditionHolds_eq_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .EQ (evalFpCmp32 sig a b) = fpEq32 a b := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_ne_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .NE (evalFpCmp32 sig a b) = !fpEq32 a b := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_cs_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .CS (evalFpCmp32 sig a b) = !fpLt32 a b := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_cc_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .CC (evalFpCmp32 sig a b) = fpLt32 a b := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_mi_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .MI (evalFpCmp32 sig a b) = fpLt32 a b := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_pl_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .PL (evalFpCmp32 sig a b) = !fpLt32 a b := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_vs_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .VS (evalFpCmp32 sig a b) = (fpIsNaN32 a || fpIsNaN32 b) := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_vc_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .VC (evalFpCmp32 sig a b) = (!fpIsNaN32 a && !fpIsNaN32 b) := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_hi_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .HI (evalFpCmp32 sig a b) = !fpLe32 a b := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_ls_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .LS (evalFpCmp32 sig a b) = fpLe32 a b := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_ge_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .GE (evalFpCmp32 sig a b) = fpGe32 a b := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_lt_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .LT (evalFpCmp32 sig a b) = !fpGe32 a b := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_gt_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .GT (evalFpCmp32 sig a b) = fpGt32 a b := by fp_cmp32_tac a b
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_le_evalFpCmp32 (sig : Bool) (a b : BitVec 32) :
    ConditionHolds .LE (evalFpCmp32 sig a b) = !fpGt32 a b := by fp_cmp32_tac a b

end Arm64
