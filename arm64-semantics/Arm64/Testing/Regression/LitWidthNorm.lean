/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib

/-!
# Regression Tests for `ProofLib.LitNorm` and `ProofLib.BV.WidthNorm`

Tests literal folding with `simp only [wp_norm]`, opt-in width round-trip normalization with
`simp only [wp_norm, width_norm]`, negative `#guard_msgs` guards on non-literal or out-of-range
operands, and `ProofLib` re-exports of state, memory, and separation-logic lemmas.
-/

@[expose] public section

namespace Testing.LitWidthNorm

open Arm64 ProofLib

/-! ## Literal folding (`ProofLib.LitNorm`) -/

/-- A ground `BitVec` literal hidden behind an `Int64` round trip (as produced by `i64` Rust code);
    core `BitVec.reduce*` simprocs do not see through it, `ProofLib.evalBitVecLit?` does.
    (Note: `evalBitVecLit?` does *not* see through a `def`/`abbrev` constant of type `BitVec w`
    inside `simp`, since `whnf` there cannot unfold `Fin.Internal.ofNat`.) -/
local notation "k24" => Int64.toBitVec (Int64.ofBitVec 24#64)
abbrev kCount : Nat := 7

example : k24 * 3#64 = 72#64 := by simp only [wp_norm]
example : BitVec.toNat k24 = 24 := by simp only [wp_norm]
example : BitVec.ult k24 25#64 = true := by simp only [wp_norm]
example : (k24 == 24#64) = true := by simp only [wp_norm]
example : (k24 == 25#64) = false := by simp only [wp_norm]
example : kCount * 8 = 56 := by simp only [wp_norm]
example : k24 >>> 3 = 3#64 := by simp only [wp_norm]
example : k24 <<< 1 = 48#64 := by simp only [wp_norm]

/-- Negative: `reduceBitVecMul` must not fire when a factor is a free variable. -/
opaque P : BitVec 64 → Prop

/--
error: `simp` made no progress
-/
#guard_msgs in
example (x : BitVec 64) (h : P (x * 3#64)) : P (x * 3#64) := by
  simp only [wp_norm] at h ⊢

/-- Negative: `reduceNatMulLit` must not fire on a symbolic `Nat` factor. -/
opaque Q : Nat → Prop

/--
error: `simp` made no progress
-/
#guard_msgs in
example (n : Nat) (h : Q (n * kCount)) : Q (n * kCount) := by
  simp only [wp_norm] at h ⊢

/-! ## Width round trips (`ProofLib.BV.WidthNorm`) -/

-- `(x >>> 48)` survives a 32-bit truncation.
example (x : BitVec 64) : BitVec.setWidth 64 (BitVec.setWidth 32 (x >>> 48)) = x >>> 48 := by
  simp only [wp_norm, width_norm]
example (x : BitVec 64) : BitVec.setWidth 64 (BitVec.setWidth 32 (x >>> 48#64)) = x >>> 48#64 := by
  simp only [wp_norm, width_norm]
example (x : BitVec 64) : BitVec.zeroExtend 64 (BitVec.truncate 32 (x >>> 32)) = x >>> 32 := by
  simp only [wp_norm, width_norm]
example (x : BitVec 64) : BitVec.setWidth 64 (BitVec.setWidth 32 (x >>> 48)) = x >>> 48 := by
  simp [width_norm]

-- 32-to-64-to-32 round trips.
example (x : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 x &&& 0xff#64) = x &&& 0xff#32 := by
  simp only [wp_norm, width_norm]
example (x : BitVec 32) :
    BitVec.truncate 32 (0xedb88320#64 ^^^ BitVec.zeroExtend 64 x) = 0xedb88320#32 ^^^ x := by
  simp only [wp_norm, width_norm]
example (x : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 x ||| 0x80#64) = x ||| 0x80#32 := by
  simp only [wp_norm, width_norm]
example (x : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 x >>> 1) = x >>> 1 := by
  simp only [wp_norm, width_norm]
example (x : BitVec 32) : BitVec.truncate 32 (BitVec.zeroExtend 64 x <<< 3) = x <<< 3 := by
  simp only [wp_norm, width_norm]

-- Comparisons through a zero-extension.
example (x : BitVec 32) : (BitVec.zeroExtend 64 x == 37#64) = (x == 37#32) := by
  simp only [wp_norm, width_norm]
example (x : BitVec 32) : (BitVec.zeroExtend 64 x).ult 37#64 = x.ult 37#32 := by
  simp only [wp_norm, width_norm]
example (x : BitVec 32) : (BitVec.zeroExtend 64 x = 37#64) = (x = 37#32) := by
  simp only [wp_norm, width_norm]
example (x : BitVec 8) : (BitVec.zeroExtend 64 x).ult 10#64 = x.ult 10#8 := by
  simp [width_norm]

-- Literal on the left.
example (x : BitVec 32) : (37#64 == BitVec.zeroExtend 64 x) = (37#32 == x) := by
  simp only [wp_norm, width_norm]
example (x : BitVec 32) : (37#64 = BitVec.zeroExtend 64 x) = (37#32 = x) := by
  simp only [wp_norm, width_norm]
example (x : BitVec 32) : (10#64).ult (BitVec.zeroExtend 64 x) = (10#32).ult x := by
  simp only [wp_norm, width_norm]

-- Register shift amounts of any width.
example (x : BitVec 32) (y : BitVec 64) :
    BitVec.setWidth 32 (BitVec.setWidth 64 x >>> y) = x >>> y := by
  simp only [wp_norm, width_norm]
example (x : BitVec 32) (y : BitVec 8) :
    BitVec.setWidth 32 (BitVec.setWidth 64 x <<< y) = x <<< y := by
  simp only [wp_norm, width_norm]
example (x : BitVec 64) (y : BitVec 32) (h : 64 ≤ 32 + y.toNat) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (x >>> y)) = x >>> y :=
  BitVec.setWidth_setWidth_ushiftRight_bv_of_le 32 x y h

/-- Negative: the literal `0x1_0000_0000` does not fit in 32 bits, so `setWidth_beq_ofNat`
    must not rewrite. -/
opaque R : Bool → Prop

/--
error: `simp` made no progress
-/
#guard_msgs in
example (x : BitVec 32) (h : R (BitVec.zeroExtend 64 x == 0x100000000#64)) :
    R (BitVec.zeroExtend 64 x == 0x100000000#64) := by
  simp only [BitVec.setWidth_beq_ofNat] at h ⊢

-- `LSLV` / `LSRV` shift-amount masks, oriented toward `shift64`'s `% 64`.
example (x y : BitVec 64) : x <<< (y &&& 63#64) = x <<< (y.toNat % 64) := by
  simp only [wp_norm, width_norm]
example (x y : BitVec 64) : x >>> (y &&& 63#64) = x >>> (y.toNat % 64) := by
  simp only [wp_norm, width_norm]
example (x y : BitVec 32) : x <<< (y &&& 31#32) = x <<< (y.toNat % 32) := by
  simp only [width_norm]
example (x y : BitVec 32) : x >>> (y &&& 31#32) = x >>> (y.toNat % 32) := by
  simp only [width_norm]

-- `UMULH`.
example (a b : BitVec 64) :
    BitVec.setWidth 64 ((BitVec.setWidth 128 a * BitVec.setWidth 128 b) >>> 64) =
      BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64) :=
  BitVec.setWidth_umulh a b
example (a b : BitVec 64) : mulHi64 a b = BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64) :=
  mulHi64_eq_ofNat a b

/-- Negative: width round trips are opt-in (`width_norm`) and not part of `wp_norm`. -/
opaque S : BitVec 32 → Prop

/--
error: `simp` made no progress
-/
#guard_msgs in
example (x : BitVec 32) (h : S (BitVec.truncate 32 (BitVec.zeroExtend 64 x &&& 0xff#64))) :
    S (BitVec.truncate 32 (BitVec.zeroExtend 64 x &&& 0xff#64)) := by
  simp only [wp_norm] at h ⊢

/-! ## Commonly guessed names -/

example (s : State) (v : BitVec 64) :
    (s.writeReg64 (.gpr 3#5) v).readReg64 (.gpr 3#5) = v :=
  Arm64.State.readReg64_writeReg64_same s _ v (by decide) (by decide)

example (s : State) (v : BitVec 64) :
    (s.writeReg64 (.gpr 3#5) v).readReg64 (.gpr 4#5) = s.readReg64 (.gpr 4#5) :=
  Arm64.State.readReg64_writeReg64_ne s _ _ v (by decide)

example (P Q R : SepProp) : (P ∗ (Q ∗ R)) = (Q ∗ (P ∗ R)) := ProofLib.sepConj_left_comm P Q R
example (P Q R : SepProp) : ((P ∗ Q) ∗ R) = ((P ∗ R) ∗ Q) := Arm64.sepConj_right_comm P Q R
example (P Q R : SepProp) : ((P ∗ Q) ∗ R) = ((P ∗ R) ∗ Q) := ProofLib.sepConj_right_comm P Q R
example (P Q R : SepProp) : (P ∗ (Q ∗ R)) = (Q ∗ (P ∗ R)) := by rw [sepConj_left_comm]

/-! ## `readBytes` / `writeBytes`, `AgreesOutside`, `CodeLoaded`, and `calleeSavedVRegs` `wp_norm` -/

example (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length ≤ 2 ^ 64) :
    (m.writeBytes a bs).readBytes a bs.length = bs :=
  Memory.readBytes_writeBytes_same m a bs h

example (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (hn : bs.length = n) (h : n ≤ 2 ^ 64) :
    (m.writeBytes a bs).readBytes a n = bs :=
  Memory.readBytes_writeBytes_eq m a bs n hn h

example (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) (off len : Nat)
    (hle : off + len ≤ bs.length) (h : bs.length ≤ 2 ^ 64) :
    (m.writeBytes a bs).readBytes (a + BitVec.ofNat 64 off) len = (bs.drop off).take len :=
  Memory.readBytes_writeBytes_slice m a bs off len hle h

example (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) :
    AgreesOutside m (m.writeBytes a bs) a bs.length :=
  agreesOutside_writeBytes m a bs

example {m₁ m₂ : Memory} {base a : BitVec 64} {len : Nat} (bs : List (BitVec 8))
    (h : AgreesOutside m₁ m₂ base len) (ha : (a - base).toNat + bs.length ≤ len) :
    AgreesOutside m₁ (m₂.writeBytes a bs) base len :=
  h.writeBytes bs ha

example (m : Memory) (a1 a2 : BitVec 64) (n1 : Nat) (bs : List (BitVec 8))
    (hd : DisjointRegions a1 n1 a2 bs.length) :
    (m.writeBytes a2 bs).readBytes a1 n1 = m.readBytes a1 n1 :=
  Memory.readBytes_writeBytes_disjoint m a1 n1 a2 bs hd

example {prog : Program} {m : Memory} (h : prog.CodeLoaded m) :
    prog.base.toNat % 4 = 0 ∧ prog.base.toNat + prog.code.length ≤ 2 ^ 64 :=
  ⟨h.aligned, h.no_wrap⟩

example {prog : Program} {m : Memory} (h : prog.CodeLoaded m) (i : Nat) (hi : i < prog.code.length) :
    m.read8 (prog.base + BitVec.ofNat 64 i) = prog.code[i] :=
  h.byte_eq i hi

-- `CodeLoaded` requires byte-for-byte equality across all `prog.code.length` bytes, including
-- 4-byte zero-filled extern stub slots.
def strictStubTestProg : Program :=
  { base := 0x1000#64
  , code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8]
  , stubs := [("ext_fn", 4)] }

example {m : Memory} (h : strictStubTestProg.CodeLoaded m)
    (i : Nat) (hi_lo : 4 ≤ i) (hi_hi : i < 8) :
    m.read8 (0x1000#64 + BitVec.ofNat 64 i) = 0#8 := by
  have hb := h.byte_eq i hi_hi
  have hcases : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> exact hb

example (prog : Program) (m : Memory)
    (h_al : prog.base.toNat % 4 = 0) (h_len : prog.base.toNat + prog.code.length ≤ 2 ^ 64) :
    prog.CodeLoaded (prog.loadCode m) :=
  Program.codeLoaded_loadCode prog m h_al h_len

example (s : State) (r : Reg) (v : BitVec 64) (v128 : BitVec 128) :
    calleeSavedVRegs (((s.writeReg64 r v).writeVReg128 0#5 v128).advancePC) =
      calleeSavedVRegs s := by
  simp only [wp_norm]

end Testing.LitWidthNorm
