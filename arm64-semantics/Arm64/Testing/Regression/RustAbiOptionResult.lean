/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Exec

/-!
# Rust ABI `Option` and `Result` Encoder Tests

Tests the register-return encoders in `Arm64.RustAbi` and the `: RustAbi.<enc>` return syntax of
`rust_spec` against compiled `rustc` AArch64 output (`--target aarch64-unknown-linux-gnu -C opt-level=3`,
`#![no_std]`), both by concrete execution and by symbolic verification of `checked_add_u64`.

```rust
#![no_std]
use core::num::NonZeroU64;
#[no_mangle] pub fn p_checked_add_u64(a: u64, b: u64) -> Option<u64> { a.checked_add(b) }
#[no_mangle] pub fn p_checked_add_u32(a: u32, b: u32) -> Option<u32> { a.checked_add(b) }
#[no_mangle] pub fn p_checked_add_u16(a: u16, b: u16) -> Option<u16> { a.checked_add(b) }
#[no_mangle] pub fn p_checked_add_u8(a: u8, b: u8) -> Option<u8> { a.checked_add(b) }
#[no_mangle] pub fn p_nonzero_low_byte(x: u64) -> Option<NonZeroU64> { NonZeroU64::new(x & 0xff) }
#[no_mangle] pub fn p_slice_get(s: &[u64], i: usize) -> Option<&u64> { s.get(i) }
#[no_mangle] pub fn p_slice_prefix(s: &[u8], n: usize) -> Option<&[u8]> { s.get(..n) }
#[no_mangle] pub fn p_checked_sub_res(a: u64, b: u64) -> Result<u64, ()> { a.checked_sub(b).ok_or(()) }
#[no_mangle] pub fn p_div_res(a: u64, b: u64) -> Result<u64, u64> { if b == 0 { Err(a) } else { Ok(a / b) } }
#[no_mangle] pub fn p_mul_res32(a: u32, b: u32) -> Result<u32, u32> { a.checked_mul(b).ok_or(a) }
#[repr(u8)] pub enum DigitErr { Empty = 0, NotDigit = 1 }
#[no_mangle] pub fn p_digit(c: u8) -> Result<u8, DigitErr> {
    if c.is_ascii_digit() { Ok(c - b'0') } else if c == 0 { Err(DigitErr::Empty) } else { Err(DigitErr::NotDigit) } }
```
-/

@[expose] public section

namespace Testing.RustAbiOptionResult

open Arm64 Arm64.RustAbi ProofLib

/-! ## Decidability -/

instance (sf : State) (o : Option (BitVec 64)) : Decidable (optionU64.holds sf o) := by
  cases o <;> simp only [optionU64] <;> infer_instance
instance (sf : State) (o : Option (BitVec 32)) : Decidable (optionU32.holds sf o) := by
  cases o <;> simp only [optionU32] <;> infer_instance
instance (sf : State) (o : Option (BitVec 16)) : Decidable (optionU16.holds sf o) := by
  cases o <;> simp only [optionU16] <;> infer_instance
instance (sf : State) (o : Option (BitVec 8)) : Decidable (optionU8.holds sf o) := by
  cases o <;> simp only [optionU8] <;> infer_instance
instance (sf : State) (o : Option (BitVec 64)) : Decidable (optionNonNull64.holds sf o) := by
  cases o <;> simp only [optionNonNull64] <;> infer_instance
instance (sf : State) (o : Option (BitVec 64 × BitVec 64)) : Decidable (optionSlice.holds sf o) := by
  rcases o with _ | ⟨_, _⟩ <;> simp only [optionSlice] <;> infer_instance
instance (sf : State) (r : Except (BitVec 64) (BitVec 64)) : Decidable (resultU64.holds sf r) := by
  cases r <;> simp only [resultU64] <;> infer_instance
instance (sf : State) (r : Except Unit (BitVec 64)) : Decidable (resultU64Unit.holds sf r) := by
  rcases r with ⟨⟩ | _ <;> simp only [resultU64Unit] <;> infer_instance
instance (sf : State) (r : Except (BitVec 32) (BitVec 32)) : Decidable (resultU32.holds sf r) := by
  cases r <;> simp only [resultU32] <;> infer_instance
instance (sf : State) (r : Except (BitVec 8) (BitVec 8)) : Decidable (resultU8.holds sf r) := by
  cases r <;> simp only [resultU8] <;> infer_instance

/-! ## Concrete execution against `rustc` output -/

/-- Flat test memory: `words` at `0x1000` (`r-x`), every other byte zero and `rw`. -/
def testMem (words : List (BitVec 32)) : Memory :=
  let code := (Program.ofWords 0x1000#64 words).code.toArray
  ⟨fun a =>
    let i := (a - 0x1000#64).toNat
    if h : i < code.size then some (some Perm.rx, code[i]) else some (some Perm.rw, 0#8)⟩

/-- Run `words` from `0x1000` with `x0..x2 := a, b, c` until `RET` to `0xdead0000`. -/
def run (words : List (BitVec 32)) (a : BitVec 64) (b : BitVec 64 := 0) (c : BitVec 64 := 0) : State :=
  let s0 := ((({} : State).setMem (testMem words)).writeReg64 .x0 a |>.writeReg64 .x1 b
    |>.writeReg64 .x2 c |>.writeReg64 .lr 0xdead0000#64)
  execUntilPC 50 (Program.ofWords 0x1000#64 words) 0xdead0000#64
    { s0 with pc := 0x1000#64, status := .Running }

/-- `p_checked_add_u64`: `adds x1, x0, x1; cmp x1, x0; cset w0, hs; ret`. -/
def checkedAddU64 : List (BitVec 32) := [0x8b000021#32, 0xeb00003f#32, 0x1a9f37e0#32, 0xd65f03c0#32]
def checkedAddU32 : List (BitVec 32) := [0x0b000021#32, 0x6b00003f#32, 0x1a9f37e0#32, 0xd65f03c0#32]
def checkedAddU16 : List (BitVec 32) :=
  [0x0b000021#32, 0x12003c28#32, 0x6b20211f#32, 0x1a9f37e0#32, 0xd65f03c0#32]
def checkedAddU8 : List (BitVec 32) :=
  [0x0b000021#32, 0x12001c28#32, 0x6b20011f#32, 0x1a9f37e0#32, 0xd65f03c0#32]
def nonzeroLowByte : List (BitVec 32) := [0x92401c00#32, 0xd65f03c0#32]
def sliceGet : List (BitVec 32) := [0x8b020c08#32, 0xeb01005f#32, 0x9a9f3100#32, 0xd65f03c0#32]
def slicePrefix : List (BitVec 32) := [0xeb01005f#32, 0xaa0203e1#32, 0x9a8083e0#32, 0xd65f03c0#32]
def checkedSubRes : List (BitVec 32) := [0xeb010001#32, 0x1a9f27e0#32, 0xd65f03c0#32]
def divRes : List (BitVec 32) :=
  [0xaa0003e8#32, 0xb4000081#32, 0x9ac10901#32, 0xaa1f03e0#32, 0xd65f03c0#32,
   0x52800020#32, 0xaa0803e1#32, 0xd65f03c0#32]
def mulRes32 : List (BitVec 32) :=
  [0x9ba17c09#32, 0xf2607d3f#32, 0x1a9f07e8#32, 0x1a891001#32, 0x2a0803e0#32, 0xd65f03c0#32]
def digit : List (BitVec 32) :=
  [0x5100c008#32, 0x72001c1f#32, 0x12001d09#32, 0x1a9f07ea#32, 0x7100253f#32, 0x1a9f97e0#32,
   0x1a888141#32, 0xd65f03c0#32]

-- `Option<u64>` (`{ i64, i64 }`).
#guard decide (optionU64.holds (run checkedAddU64 5 7) (some 12))
#guard decide (optionU64.holds (run checkedAddU64 (-1) 2) none)
#guard !decide (optionU64.holds (run checkedAddU64 (-1) 2) (some 1))
#guard !decide (optionU64.holds (run checkedAddU64 5 7) none)
-- `None` leaves the wrapped sum in `x1`: the encoder must not constrain it.
#guard (run checkedAddU64 (-1) 2).readReg64 .x1 == 1#64
-- `Option<u32>` / `<u16>` / `<u8>` (`{ i32, i32 }` / `{ i16, i16 }` / `{ i1, i8 }`).
#guard decide (optionU32.holds (run checkedAddU32 0xffff_fff0 0xf) (some 0xffff_ffff))
#guard decide (optionU32.holds (run checkedAddU32 0xffff_fff0 0x10) none)
#guard decide (optionU16.holds (run checkedAddU16 0xfff0 0xf) (some 0xffff))
#guard decide (optionU16.holds (run checkedAddU16 0xfff0 0x10) none)
#guard !decide (optionU16.holds (run checkedAddU16 0xfff0 0x10) (some 0))
#guard decide (optionU8.holds (run checkedAddU8 200 55) (some 255))
#guard decide (optionU8.holds (run checkedAddU8 200 56) none)
#guard !decide (optionU8.holds (run checkedAddU8 200 56) (some 0))
-- `Option<NonZeroU64>` (null niche in `x0`).
#guard decide (optionNonNull64.holds (run nonzeroLowByte 0x1234) (some 0x34))
#guard decide (optionNonNull64.holds (run nonzeroLowByte 0x1200) none)
#guard !decide (optionNonNull64.holds (run nonzeroLowByte 0x1200) (some 0))
-- `Option<&u64>` from `<[u64]>::get` (`x0 = ptr`, `x1 = len`, `x2 = i`).
#guard decide (optionNonNull64.holds (run sliceGet 0x8000 4 3) (some 0x8018))
#guard decide (optionNonNull64.holds (run sliceGet 0x8000 4 4) none)
-- `Option<&[u8]>` from `<[u8]>::get(..n)` (`{ ptr, i64 }`, null niche).
#guard decide (optionSlice.holds (run slicePrefix 0x8000 10 4) (some (0x8000, 4)))
#guard decide (optionSlice.holds (run slicePrefix 0x8000 10 11) none)
#guard !decide (optionSlice.holds (run slicePrefix 0x8000 10 4) (some (0x8000, 10)))
-- `Result<u64, ()>`, `Result<u64, u64>`, `Result<u32, u32>`.
#guard decide (resultU64Unit.holds (run checkedSubRes 9 4) (.ok 5))
#guard decide (resultU64Unit.holds (run checkedSubRes 4 9) (.error ()))
#guard decide (resultU64.holds (run divRes 17 5) (.ok 3))
#guard decide (resultU64.holds (run divRes 17 0) (.error 17))
#guard !decide (resultU64.holds (run divRes 17 0) (.ok 17))
#guard decide (resultU32.holds (run mulRes32 0x10000 0xffff) (.ok 0xffff_0000))
#guard decide (resultU32.holds (run mulRes32 0x10000 0x10000) (.error 0x10000))
-- `Result<u8, DigitErr>` (`{ i1, i8 }`, error byte = enum discriminant).
#guard decide (resultU8.holds (run digit 0x37) (.ok 7))
#guard decide (resultU8.holds (run digit 0) (.error 0))
#guard decide (resultU8.holds (run digit 0x41) (.error 1))
#guard !decide (resultU8.holds (run digit 0x41) (.ok 1))

/-! ## Symbolic verification of `Option<u64>` return -/

def checkedAddU64FnCode : FnCode :=
  .ofFn "checked_add_u64" "8b000021 eb00003f 1a9f37e0 d65f03c0"

abbrev CheckedAddU64CodeAt (prog : Program) : Prop :=
  checkedAddU64FnCode.holds prog

/-- `checked_add_u64` with the typed return: payload unconstrained on `None`. -/
rust_spec rustCheckedAddU64OptSpec (a : u64) (b : u64) : RustAbi.optionU64
  returns if BitVec.ult (a + b) a then none else some (a + b)

/-- Unfolding rule for an `if`-valued `Option<u64>` return, so `wp_done` sees plain register
    equations. -/
theorem optionU64_ite (sf : State) (c : Prop) [Decidable c] (v : BitVec 64) :
    optionU64.holds sf (if c then none else some v) ↔
      if c then sf.readReg64 .x0 = 0#64 else sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = v := by
  by_cases c <;> simp_all [optionU64]

theorem rustCheckedAddU64Opt_ok_abstract (prog : Program)
    (h_code : CheckedAddU64CodeAt prog) :
    prog.subroutineOk "checked_add_u64" rustCheckedAddU64OptSpec := by
  wp_init
  wp_steps
  simp only [optionU64_ite]
  wp_done

end Testing.RustAbiOptionResult
