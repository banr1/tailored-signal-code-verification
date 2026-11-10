/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Trusted.Process
public import Arm64.Trusted.Spec.RustHeap
public import Arm64.Trusted.Spec.GlobalAlloc

/-!
# ASCII Literal Macros and Decimal Integer Formatting/Parsing Tests

Positive `decide +kernel` and negative `#guard_msgs` tests for `ascii!`, `asciic!`, `asciiCode!`
(`Arm64.Trusted.Surface.Ascii`) and decimal formatting/parsing (`Arm64.Trusted.Spec.AsciiNum`),
plus definitional equality checks between `Init`-only `Spec` records in `RustHeap` / `GlobalAlloc`
and `rust_spec` expansion.
-/

@[expose] public section

namespace Arm64.Testing.AsciiTests

open Arm64 Arm64.Process Arm64.Rust

/-! ## `ascii!`, `asciic!`, and `asciiCode!` -/

example : ascii!"" = [] := by decide +kernel
example : ascii!"0" = [0x30#8] := by decide +kernel
example : ascii!"Az09" = [0x41#8, 0x7a#8, 0x30#8, 0x39#8] := by decide +kernel
example : ascii!"+-./: \n\t~" =
    [0x2b#8, 0x2d#8, 0x2e#8, 0x2f#8, 0x3a#8, 0x20#8, 0x0a#8, 0x09#8, 0x7e#8] := by
  decide +kernel

example : asciic!"\x00" = 0x00#8 := by decide +kernel
example : asciic!"-" = 0x2d#8 := by decide +kernel
example : asciic!"." = 0x2e#8 := by decide +kernel
example : asciic!"0" = 0x30#8 := by decide +kernel
example : asciic!"9" = 0x39#8 := by decide +kernel
example : asciic!"A" = 0x41#8 := by decide +kernel
example : asciic!"z" = 0x7a#8 := by decide +kernel
example : asciic!"\x7f" = 0x7f#8 := by decide +kernel

example : asciiCode!"\x00" = 0 := by decide +kernel
example : asciiCode!"-" = 45 := by decide +kernel
example : asciiCode!"0" = 48 := by decide +kernel
example : asciiCode!"9" = 57 := by decide +kernel
example : asciiCode!"A" = 65 := by decide +kernel
example : asciiCode!"\x7f" = 127 := by decide +kernel

example : ascii!"" = bytesOfString "" := by decide +kernel
example : ascii!"insert 42 99\n" = bytesOfString "insert 42 99\n" := by decide +kernel
example : ascii!"error: invalid command\n" = bytesOfString "error: invalid command\n" := by
  decide +kernel
example : ascii!"-0.0 NaN inf -inf 1.7976931348623157e308" =
    bytesOfString "-0.0 NaN inf -inf 1.7976931348623157e308" := by
  decide +kernel

/-- error: ascii! expects ASCII characters (< 128), got 'é' -/
#guard_msgs in
private def badAsciiNonAscii := ascii!"café"

/-- error: asciic! expects an ASCII character (< 128), got '€' -/
#guard_msgs in
private def badAsciicNonAscii := asciic!"€"

/-- error: asciic! expects a single-character ASCII string literal -/
#guard_msgs in
private def badAsciicEmpty := asciic!""

/-- error: asciic! expects a single-character ASCII string literal -/
#guard_msgs in
private def badAsciicTwo := asciic!"ab"

/-- error: asciiCode! expects an ASCII character (< 128), got 'λ' -/
#guard_msgs in
private def badAsciiCodeNonAscii := asciiCode!"λ"

/-- error: asciiCode! expects a single-character ASCII string literal -/
#guard_msgs in
private def badAsciiCodeEmpty := asciiCode!""

/-- error: asciiCode! expects a single-character ASCII string literal -/
#guard_msgs in
private def badAsciiCodeTwo := asciiCode!"01"

/-! ## `natToDigits10`, `formatDecimalNat`, and `formatDecimalInt` -/

example : natToDigits10 0 = [0] := by decide +kernel
example : natToDigits10 9 = [9] := by decide +kernel
example : natToDigits10 10 = [1, 0] := by decide +kernel
example : natToDigits10 42 = [4, 2] := by decide +kernel
example : natToDigits10 (2 ^ 64 - 1) =
    [1, 8, 4, 4, 6, 7, 4, 4, 0, 7, 3, 7, 0, 9, 5, 5, 1, 6, 1, 5] := by
  decide +kernel

example : formatDecimalNat 0 = ascii!"0" := by decide +kernel
example : formatDecimalNat 9 = ascii!"9" := by decide +kernel
example : formatDecimalNat 10 = ascii!"10" := by decide +kernel
example : formatDecimalNat 42 = ascii!"42" := by decide +kernel
example : formatDecimalNat (2 ^ 64 - 1) = ascii!"18446744073709551615" := by decide +kernel

example : formatDecimalInt 0 = ascii!"0" := by decide +kernel
example : formatDecimalInt 9 = ascii!"9" := by decide +kernel
example : formatDecimalInt 10 = ascii!"10" := by decide +kernel
example : formatDecimalInt 42 = ascii!"42" := by decide +kernel
example : formatDecimalInt (-1) = ascii!"-1" := by decide +kernel
example : formatDecimalInt (-42) = ascii!"-42" := by decide +kernel
example : formatDecimalInt (-(2 ^ 63 : Int)) = ascii!"-9223372036854775808" := by decide +kernel
example : formatDecimalInt ((2 ^ 63 : Int) - 1) = ascii!"9223372036854775807" := by decide +kernel

/-! ## `parseDecimalNat`, `parseDecimalUInt`, `parseDecimalU64`, and `parseDecimalU32` -/

example : parseDecimalNat ascii!"0" = some 0 := by decide +kernel
example : parseDecimalNat ascii!"00042" = some 42 := by decide +kernel
example : parseDecimalNat ascii!"18446744073709551615" = some (2 ^ 64 - 1) := by decide +kernel
example : parseDecimalNat ascii!"18446744073709551616" = some (2 ^ 64) := by decide +kernel

example : parseDecimalNat [] = none := by decide +kernel
example : parseDecimalNat ascii!"" = none := by decide +kernel
example : parseDecimalNat ascii!"/" = none := by decide +kernel
example : parseDecimalNat ascii!":" = none := by decide +kernel
example : parseDecimalNat [0x2f#8] = none := by decide +kernel
example : parseDecimalNat [0x3a#8] = none := by decide +kernel
example : parseDecimalNat ascii!" 1" = none := by decide +kernel
example : parseDecimalNat ascii!"1 " = none := by decide +kernel
example : parseDecimalNat ascii!"1\n" = none := by decide +kernel
example : parseDecimalNat ascii!"-1" = none := by decide +kernel
example : parseDecimalNat ascii!"+1" = none := by decide +kernel
example : parseDecimalNat ascii!"12a3" = none := by decide +kernel

example : parseDecimalU64 ascii!"0" = some 0#64 := by decide +kernel
example : parseDecimalU64 ascii!"00042" = some 42#64 := by decide +kernel
example : parseDecimalU64 ascii!"18446744073709551615" = some (BitVec.allOnes 64) := by
  decide +kernel
example : parseDecimalU64 ascii!"00018446744073709551615" = some (BitVec.allOnes 64) := by
  decide +kernel
example : parseDecimalU64 ascii!"18446744073709551616" = none := by decide +kernel
example : parseDecimalU64 [] = none := by decide +kernel
example : parseDecimalU64 ascii!"/" = none := by decide +kernel
example : parseDecimalU64 ascii!":" = none := by decide +kernel
example : parseDecimalU64 ascii!" 1" = none := by decide +kernel
example : parseDecimalU64 ascii!"1 " = none := by decide +kernel
example : parseDecimalU64 ascii!"1\n" = none := by decide +kernel
example : parseDecimalU64 ascii!"-1" = none := by decide +kernel
example : parseDecimalU64 ascii!"12a3" = none := by decide +kernel

example : parseDecimalU32 ascii!"0" = some 0#32 := by decide +kernel
example : parseDecimalU32 ascii!"4294967295" = some (BitVec.allOnes 32) := by decide +kernel
example : parseDecimalU32 ascii!"4294967296" = none := by decide +kernel

example : parseDecimalUInt 8 ascii!"255" = some 255#8 := by decide +kernel
example : parseDecimalUInt 8 ascii!"256" = none := by decide +kernel
example : parseDecimalUInt 0 ascii!"0" = some 0#0 := by decide +kernel
example : parseDecimalUInt 0 ascii!"1" = none := by decide +kernel

/-! ## `parseDecimalInt`, `parseDecimalSInt`, and `parseDecimalI64` -/

example : parseDecimalInt ascii!"0" = some 0 := by decide +kernel
example : parseDecimalInt ascii!"-0" = some 0 := by decide +kernel
example : parseDecimalInt ascii!"-000" = some 0 := by decide +kernel
example : parseDecimalInt ascii!"-42" = some (-42) := by decide +kernel
example : parseDecimalInt ascii!"-0042" = some (-42) := by decide +kernel
example : parseDecimalInt ascii!"42" = some 42 := by decide +kernel
example : parseDecimalInt ascii!"-9223372036854775808" = some (-(2 ^ 63 : Int)) := by
  decide +kernel
example : parseDecimalInt ascii!"9223372036854775807" = some ((2 ^ 63 : Int) - 1) := by
  decide +kernel

example : parseDecimalInt [] = none := by decide +kernel
example : parseDecimalInt ascii!"-" = none := by decide +kernel
example : parseDecimalInt ascii!"+" = none := by decide +kernel
example : parseDecimalInt ascii!"+1" = none := by decide +kernel
example : parseDecimalInt ascii!"--1" = none := by decide +kernel
example : parseDecimalInt ascii!" -1" = none := by decide +kernel
example : parseDecimalInt ascii!"- 1" = none := by decide +kernel
example : parseDecimalInt ascii!"-1 " = none := by decide +kernel
example : parseDecimalInt ascii!"-1\n" = none := by decide +kernel
example : parseDecimalInt ascii!"-/" = none := by decide +kernel
example : parseDecimalInt ascii!"-:" = none := by decide +kernel
example : parseDecimalInt ascii!"-12a3" = none := by decide +kernel

example : parseDecimalI64 ascii!"0" = some 0#64 := by decide +kernel
example : parseDecimalI64 ascii!"-0" = some 0#64 := by decide +kernel
example : parseDecimalI64 ascii!"-42" = some (BitVec.ofInt 64 (-42)) := by decide +kernel
example : parseDecimalI64 ascii!"-9223372036854775808" = some 0x8000000000000000#64 := by
  decide +kernel
example : parseDecimalI64 ascii!"-9223372036854775809" = none := by decide +kernel
example : parseDecimalI64 ascii!"9223372036854775807" = some 0x7fffffffffffffff#64 := by
  decide +kernel
example : parseDecimalI64 ascii!"9223372036854775808" = none := by decide +kernel
example : parseDecimalI64 ascii!"-" = none := by decide +kernel
example : parseDecimalI64 [] = none := by decide +kernel

example : parseDecimalSInt 8 ascii!"-128" = some 0x80#8 := by decide +kernel
example : parseDecimalSInt 8 ascii!"-129" = none := by decide +kernel
example : parseDecimalSInt 8 ascii!"127" = some 0x7f#8 := by decide +kernel
example : parseDecimalSInt 8 ascii!"128" = none := by decide +kernel
example : parseDecimalSInt 1 ascii!"-1" = some 1#1 := by decide +kernel
example : parseDecimalSInt 1 ascii!"0" = some 0#1 := by decide +kernel
example : parseDecimalSInt 1 ascii!"1" = none := by decide +kernel
example : parseDecimalSInt 0 ascii!"0" = none := by decide +kernel

/-! ## Concrete Round-Trip Checks -/

example :
    [0, 1, 9, 10, 42, 99999, 2 ^ 32 - 1, 2 ^ 64 - 1, 2 ^ 128].all
      (fun n => parseDecimalNat (formatDecimalNat n) == some n) = true := by
  decide +kernel

example :
    ([0, 1, -1, 9, -9, 10, -10, 42, -42,
      (2 ^ 63 : Int) - 1, -(2 ^ 63 : Int), (2 ^ 128 : Int), -(2 ^ 128 : Int)] : List Int).all
      (fun z => parseDecimalInt (formatDecimalInt z) == some z) = true := by
  decide +kernel

example :
    ([0#64, 1#64, 42#64, 0x7fffffffffffffff#64, 0x8000000000000000#64, BitVec.allOnes 64] :
      List (BitVec 64)).all
      (fun v =>
        parseDecimalU64 (formatDecimalNat v.toNat) == some v &&
        parseDecimalI64 (formatDecimalInt v.toInt) == some v) = true := by
  decide +kernel

/-! ## `RustHeap` and `GlobalAlloc` `Init`-Only `Spec` Equivalence with `rust_spec` -/

rust_spec allocSpecDsl (ctx A : Arm64.Rust.Allocator) (ctx zeroed : Bool)
    (n : u64) (_ : u64 := 1#64) (sp : sp) : (ret : u64)
  requires_cond n ≠ 0 ∧ SmallLen n.toNat
  preserves     A.pool ∗ hookFrame sp
  ensures       if ret = 0 then emp
                else A.live ret n.toNat ∗
                  (if zeroed then (ret ↦ₛ List.replicate n.toNat 0#8)
                   else memRegion ret n.toNat)

rust_spec deallocSpecDsl (ctx A : Arm64.Rust.Allocator)
    (p : ptr) (n : u64) (_ : u64 := 1#64) (sp : sp)
  preserves A.pool
  requires  A.live p n.toNat ∗ memRegion p n.toNat
  preserves hookFrame sp

rust_spec shimSpecDsl (sp : sp)
  preserves hookFrame sp

example : @Arm64.Rust.allocSpec = @allocSpecDsl := rfl
example : @Arm64.Rust.deallocSpec = @deallocSpecDsl := rfl
example : @Arm64.Rust.shimSpec = @shimSpecDsl := rfl

rust_spec globalAllocSpecDsl
    (ctx Heap : Nat → Nat → State → SepProp)
    (ctx Block : BitVec 64 → Nat → Nat → SepProp)
    (ctx stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks : Nat)
    (size : u64) (align : u64) (sp : sp)
    (ghost liveBytes liveBlocks : Nat) : (ret : u64)
  requires_cond LayoutOk size align
  requires      Heap liveBytes liveBlocks s0 ∗
                memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes
  ensures_pure  AllocStatePreserved s0 sf
  ensures       memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes ∗
                (if ret = 0#64 then
                   ⌜¬ BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks
                       liveBytes liveBlocks size.toNat align.toNat⌝ ∗
                   Heap liveBytes liveBlocks sf
                 else
                   ⌜ret.toNat % align.toNat = 0 ∧ ret.toNat + size.toNat < 2 ^ 64⌝ ∗
                   Heap (liveBytes + size.toNat) (liveBlocks + 1) sf ∗
                   Block ret size.toNat align.toNat ∗
                   memRegion ret size.toNat)
  oom_when      True

rust_spec globalAllocZeroedSpecDsl
    (ctx Heap : Nat → Nat → State → SepProp)
    (ctx Block : BitVec 64 → Nat → Nat → SepProp)
    (ctx stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks : Nat)
    (size : u64) (align : u64) (sp : sp)
    (ghost liveBytes liveBlocks : Nat) : (ret : u64)
  requires_cond LayoutOk size align
  requires      Heap liveBytes liveBlocks s0 ∗
                memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes
  ensures_pure  AllocStatePreserved s0 sf
  ensures       memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes ∗
                (if ret = 0#64 then
                   ⌜¬ BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks
                       liveBytes liveBlocks size.toNat align.toNat⌝ ∗
                   Heap liveBytes liveBlocks sf
                 else
                   ⌜ret.toNat % align.toNat = 0 ∧ ret.toNat + size.toNat < 2 ^ 64⌝ ∗
                   Heap (liveBytes + size.toNat) (liveBlocks + 1) sf ∗
                   Block ret size.toNat align.toNat ∗
                   (ret ↦ₛ List.replicate size.toNat 0#8))
  oom_when      True

rust_spec globalDeallocSpecDsl
    (ctx Heap : Nat → Nat → State → SepProp)
    (ctx Block : BitVec 64 → Nat → Nat → SepProp)
    (ctx stackBytes : Nat)
    (p : ptr) (size : u64) (align : u64) (sp : sp)
    (ghost liveBytes liveBlocks : Nat)
  requires_cond LayoutOk size align
  requires      Heap liveBytes liveBlocks s0 ∗
                Block p size.toNat align.toNat ∗
                memRegion p size.toNat ∗
                memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes
  ensures_pure  AllocStatePreserved s0 sf
  ensures       Heap (liveBytes - size.toNat) (liveBlocks - 1) sf ∗
                memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes

rust_spec globalReallocSpecDsl
    (ctx Heap : Nat → Nat → State → SepProp)
    (ctx Block : BitVec 64 → Nat → Nat → SepProp)
    (ctx stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks : Nat)
    (p : ptr) (oldSize : u64) (align : u64) (newSize : u64) (sp : sp)
    (ghost bs : List (BitVec 8))
    (ghost liveBytes liveBlocks : Nat) : (ret : u64)
  requires_cond LayoutOk oldSize align ∧ LayoutOk newSize align ∧
                bs.length ≤ oldSize.toNat ∧ bs.length ≤ newSize.toNat
  requires      Heap liveBytes liveBlocks s0 ∗
                Block p oldSize.toNat align.toNat ∗
                (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (oldSize.toNat - bs.length) ∗
                memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes
  ensures_pure  AllocStatePreserved s0 sf
  ensures       memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes ∗
                (if ret = 0#64 then
                   ⌜¬ BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks
                       liveBytes liveBlocks newSize.toNat align.toNat⌝ ∗
                   Heap liveBytes liveBlocks sf ∗
                   Block p oldSize.toNat align.toNat ∗
                   (p ↦ₛ bs) ∗
                   memRegion (p + BitVec.ofNat 64 bs.length) (oldSize.toNat - bs.length)
                 else
                   ⌜ret.toNat % align.toNat = 0 ∧ ret.toNat + newSize.toNat < 2 ^ 64⌝ ∗
                   Heap (liveBytes - oldSize.toNat + newSize.toNat) liveBlocks sf ∗
                   Block ret newSize.toNat align.toNat ∗
                   (ret ↦ₛ bs) ∗
                   memRegion (ret + BitVec.ofNat 64 bs.length) (newSize.toNat - bs.length))
  oom_when      True

example : @Arm64.Rust.globalAllocSpec = @globalAllocSpecDsl := rfl
example : @Arm64.Rust.globalAllocZeroedSpec = @globalAllocZeroedSpecDsl := rfl
example : @Arm64.Rust.globalDeallocSpec = @globalDeallocSpecDsl := rfl
example : @Arm64.Rust.globalReallocSpec = @globalReallocSpecDsl := rfl

end Arm64.Testing.AsciiTests
