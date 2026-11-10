/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.AsciiNum

/-!
# Decimal ASCII Formatting and Parsing Tests

Tests for `ProofLib.AsciiNum` covering byte-accumulator equivalence, 4-digit chunk splitting,
bounded decimal parsing overflow bounds, and formatting round-trip identities.
-/

@[expose] public section

namespace ProofLib.Testing.AsciiNum

open Arm64 ProofLib.AsciiNum

example (n : Nat) : formatDecimalNat n = formatDecimalByteAux (n + 1) n [] :=
  formatDecimalNat_eq_byteAux n

example : formatDecimalByteAux 1 0 [] = ascii!"0" := by decide +kernel
example : formatDecimalByteAux 43 42 [] = ascii!"42" := by decide +kernel

example : formatDecimalNat 12345 = formatDecimalNat 1 ++ fourDecimalDigits 2345 :=
  formatDecimalNat_div_10000 (by decide)

example (bs : List (BitVec 8)) :
    parseDecimalU64 bs =
      if bs.isEmpty then none
      else (parseDecimalBoundedFold (2 ^ 64) 0 bs).map (BitVec.ofNat 64) :=
  parseDecimalU64_eq_boundedFold bs

example : parseDecimalBoundedFold (2 ^ 64) 0 ascii!"18446744073709551615" = some (2 ^ 64 - 1) := by
  decide +kernel

example : parseDecimalBoundedFold (2 ^ 64) 0 ascii!"18446744073709551616" = none := by
  decide +kernel

example : parseDecimalBoundedFold (2 ^ 64) 0 ascii!"999999999999999999999x" = none := by
  decide +kernel

-- `acc < bound` is needed in `parseDecimalBoundedFold_eq` on `[]`.
example : parseDecimalBoundedFold 10 10 [] ≠
    (match parseDecimalNatFold 10 [] with
     | some n => if n < 10 then some n else none
     | none => none) := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  parseDecimalBoundedFold (2 ^ 64) 0 [52#8, 50#8] = none
is false
-/
#guard_msgs in
example : parseDecimalBoundedFold (2 ^ 64) 0 ascii!"42" = none := by
  decide

example (n : Nat) : parseDecimalNat (formatDecimalNat n) = some n :=
  parseDecimalNat_formatDecimalNat n

example (v : BitVec 64) : parseDecimalU64 (formatDecimalNat v.toNat) = some v :=
  parseDecimalU64_formatDecimalNat v

example (v : BitVec 32) : parseDecimalU32 (formatDecimalNat v.toNat) = some v :=
  parseDecimalU32_formatDecimalNat v

end ProofLib.Testing.AsciiNum
