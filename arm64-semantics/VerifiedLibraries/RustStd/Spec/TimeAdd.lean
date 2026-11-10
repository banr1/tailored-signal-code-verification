/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.RustStd.Spec.IoCommon
public import VerifiedLibraries.RustStd.Generated.TimePlacedObj

/-!
# `<SystemTime as Add<Duration>>::add` Specification

Pure model (`Timespec`, `Duration`, `timespecCheckedAdd`) and Hoare specification (`timeAddSpec`)
for `<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add` in `timeMultiLib`,
returning `(r.sec, r.nsec.zeroExtend 64)` in `(x0, x1)` on `some r` and panicking via
`core::option::expect_failed` on overflow (`none`).
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-- Demangled symbol name of `<SystemTime as Add<Duration>>::add` in `timeMultiLib`. -/
abbrev timeAddSym : String :=
  "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add"

/-- Rust `std::sys::pal::unix::time::Timespec` (`tv_sec : i64`, `tv_nsec : u32`). Distinct from
    `Arm64.Timespec` (whose `nsec` has type `Fin 1000000000`). -/
structure Timespec where
  sec  : BitVec 64
  nsec : BitVec 32
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Rust `core::time::Duration` (`secs : u64`, `nanos : u32`). -/
structure Duration where
  secs  : BitVec 64
  nanos : BitVec 32
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Pure model of `Timespec::checked_add_duration` (`std/src/sys/pal/unix/time.rs:145-156`,
    called by `<SystemTime as Add<Duration>>::add` in `std/src/time.rs:738-748`):
    1. `secs := t.sec.toInt + d.secs.toNat` (`none` if `secs > i64::MAX`, matching
       `i64::checked_add_unsigned`);
    2. `nsec := t.nsec.toNat + d.nanos.toNat`;
    3. if `nsec >= 10 ^ 9`, subtract `10 ^ 9` and add `1` to `secs`
       (`none` if `secs + 1 > i64::MAX`). -/
def timespecCheckedAdd (t : Timespec) (d : Duration) : Option Timespec :=
  let secs : Int := t.sec.toInt + d.secs.toNat
  if 2 ^ 63 - 1 < secs then
    none
  else
    let nsec : Nat := t.nsec.toNat + d.nanos.toNat
    if 10 ^ 9 ≤ nsec then
      let secs' : Int := secs + 1
      if 2 ^ 63 - 1 < secs' then
        none
      else
        some { sec := BitVec.ofInt 64 secs', nsec := BitVec.ofNat 32 (nsec - 10 ^ 9) }
    else
      some { sec := BitVec.ofInt 64 secs, nsec := BitVec.ofNat 32 nsec }

/-- `<SystemTime as Add<Duration>>::add(self, dur) -> SystemTime` (`std/src/time.rs:738-748`).
    - ABI: `self = (x0 : i64, w1 : u32)`, `dur = (x2 : u64, w3 : u32)`, `x4` = panic `Location`
      (unconstrained); returns `(x0 : i64, w1 : u32)` with `w1` zero-extended to `x1`.
    - Stack: `stackFrameAt s0.sp 16` (frameless on normal return; `stp x29, x30, [sp, #-0x10]!`
      on overflow before `bl core::option::expect_failed`). -/
def timeAddSpec : Spec (Timespec × Duration) where
  pre := fun (t, d) s0 =>
    ⌜s0.readReg64 .x0 = t.sec ∧ s0.readReg32 .x1 = t.nsec ∧
      s0.readReg64 .x2 = d.secs ∧ s0.readReg32 .x3 = d.nanos ∧
      t.nsec.toNat < 10 ^ 9 ∧ d.nanos.toNat < 10 ^ 9⌝ ∗
      stackFrameAt s0.sp 16
  post := fun (t, d) s0 sf =>
    ⌜(∃ r, timespecCheckedAdd t d = some r ∧
        sf.readReg64 .x0 = r.sec ∧ sf.readReg64 .x1 = r.nsec.zeroExtend 64) ∧
      sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      stackFrameAt s0.sp 16
  onPanic := fun (t, d) s0 sf =>
    ⌜timespecCheckedAdd t d = none ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      stackFrameAt s0.sp 16

end VerifiedLibraries.RustStd
