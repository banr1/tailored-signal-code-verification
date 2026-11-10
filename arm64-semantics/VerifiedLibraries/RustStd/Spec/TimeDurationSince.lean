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
# `SystemTime::duration_since` Specification

Hoare specification `timeDurationSinceSpec` for `<std::time::SystemTime>::duration_since` in
`timeMultiLib`, computing `|t1 - t2|` across bytes `0..20` of `sret` (`x8`) without reading
padding `@12` of `self` or panicking when `n1, n2 < 10 ^ 9`.
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-- Demangled symbol name of `SystemTime::duration_since` in `timeMultiLib`. -/
abbrev timeDurationSinceSym : String :=
  "<std::time::SystemTime>::duration_since"

/-- Read-only 16-byte `.rodata` piece symbol (`timePlacedData0`, `[1, 0, ..., 0]`) read by
    `Timespec::sub_timespec` on the `self < other` path (`eor v0.16b` flips the `Result` tag;
    `c16 = mpl.ρ timeRodataCst16Sym`). -/
abbrev timeRodataCst16Sym : String :=
  "rust_time:.rodata.cst16+0x0"

/-- `SystemTime::duration_since(&self, earlier) -> Result<Duration, SystemTimeError>`.

    `c16` is the placement-fixed address `mpl.ρ timeRodataCst16Sym` of `timePlacedData0`.
    ABI: `x0 = p` (`&self`: `tv_sec` at `@0`, `tv_nsec` at `@8`; padding at `@12` is unread),
    `earlier = (x1 = s2 : i64, w2 = n2 : u32)`, and `x8 = ret` (24-byte `sret`: bytes `0..20`
    written, bytes `20..24` kept at `b20`). Uses 208 bytes of stack (`0x50` in `duration_since`
    plus two `0x40` frames in `sub_timespec`); panic is unreachable for `n1, n2 < 10 ^ 9`
    (`onPanic = ⌜False⌝`). -/
rust_spec timeDurationSinceSpec (ctx c16 : ptr)
    (p : ptr) (s2 : i64) (n2 : u32) (ret : sret) (sp : sp)
    (ghost s1 : i64) (ghost n1 : u32) (ghost b20 : u32)
  requires_cond n1.toNat < 10 ^ 9 ∧ n2.toNat < 10 ^ 9
  preserves     (p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗
                ((ret + 20#64) ↦₃₂ b20) ∗
                (c16 ↦ᵣ timePlacedData0) ∗
                stackFrameAt sp 208
  requires      memRegion ret 20
  let t1 : Int := s1.toInt * 10 ^ 9 + n1.toNat
  let t2 : Int := s2.toInt * 10 ^ 9 + n2.toNat
  let d  : Nat := (t1 - t2).natAbs
  ensures       (ret ↦₆₄ (if t2 ≤ t1 then 0#64 else 1#64)) ∗
                ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
                ((ret + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9))
  ensures_pure  sf.trace = s0.trace ∧ sf.fs = s0.fs

end VerifiedLibraries.RustStd
