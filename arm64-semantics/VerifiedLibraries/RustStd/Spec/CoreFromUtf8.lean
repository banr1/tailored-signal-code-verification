/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.RustStd.Generated.CorePlacedObj

/-!
# `core::str::from_utf8` Specification

Functional model (`Utf8Error`, `runUtf8Validation`) and relational specifications
(`coreFromUtf8Spec`, `coreFromUtf8ROSpec`) for `core::str::converts::from_utf8` (`coreFromUtf8Sym`,
block 1 of `coreMultiLib`), with `run_utf8_validation` inlined as a frameless leaf reading the
256-byte `UTF8_CHAR_WIDTH` table (`coreUtf8CharWidthSym`, `corePlacedData1`) at placed address `tbl`.

The 24-byte `Result<&str, Utf8Error>` sret buffer at `x8 = ret` has layout:
- `Ok(s)`: `ret ↦₆₄ 0`, `(ret + 8) ↦₆₄ p`, `(ret + 16) ↦₆₄ len`.
- `Err(e)`: `ret ↦₆₄ 1`, `(ret + 8) ↦₆₄ e.valid_up_to`, `error_len : Option<u8>` as a 1-byte tag at
  `+16` and 1-byte payload at `+17` (for `none`, tag `0` and an unspecified scratch byte written by
  `strb w13, [x8, #17]`), while bytes `+18..+24` (`b18` at `+18`, `b20` at `+20`) remain untouched.
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-! ## Harness Symbols -/

/-- Demangled symbol name of `core::str::converts::from_utf8` in `coreMultiLib` (block 1). -/
abbrev coreFromUtf8Sym : String :=
  "core::str::converts::from_utf8"

/-- Harness name of the read-only 256-byte `UTF8_CHAR_WIDTH` table in `coreMultiLib` (bytes
    `corePlacedData1`); its placed address is the specification context parameter `tbl`. -/
abbrev coreUtf8CharWidthSym : String :=
  "rust_core:.rodata..Lanon.208"

/-! ## Pure Model of `run_utf8_validation` -/

/-- `core::str::Utf8Error` (`core/src/str/error.rs`): `valid_up_to` is the byte index of the first
    invalid or incomplete sequence (the length of the longest valid prefix); `error_len` is `none`
    when input ends mid-sequence, and `some k` (`k ∈ {1, 2, 3}`) when an unexpected byte terminates
    an invalid sequence after `k` bytes. -/
structure Utf8Error where
  valid_up_to : Nat
  error_len : Option (BitVec 8)
  deriving DecidableEq, Repr

/-- `b` is a UTF-8 continuation byte (`0x80 ≤ b ≤ 0xbf`, i.e. `0b10xx_xxxx`). -/
def isUtf8ContByte (b : BitVec 8) : Bool :=
  0x80#8 ≤ b && b ≤ 0xbf#8

/-- `run_utf8_validation` starting at byte index `offset` (Unicode Table 3-7 / RFC 3629):
    `0x00..=0x7f` begins a 1-byte sequence; `0xc2..=0xdf` a 2-byte sequence; `0xe0..=0xef` a 3-byte
    sequence (second byte `0xa0..=0xbf` after `0xe0`, `0x80..=0x9f` after `0xed`); `0xf0..=0xf4` a
    4-byte sequence (second byte `0x90..=0xbf` after `0xf0`, `0x80..=0x8f` after `0xf4`); all other
    lead bytes fail with `error_len = some 1`. -/
def runUtf8ValidationLoop (offset : Nat) : List (BitVec 8) → Except Utf8Error Unit
  | [] => .ok ()
  | b0 :: rest =>
    if b0 < 0x80#8 then
      runUtf8ValidationLoop (offset + 1) rest
    else if 0xc2#8 ≤ b0 && b0 ≤ 0xdf#8 then
      match rest with
      | [] => .error { valid_up_to := offset, error_len := none }
      | b1 :: rest1 =>
        if isUtf8ContByte b1 then
          runUtf8ValidationLoop (offset + 2) rest1
        else
          .error { valid_up_to := offset, error_len := some 1#8 }
    else if 0xe0#8 ≤ b0 && b0 ≤ 0xef#8 then
      match rest with
      | [] => .error { valid_up_to := offset, error_len := none }
      | b1 :: rest1 =>
        let ok2 : Bool :=
          if b0 == 0xe0#8 then 0xa0#8 ≤ b1 && b1 ≤ 0xbf#8
          else if b0 == 0xed#8 then 0x80#8 ≤ b1 && b1 ≤ 0x9f#8
          else isUtf8ContByte b1
        if !ok2 then
          .error { valid_up_to := offset, error_len := some 1#8 }
        else match rest1 with
          | [] => .error { valid_up_to := offset, error_len := none }
          | b2 :: rest2 =>
            if isUtf8ContByte b2 then
              runUtf8ValidationLoop (offset + 3) rest2
            else
              .error { valid_up_to := offset, error_len := some 2#8 }
    else if 0xf0#8 ≤ b0 && b0 ≤ 0xf4#8 then
      match rest with
      | [] => .error { valid_up_to := offset, error_len := none }
      | b1 :: rest1 =>
        let ok2 : Bool :=
          if b0 == 0xf0#8 then 0x90#8 ≤ b1 && b1 ≤ 0xbf#8
          else if b0 == 0xf4#8 then 0x80#8 ≤ b1 && b1 ≤ 0x8f#8
          else isUtf8ContByte b1
        if !ok2 then
          .error { valid_up_to := offset, error_len := some 1#8 }
        else match rest1 with
          | [] => .error { valid_up_to := offset, error_len := none }
          | b2 :: rest2 =>
            if !isUtf8ContByte b2 then
              .error { valid_up_to := offset, error_len := some 2#8 }
            else match rest2 with
              | [] => .error { valid_up_to := offset, error_len := none }
              | b3 :: rest3 =>
                if isUtf8ContByte b3 then
                  runUtf8ValidationLoop (offset + 4) rest3
                else
                  .error { valid_up_to := offset, error_len := some 3#8 }
    else
      .error { valid_up_to := offset, error_len := some 1#8 }

/-- `core::str::validations::run_utf8_validation(bs)`: `.ok ()` iff `bs` is valid UTF-8, else the
    exact `Utf8Error`. -/
def runUtf8Validation (bs : List (BitVec 8)) : Except Utf8Error Unit :=
  runUtf8ValidationLoop 0 bs

/-! ## Sret Result Layout -/

/-- `Utf8Error.error_len : Option<u8>` at `a = ret + 16` (2 bytes): `some k` stores tag `1` at `a`
    and `k` at `a + 1`; `none` stores tag `0` at `a` and an unspecified scratch byte at `a + 1`. -/
def utf8ErrorLenAt (a : BitVec 64) : Option (BitVec 8) → SepProp
  | some k => (a ↦₈ 1#8) ∗ ((a + 1#64) ↦₈ k)
  | none => (a ↦₈ 0#8) ∗ (∃∗ pad17 : BitVec 8, (a + 1#64) ↦₈ pad17)

/-- Post-state of the 24-byte `Result<&str, Utf8Error>` buffer at `ret` for input `(p, len)` with
    entry values `b18` at `+18..+20` and `b20` at `+20..+24`. -/
def fromUtf8SretPost (ret p : BitVec 64) (len : Nat) (b18 : BitVec 16) (b20 : BitVec 32) :
    Except Utf8Error Unit → SepProp
  | .ok () =>
    (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ p) ∗ ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 len)
  | .error e =>
    (ret ↦₆₄ 1#64) ∗ ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 e.valid_up_to) ∗
      utf8ErrorLenAt (ret + 16#64) e.error_len ∗
      ((ret + 18#64) ↦₁₆ b18) ∗ ((ret + 20#64) ↦₃₂ b20)

/-! ## Specifications -/

/-- `core::str::from_utf8(v: &[u8]) -> Result<&str, Utf8Error>` with read-write input slice
    ownership `p ↦ₛ bs` and read-only `UTF8_CHAR_WIDTH` table at placed address `tbl` (`x0 = p`,
    `x1 = bs.length`, `x8 = ret`, frameless leaf). -/
rust_spec coreFromUtf8Spec (ctx tbl : ptr)
    (p : slice8 bs) (ret : sret)
    (ghost bs : List (BitVec 8)) (ghost b18 : u16) (ghost b20 : u32)
  requires_cond bs.length < 2 ^ 64
  preserves     (p ↦ₛ bs) ∗ (tbl ↦ᵣ corePlacedData1)
  requires      memRegion ret 18 ∗ ((ret + 18#64) ↦₁₆ b18) ∗ ((ret + 20#64) ↦₃₂ b20)
  ensures       fromUtf8SretPost ret p bs.length b18 b20 (runUtf8Validation bs)
  ensures_pure  sf.trace = s0.trace ∧ sf.fs = s0.fs

/-- `coreFromUtf8Spec` with read-only input slice ownership `p ↦ᵣ bs`. -/
rust_spec coreFromUtf8ROSpec (ctx tbl : ptr)
    (p : slice8 bs) (ret : sret)
    (ghost bs : List (BitVec 8)) (ghost b18 : u16) (ghost b20 : u32)
  requires_cond bs.length < 2 ^ 64
  preserves     (p ↦ᵣ bs) ∗ (tbl ↦ᵣ corePlacedData1)
  requires      memRegion ret 18 ∗ ((ret + 18#64) ↦₁₆ b18) ∗ ((ret + 20#64) ↦₃₂ b20)
  ensures       fromUtf8SretPost ret p bs.length b18 b20 (runUtf8Validation bs)
  ensures_pure  sf.trace = s0.trace ∧ sf.fs = s0.fs

end VerifiedLibraries.RustStd
