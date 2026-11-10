/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.RustStd.Spec.Top
public import VerifiedLibraries.RustStd.Spec.CoreFmtWrite

/-!
# `core::fmt::Display` and `Formatter` Padding Specifications

Defines contracts for `coreFmtMultiLib` (`rustc 1.98.1`, `aarch64-unknown-linux-musl`):
- `Formatter::pad` and the `str`, `&str`, and `String` `Display::fmt` contracts on the
  no-width/no-precision fast path (`FmtPadFastOpts`: neither `HAVE_WIDTH` bit 27 nor
  `HAVE_PRECISION` bit 28 set);
- `Formatter::pad_integral` and the unsigned decimal `Display::fmt` contracts (`u8`, `u32`, `u64`,
  `usize`) for all non-alternate option combinations (`opts.flags.getLsbD 23 = false`), including
  width padding, alignment, fill character, `SIGN_PLUS` (bit 21), and `SIGN_AWARE_ZERO_PAD`
  (bit 24).
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-! ## Symbol names and digit table -/

/-- Demangled symbol name of `<core::fmt::Formatter>::write_str` (`coreFmtMultiLib` block 2). -/
abbrev formatterWriteStrSym : String :=
  "<core::fmt::Formatter>::write_str"

/-- Demangled symbol name of `<core::fmt::Formatter>::pad` (`coreFmtMultiLib` block 1). -/
abbrev formatterPadSym : String :=
  "<core::fmt::Formatter>::pad"

/-- Demangled symbol name of `<core::fmt::Formatter>::pad_integral` (`coreFmtMultiLib` block 0). -/
abbrev formatterPadIntegralSym : String :=
  "<core::fmt::Formatter>::pad_integral"

/-- Demangled symbol name of `<str as core::fmt::Display>::fmt` (`coreFmtMultiLib` block 10). -/
abbrev strDisplayFmtSym : String :=
  "<str as core::fmt::Display>::fmt"

/-- Demangled symbol name of `<&str as core::fmt::Display>::fmt` (`coreFmtMultiLib` block 7). -/
abbrev strRefDisplayFmtSym : String :=
  "<&str as core::fmt::Display>::fmt"

/-- Demangled symbol name of `<alloc::string::String as core::fmt::Display>::fmt`. -/
abbrev stringDisplayFmtSym : String :=
  "<alloc::string::String as core::fmt::Display>::fmt"

/-- Demangled symbol name of `<u8 as core::fmt::Display>::fmt` (`coreFmtMultiLib` block 6). -/
abbrev u8DisplayFmtSym : String :=
  "<u8 as core::fmt::Display>::fmt"

/-- Demangled symbol name of `<u32 as core::fmt::Display>::fmt` (`coreFmtMultiLib` block 8). -/
abbrev u32DisplayFmtSym : String :=
  "<u32 as core::fmt::Display>::fmt"

/-- Demangled symbol name of `<u64 as core::fmt::Display>::fmt` (`coreFmtMultiLib` block 9). -/
abbrev u64DisplayFmtSym : String :=
  "<u64 as core::fmt::Display>::fmt"

/-- Demangled symbol name of `<usize as core::fmt::Display>::fmt` (`coreFmtMultiLib` block 9,
    aliased at offset 0 with `u64DisplayFmtSym` on 64-bit targets). -/
abbrev usizeDisplayFmtSym : String :=
  "<usize as core::fmt::Display>::fmt"

/-- Harness name of the 200-byte read-only `DEC_DIGITS_LUT` table (`"000102...99"`) in
    `coreFmtMultiLib` (data 2). -/
abbrev coreFmtDecDigitsLutSym : String :=
  "rust_core_fmt:.rodata..Lanon.203"

/-- The 200 ASCII bytes `"000102...99"` of `core::fmt::num::DEC_DIGITS_LUT`. -/
def decDigitsLutBytes : List (BitVec 8) :=
  (List.range 100).flatMap fun i =>
    [BitVec.ofNat 8 (48 + i / 10), BitVec.ofNat 8 (48 + i % 10)]

/-! ## Value and slice footprints -/

/-- Byte slice `bs` at `ptr`, owned read-only (`ro = true`) or read-write (`ro = false`). -/
def fmtSrcBytes (ro : Bool) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if ro then (ptr ↦ᵣ bs) else (ptr ↦ₛ bs)

/-- 1-byte `u8` reference at `p`, owned read-only (`ro = true`) or read-write (`ro = false`). -/
def fmtRef8 (ro : Bool) (p : BitVec 64) (v : BitVec 8) : SepProp :=
  if ro then (p ↦₈ᵣ v) else (p ↦₈ v)

/-- 4-byte `u32` reference at `p`, owned read-only (`ro = true`) or read-write (`ro = false`). -/
def fmtRef32 (ro : Bool) (p : BitVec 64) (v : BitVec 32) : SepProp :=
  if ro then (p ↦₃₂ᵣ v) else (p ↦₃₂ v)

/-- 8-byte `u64` / `usize` reference at `p`, owned read-only (`ro = true`) or read-write
    (`ro = false`). -/
def fmtRef64 (ro : Bool) (p : BitVec 64) (v : BitVec 64) : SepProp :=
  if ro then (p ↦₆₄ᵣ v) else (p ↦₆₄ v)

/-- 16-byte `&str` fat pointer `{ptr @ +0, len @ +8}` at `p`, owned read-only (`ro = true`) or
    read-write (`ro = false`). -/
def fmtRefStr (ro : Bool) (p ptr len : BitVec 64) : SepProp :=
  if ro then (p ↦₆₄ᵣ ptr) ∗ ((p + 8#64) ↦₆₄ᵣ len)
  else (p ↦₆₄ ptr) ∗ ((p + 8#64) ↦₆₄ len)

/-- 24-byte `alloc::string::String` header `{cap @ +0, ptr @ +8, len @ +16}` at `p`, owned
    read-only (`ro = true`) or read-write (`ro = false`, matching `vecHeader`). -/
def fmtRefString (ro : Bool) (p cap ptr len : BitVec 64) : SepProp :=
  if ro then (p ↦₆₄ᵣ cap) ∗ ((p + 8#64) ↦₆₄ᵣ ptr) ∗ ((p + 16#64) ↦₆₄ᵣ len)
  else vecHeader p cap ptr len

/-! ## `core::fmt::Write` protocol and operation runs -/

/-- UTF-8 byte length emitted by `Write::write_char` for code point word `c`. -/
def charUtf8Len (c : BitVec 32) : Nat :=
  if c.toNat < 128 then 1 else if c.toNat < 2048 then 2 else if c.toNat < 65536 then 3 else 4

/-- One `core::fmt::Write` method call emitted by a `Formatter` helper: `write_str(bs)` or
    `write_char(c)`. -/
inductive FmtOp where
  | str (bs : List (BitVec 8))
  | char (c : BitVec 32)
  deriving DecidableEq, Repr

/-- Number of output bytes appended by one `FmtOp`. -/
def FmtOp.byteLen : FmtOp → Nat
  | .str bs => bs.length
  | .char c => charUtf8Len c

/-- Sequential execution of `ops` from writer state `st` under `StrStep` / `CharStep`, stopping at
    the first `Err` (`ok = false`). -/
inductive FmtOpsRun {σ : Type} (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (CharStep : σ → BitVec 32 → Bool → σ → Prop) : List FmtOp → σ → Bool → σ → Prop
  | nil (st : σ) : FmtOpsRun StrStep CharStep [] st true st
  | str_ok {bs : List (BitVec 8)} {ops : List FmtOp} {st st' st'' : σ} {b : Bool} :
      StrStep st bs true st' → FmtOpsRun StrStep CharStep ops st' b st'' →
      FmtOpsRun StrStep CharStep (.str bs :: ops) st b st''
  | str_err {bs : List (BitVec 8)} {ops : List FmtOp} {st st' : σ} :
      StrStep st bs false st' → FmtOpsRun StrStep CharStep (.str bs :: ops) st false st'
  | char_ok {c : BitVec 32} {ops : List FmtOp} {st st' st'' : σ} {b : Bool} :
      CharStep st c true st' → FmtOpsRun StrStep CharStep ops st' b st'' →
      FmtOpsRun StrStep CharStep (.char c :: ops) st b st''
  | char_err {c : BitVec 32} {ops : List FmtOp} {st st' : σ} :
      CharStep st c false st' → FmtOpsRun StrStep CharStep (.char c :: ops) st false st'

/-- Abort outcome (`onPanic` or `onOom`) of running `ops` from writer state `st`: some `op` in
    `ops` was reached after an `Ok` prefix ending in `st_i`, and `Abort st_i op.byteLen sf`
    held. -/
def FmtOpsAbort {σ : Type} (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (CharStep : σ → BitVec 32 → Bool → σ → Prop)
    (Abort : σ → Nat → State → Prop) (ops : List FmtOp) (st : σ) (sf : State) : Prop :=
  ∃ pre op post st_i, ops = pre ++ op :: post ∧
    FmtOpsRun StrStep CharStep pre st true st_i ∧ Abort st_i op.byteLen sf

/-- `Write::write_str(out, ptr, bs.length)` (`[vt + 0x18]`) on writer `(W, StrStep, Panic, Oom)`
    for slices shorter than `2 ^ 60` bytes. Ghost: writer state `st`. -/
def fmtWriterStrSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (out : BitVec 64) (ro : Bool) (ptr : BitVec 64) (bs : List (BitVec 8)) : Spec σ where
  pre := fun st s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = ptr ∧ (s.readReg64 .x2).toNat = bs.length ∧
      bs.length < 2 ^ 60⌝ ∗
      fmtSrcBytes ro ptr bs ∗ W st s ∗ stackFrameAt s.sp stackBytes
  post := fun st s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
        fmtSrcBytes ro ptr bs ∗ W st' sf ∗ stackFrameAt s0.sp stackBytes
  onPanic := fun st _ sf => ⌜Panic st bs.length sf⌝ ∗ anyHeap
  onOom := fun st _ sf => ⌜Oom st bs.length sf⌝

/-- `Write::write_char(out, c)` (`[vt + 0x20]`) on writer `(W, CharStep, Panic, Oom)`.
    Ghost: writer state `st`. -/
def fmtWriterCharSpec {σ : Type} (W : σ → State → SepProp)
    (CharStep : σ → BitVec 32 → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (out : BitVec 64) (c : BitVec 32) : Spec σ where
  pre := fun st s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg32 .x1 = c⌝ ∗
      W st s ∗ stackFrameAt s.sp stackBytes
  post := fun st s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ CharStep st c ok st'⌝ ∗
        W st' sf ∗ stackFrameAt s0.sp stackBytes
  onPanic := fun st _ sf => ⌜Panic st (charUtf8Len c) sf⌝ ∗ anyHeap
  onOom := fun st _ sf => ⌜Oom st (charUtf8Len c) sf⌝

/-- Well-behaved `core::fmt::Write` implementation at `(out, vt)` with `write_str` at `wsFn` and
    `write_char` at `wcFn`:
    - `transport`: `W st` is stable under `FmtWriteFrame`;
    - `slots`: `W st s` carries read-only copies of `[vt + 0x18] = wsFn` and `[vt + 0x20] = wcFn`;
    - `write_str` / `write_char`: meet `fmtWriterStrSpec` / `fmtWriterCharSpec`. -/
structure FmtWriterOk {σ : Type} (P : Program) (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (CharStep : σ → BitVec 32 → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (out vt wsFn wcFn : BitVec 64) : Prop where
  transport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s'
  slots : ∀ (st : σ) (s : State),
    W st s = ((vt + 0x18#64) ↦₆₄ᵣ wsFn) ∗ ((vt + 0x20#64) ↦₆₄ᵣ wcFn) ∗ W st s
  write_str : ∀ (ro : Bool) (ptr : BitVec 64) (bs : List (BitVec 8)),
    subroutine_ok P wsFn (fmtWriterStrSpec W StrStep Panic Oom stackBytes out ro ptr bs)
  write_char : ∀ c : BitVec 32,
    subroutine_ok P wcFn (fmtWriterCharSpec W CharStep Panic Oom stackBytes out c)

/-! ## Formatting options and `pad_integral` operation sequence -/

/-- `Formatter::pad` fast-path condition (`tst w22, #0x18000000` at `pad+0x24`): neither
    `HAVE_WIDTH` (bit 27) nor `HAVE_PRECISION` (bit 28) is set in `opts.flags`. -/
def FmtPadFastOpts (opts : FmtOptions) : Prop :=
  opts.flags &&& 0x18000000#32 = 0#32

/-- Fill character stored in the low 21 bits of `opts.flags` (`opts.flags & 0x1f_ffff`). -/
def fmtFillChar (opts : FmtOptions) : BitVec 32 :=
  opts.flags &&& 0x1fffff#32

/-- Leading sign call emitted by `pad_integral`: `'+'` (`0x2b`) when `isNonneg = true` and
    `SIGN_PLUS` (bit 21) is set, `'-'` (`0x2d`) when `isNonneg = false`, and `[]` otherwise. -/
def fmtSignOp (opts : FmtOptions) (isNonneg : Bool) : List FmtOp :=
  if isNonneg then
    if opts.flags.getLsbD 21 then [.char 0x2b#32] else []
  else
    [.char 0x2d#32]

/-- Left/right fill split of `pad` characters under `opts.flags` alignment bits `29..30`:
    `0` (`Left` `<`) gives `(0, pad)`, `2` (`Center` `^`) gives `(pad / 2, pad - pad / 2)`, and
    `1` (`Right` `>`) or `3` (`Unknown`) gives `(pad, 0)`. -/
def fmtPadSplit (opts : FmtOptions) (pad : Nat) : Nat × Nat :=
  match (opts.flags >>> 29).toNat % 4 with
  | 0 => (0, pad)
  | 2 => (pad / 2, pad - pad / 2)
  | _ => (pad, 0)

/-- Exact writer call sequence of `Formatter::pad_integral` when the alternate `#` flag (bit 23) is
    clear (`opts.flags.getLsbD 23 = false`), for `isNonneg` and digit bytes `ds`. -/
def padIntegralNoAltOps (opts : FmtOptions) (isNonneg : Bool) (ds : List (BitVec 8)) :
    List FmtOp :=
  let sign := fmtSignOp opts isNonneg
  let pad := opts.width.toNat - (sign.length + ds.length)
  if opts.flags.getLsbD 24 then
    sign ++ List.replicate pad (.char 0x30#32) ++ [.str ds]
  else
    let (lp, rp) := fmtPadSplit opts pad
    List.replicate lp (.char (fmtFillChar opts)) ++ sign ++ [.str ds] ++
      List.replicate rp (.char (fmtFillChar opts))

/-! ## Subroutine contracts -/

/-- `<core::fmt::Formatter>::write_str(f = x0, ptr = x1, len = x2)`. Ghost: writer state `st`. -/
def formatterWriteStrSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (f out vt : BitVec 64) (opts : FmtOptions) (ro : Bool) (ptr : BitVec 64)
    (bs : List (BitVec 8)) : Spec σ where
  pre := fun st s =>
    ⌜s.readReg64 .x0 = f ∧ s.readReg64 .x1 = ptr ∧ (s.readReg64 .x2).toNat = bs.length ∧
      bs.length < 2 ^ 60⌝ ∗
      formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st s ∗
      stackFrameAt s.sp stackBytes
  post := fun st s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
        formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st' sf ∗
        stackFrameAt s0.sp stackBytes
  onPanic := fun st _ sf => ⌜Panic st bs.length sf⌝ ∗ anyHeap
  onOom := fun st _ sf => ⌜Oom st bs.length sf⌝

/-- `<core::fmt::Formatter>::pad(f = x0, ptr = x1, len = x2)` on the no-width/no-precision fast
    path (`FmtPadFastOpts opts`). Pushes and pops an `80`-byte (`0x50`) frame before tail-calling
    `[vt + 0x18]`. Ghost: writer state `st`. -/
def formatterPadSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (f out vt : BitVec 64) (opts : FmtOptions) (ro : Bool) (ptr : BitVec 64)
    (bs : List (BitVec 8)) : Spec σ where
  pre := fun st s =>
    ⌜s.readReg64 .x0 = f ∧ s.readReg64 .x1 = ptr ∧ (s.readReg64 .x2).toNat = bs.length ∧
      bs.length < 2 ^ 60 ∧ FmtPadFastOpts opts⌝ ∗
      formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st s ∗
      stackFrameAt s.sp (max 80 stackBytes)
  post := fun st s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
        formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st' sf ∗
        stackFrameAt s0.sp (max 80 stackBytes)
  onPanic := fun st _ sf => ⌜Panic st bs.length sf⌝ ∗ anyHeap
  onOom := fun st _ sf => ⌜Oom st bs.length sf⌝

/-- `<str as core::fmt::Display>::fmt(ptr = x0, len = x1, f = x2)` (3-register unsized-DST ABI) on
    the `FmtPadFastOpts` fast path. Ghost: `(st, f)`. -/
def strDisplayFmtSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (out vt : BitVec 64) (opts : FmtOptions) (ro : Bool) (ptr : BitVec 64)
    (bs : List (BitVec 8)) : Spec (σ × BitVec 64) where
  pre := fun (st, f) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x2 = f ∧
      bs.length < 2 ^ 60 ∧ FmtPadFastOpts opts⌝ ∗
      formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st s ∗
      stackFrameAt s.sp (max 80 stackBytes)
  post := fun (st, f) s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
        formatterAt f out vt opts ∗ fmtSrcBytes ro ptr bs ∗ W st' sf ∗
        stackFrameAt s0.sp (max 80 stackBytes)
  onPanic := fun (st, _) _ sf => ⌜Panic st bs.length sf⌝ ∗ anyHeap
  onOom := fun (st, _) _ sf => ⌜Oom st bs.length sf⌝

/-- `<&str as core::fmt::Display>::fmt(valPtr = x0, f = x1)` (2-register `rt::Argument` ABI) on the
    `FmtPadFastOpts` fast path. Ghost: `(st, f)`. -/
def strRefDisplayFmtSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (out vt : BitVec 64) (opts : FmtOptions) (refRo srcRo : Bool) (valPtr ptr : BitVec 64)
    (bs : List (BitVec 8)) : Spec (σ × BitVec 64) where
  pre := fun (st, f) s =>
    ⌜s.readReg64 .x0 = valPtr ∧ s.readReg64 .x1 = f ∧ bs.length < 2 ^ 60 ∧
      FmtPadFastOpts opts⌝ ∗
      fmtRefStr refRo valPtr ptr (BitVec.ofNat 64 bs.length) ∗
      formatterAt f out vt opts ∗ fmtSrcBytes srcRo ptr bs ∗ W st s ∗
      stackFrameAt s.sp (max 80 stackBytes)
  post := fun (st, f) s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
        fmtRefStr refRo valPtr ptr (BitVec.ofNat 64 bs.length) ∗
        formatterAt f out vt opts ∗ fmtSrcBytes srcRo ptr bs ∗ W st' sf ∗
        stackFrameAt s0.sp (max 80 stackBytes)
  onPanic := fun (st, _) _ sf => ⌜Panic st bs.length sf⌝ ∗ anyHeap
  onOom := fun (st, _) _ sf => ⌜Oom st bs.length sf⌝

/-- `<alloc::string::String as core::fmt::Display>::fmt(valPtr = x0, f = x1)` (2-register
    `rt::Argument` ABI) on the `FmtPadFastOpts` fast path. Ghost: `(st, f)`. -/
def stringDisplayFmtSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (out vt : BitVec 64) (opts : FmtOptions) (refRo srcRo : Bool) (valPtr cap ptr : BitVec 64)
    (bs : List (BitVec 8)) : Spec (σ × BitVec 64) where
  pre := fun (st, f) s =>
    ⌜s.readReg64 .x0 = valPtr ∧ s.readReg64 .x1 = f ∧ bs.length < 2 ^ 60 ∧
      FmtPadFastOpts opts⌝ ∗
      fmtRefString refRo valPtr cap ptr (BitVec.ofNat 64 bs.length) ∗
      formatterAt f out vt opts ∗ fmtSrcBytes srcRo ptr bs ∗ W st s ∗
      stackFrameAt s.sp (max 80 stackBytes)
  post := fun (st, f) s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧ StrStep st bs ok st'⌝ ∗
        fmtRefString refRo valPtr cap ptr (BitVec.ofNat 64 bs.length) ∗
        formatterAt f out vt opts ∗ fmtSrcBytes srcRo ptr bs ∗ W st' sf ∗
        stackFrameAt s0.sp (max 80 stackBytes)
  onPanic := fun (st, _) _ sf => ⌜Panic st bs.length sf⌝ ∗ anyHeap
  onOom := fun (st, _) _ sf => ⌜Oom st bs.length sf⌝

/-- `<core::fmt::Formatter>::pad_integral(f = x0, is_nonneg = w1, pfx_ptr = x2, pfx_len = x3,
    ds_ptr = x4, ds_len = x5)` when the alternate `#` flag is clear (`opts.flags.getLsbD 23 = false`).
    On `SIGN_AWARE_ZERO_PAD` (`bit 24`), `pad_integral+0x284` mutates `[f + 0x10]` and restores it
    at `+0x2f0` on `Ok`, leaving `memRegion f 24` on `Err`. Ghost: writer state `st`. -/
def formatterPadIntegralSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (CharStep : σ → BitVec 32 → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (f out vt : BitVec 64) (opts : FmtOptions) (isNonneg : Bool) (ro : Bool) (dsPtr : BitVec 64)
    (ds : List (BitVec 8)) : Spec σ where
  pre := fun st s =>
    ⌜s.readReg64 .x0 = f ∧ s.readReg32 .x1 = (if isNonneg then 1#32 else 0#32) ∧
      s.readReg64 .x4 = dsPtr ∧ (s.readReg64 .x5).toNat = ds.length ∧
      ds.length < 2 ^ 60 ∧ opts.flags.getLsbD 23 = false⌝ ∗
      formatterAt f out vt opts ∗ fmtSrcBytes ro dsPtr ds ∗ W st s ∗
      stackFrameAt s.sp (160 + stackBytes)
  post := fun st s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧
        FmtOpsRun StrStep CharStep (padIntegralNoAltOps opts isNonneg ds) st ok st'⌝ ∗
        (if ok then formatterAt f out vt opts else memRegion f 24) ∗
        fmtSrcBytes ro dsPtr ds ∗ W st' sf ∗ stackFrameAt s0.sp (160 + stackBytes)
  onPanic := fun st _ sf =>
    ⌜FmtOpsAbort StrStep CharStep Panic (padIntegralNoAltOps opts isNonneg ds) st sf⌝ ∗ anyHeap
  onOom := fun st _ sf =>
    ⌜FmtOpsAbort StrStep CharStep Oom (padIntegralNoAltOps opts isNonneg ds) st sf⌝

/-- `<u8 as core::fmt::Display>::fmt(valPtr = x0, f = x1)` under `opts.flags.getLsbD 23 = false`.
    Formats `v.toNat` in base 10 (`formatDecimalNat v.toNat`) using the 200-byte read-only
    `DEC_DIGITS_LUT` at `lutAddr`, then delegates to `pad_integral`. Ghost: `(st, f)`. -/
def u8DisplayFmtSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (CharStep : σ → BitVec 32 → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (lutAddr out vt : BitVec 64) (opts : FmtOptions) (ro : Bool) (valPtr : BitVec 64)
    (v : BitVec 8) : Spec (σ × BitVec 64) where
  pre := fun (st, f) s =>
    ⌜s.readReg64 .x0 = valPtr ∧ s.readReg64 .x1 = f ∧ opts.flags.getLsbD 23 = false⌝ ∗
      fmtRef8 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
      formatterAt f out vt opts ∗ W st s ∗ stackFrameAt s.sp (192 + stackBytes)
  post := fun (st, f) s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧
        FmtOpsRun StrStep CharStep
          (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st ok st'⌝ ∗
        fmtRef8 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
        (if ok then formatterAt f out vt opts else memRegion f 24) ∗
        W st' sf ∗ stackFrameAt s0.sp (192 + stackBytes)
  onPanic := fun (st, _) _ sf =>
    ⌜FmtOpsAbort StrStep CharStep Panic
      (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf⌝ ∗ anyHeap
  onOom := fun (st, _) _ sf =>
    ⌜FmtOpsAbort StrStep CharStep Oom
      (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf⌝

/-- `<u32 as core::fmt::Display>::fmt(valPtr = x0, f = x1)` under `opts.flags.getLsbD 23 = false`.
    Formats `v.toNat` in base 10 (`formatDecimalNat v.toNat`) using `DEC_DIGITS_LUT` at `lutAddr`,
    then delegates to `pad_integral`. Ghost: `(st, f)`. -/
def u32DisplayFmtSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (CharStep : σ → BitVec 32 → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (lutAddr out vt : BitVec 64) (opts : FmtOptions) (ro : Bool) (valPtr : BitVec 64)
    (v : BitVec 32) : Spec (σ × BitVec 64) where
  pre := fun (st, f) s =>
    ⌜s.readReg64 .x0 = valPtr ∧ s.readReg64 .x1 = f ∧ opts.flags.getLsbD 23 = false⌝ ∗
      fmtRef32 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
      formatterAt f out vt opts ∗ W st s ∗ stackFrameAt s.sp (192 + stackBytes)
  post := fun (st, f) s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧
        FmtOpsRun StrStep CharStep
          (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st ok st'⌝ ∗
        fmtRef32 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
        (if ok then formatterAt f out vt opts else memRegion f 24) ∗
        W st' sf ∗ stackFrameAt s0.sp (192 + stackBytes)
  onPanic := fun (st, _) _ sf =>
    ⌜FmtOpsAbort StrStep CharStep Panic
      (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf⌝ ∗ anyHeap
  onOom := fun (st, _) _ sf =>
    ⌜FmtOpsAbort StrStep CharStep Oom
      (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf⌝

/-- `<u64 as core::fmt::Display>::fmt` and `<usize as core::fmt::Display>::fmt`
    `(valPtr = x0, f = x1)` under `opts.flags.getLsbD 23 = false` (both share the same 96-byte
    block on 64-bit targets). Formats `v.toNat` in base 10 (`formatDecimalNat v.toNat`) using
    `DEC_DIGITS_LUT` at `lutAddr`, then delegates to `pad_integral`. Ghost: `(st, f)`. -/
def u64DisplayFmtSpec {σ : Type} (W : σ → State → SepProp)
    (StrStep : σ → List (BitVec 8) → Bool → σ → Prop)
    (CharStep : σ → BitVec 32 → Bool → σ → Prop)
    (Panic Oom : σ → Nat → State → Prop) (stackBytes : Nat)
    (lutAddr out vt : BitVec 64) (opts : FmtOptions) (ro : Bool) (valPtr v : BitVec 64) :
    Spec (σ × BitVec 64) where
  pre := fun (st, f) s =>
    ⌜s.readReg64 .x0 = valPtr ∧ s.readReg64 .x1 = f ∧ opts.flags.getLsbD 23 = false⌝ ∗
      fmtRef64 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
      formatterAt f out vt opts ∗ W st s ∗ stackFrameAt s.sp (240 + stackBytes)
  post := fun (st, f) s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧
        FmtOpsRun StrStep CharStep
          (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st ok st'⌝ ∗
        fmtRef64 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗
        (if ok then formatterAt f out vt opts else memRegion f 24) ∗
        W st' sf ∗ stackFrameAt s0.sp (240 + stackBytes)
  onPanic := fun (st, _) _ sf =>
    ⌜FmtOpsAbort StrStep CharStep Panic
      (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf⌝ ∗ anyHeap
  onOom := fun (st, _) _ sf =>
    ⌜FmtOpsAbort StrStep CharStep Oom
      (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf⌝

end VerifiedLibraries.RustStd
