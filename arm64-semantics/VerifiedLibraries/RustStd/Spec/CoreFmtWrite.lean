/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64

/-!
# `core::fmt::write` Specification

Specifies `core::fmt::write(output: &mut dyn Write, fmt: Arguments<'_>)` (`core/src/fmt/mod.rs`,
block `0` of `coreMultiLib`, `aarch64-unknown-linux-musl`).

Calling convention (`x0 = output`, `x1 = vt`, `x2 = fmt.template`, `x3 = fmt.args`):
- `x3` odd (`Arguments::from_str`): `x2` points at a `str` of `x3 >>> 1` bytes, and `core::fmt::write`
  pops its frame and tail-calls `[vt + 0x18]` (`Write::write_str`) with `(output, x2, x3 >>> 1)`,
  passing `w0` through unchanged.
- `x3` even: `x2` points at the encoded template and `x3` at the `rt::Argument` array. A `0x70`-byte
  frame is pushed and the template is walked: literal pieces call `[vt + 0x18]` (`Write::write_str`),
  and placeholders populate a 24-byte `Formatter` at `sp_entry - 0x68` and call the argument's
  `fmtFn(value, &mut Formatter)`. Each callback result is tested on bit 0 of `w0`, returning `w0 = 1`
  on the first `Err` and `w0 = 0` when the template finishes.
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-! ## Harness name, `FormattingOptions`, and `Formatter` -/

/-- Demangled symbol name of `core::fmt::write` in `coreMultiLib` (block 0). -/
abbrev coreFmtWriteSym : String :=
  "core::fmt::write"

/-- `core::fmt::FormattingOptions` (`core/src/fmt/mod.rs`): `flags : u32`, `width : u16`,
    `precision : u16`. The defaults are `FormattingOptions::new()`:
    `flags = ' ' as u32 | ALIGN_UNKNOWN = 0x20 | 3 << 29 = 0x6000_0020`, `width = 0`,
    `precision = 0`. -/
structure FmtOptions where
  flags     : BitVec 32 := 0x60000020#32
  width     : BitVec 16 := 0#16
  precision : BitVec 16 := 0#16
  deriving DecidableEq, Repr

/-- `FormattingOptions::new()`. -/
def defaultFmtOptions : FmtOptions := {}

/-- The 24-byte `core::fmt::Formatter<'_>` at `f`, in rustc's field order:
    `buf.data @ +0`, `buf.vtable @ +8`, `options.flags @ +16`, `options.width @ +20`,
    `options.precision @ +22`. `core::fmt::write` builds it at `sp_entry - 0x68` and stores all
    24 bytes again before every `fmtFn` call. -/
def formatterAt (f outPtr vtPtr : BitVec 64) (opts : FmtOptions) : SepProp :=
  (f ↦₆₄ outPtr) ∗
  ((f + 8#64) ↦₆₄ vtPtr) ∗
  ((f + 16#64) ↦₃₂ opts.flags) ∗
  ((f + 20#64) ↦₁₆ opts.width) ∗
  ((f + 22#64) ↦₁₆ opts.precision)

/-! ## Decoding `fmt::Arguments` into calls -/

/-- One call `core::fmt::write` makes.
    - `writeStr ptr bs`: `Write::write_str(output, ptr, bs.length)` (`[vt + 0x18]`) on a literal
      piece `bs` that the template holds at `ptr`.
    - `fmtArg idx value fmtFn opts`: `fmtFn(value, &mut Formatter)` for the `rt::Argument`
      `args[idx] = {value, fmtFn}` with options `opts`. -/
inductive FmtCall where
  | writeStr (ptr : BitVec 64) (bs : List (BitVec 8))
  | fmtArg (idx : Nat) (value fmtFn : BitVec 64) (opts : FmtOptions)
  deriving DecidableEq, Repr

/-- The little-endian number in the bytes `bs`. -/
def leBytesNat (bs : List (BitVec 8)) : Nat :=
  bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- The `u16` of a `Count` entry `args[i]` (`rt::Argument::as_u16`): the low 16 bits of the word
    at `+8` (`ldrh` at `+0x120` / `+0x150`). `none` when `i` is out of range. -/
def fmtCountAt (args : List (BitVec 64 × BitVec 64)) (i : Nat) : Option (BitVec 16) :=
  (args[i]?).map fun a => a.2.setWidth 16

/-- A placeholder header byte `n ≥ 0xc0` and the bytes after it. Returns the formatting options,
    the argument index used, the next argument index and the number of bytes the optional fields
    take, following `core::fmt::write`:
    - bit 0: `flags : u32` present; bit 1: `width : u16`; bit 2: `precision : u16`;
      bit 3: `arg_index : u16`, each little-endian, in this order;
    - bit 4 (bit 5): the width (precision) field is an index `j`, and the value is the `u16` of
      `args[j]` (`fmtCountAt`);
    - absent fields take the `FormattingOptions::new()` values; without bit 3 the argument index
      is the running index `ai`; the next running index is the index used plus one.
    `0xc0` (no bits) is the default placeholder. `none` when a field runs past the template or a
    `Count` index is out of range. -/
def decodeFmtPlaceholder (n : BitVec 8) (rest : List (BitVec 8))
    (args : List (BitVec 64 × BitVec 64)) (ai : Nat) :
    Option (FmtOptions × Nat × Nat × Nat) :=
  let lf := if n.getLsbD 0 then 4 else 0
  let lw := if n.getLsbD 1 then 2 else 0
  let lp := if n.getLsbD 2 then 2 else 0
  let li := if n.getLsbD 3 then 2 else 0
  if rest.length < lf + lw + lp + li then none else
  let flags : BitVec 32 :=
    if n.getLsbD 0 then BitVec.ofNat 32 (leBytesNat (rest.take 4)) else 0x60000020#32
  let r1 := rest.drop lf
  let width0 : BitVec 16 := if n.getLsbD 1 then BitVec.ofNat 16 (leBytesNat (r1.take 2)) else 0#16
  let r2 := r1.drop lw
  let prec0 : BitVec 16 := if n.getLsbD 2 then BitVec.ofNat 16 (leBytesNat (r2.take 2)) else 0#16
  let r3 := r2.drop lp
  let idx : Nat := if n.getLsbD 3 then leBytesNat (r3.take 2) else ai
  let width? : Option (BitVec 16) :=
    if n.getLsbD 4 then fmtCountAt args width0.toNat else some width0
  let prec? : Option (BitVec 16) :=
    if n.getLsbD 5 then fmtCountAt args prec0.toNat else some prec0
  match width?, prec? with
  | some width, some prec =>
    some ({ flags := flags, width := width, precision := prec }, idx, idx + 1, lf + lw + lp + li)
  | _, _ => none

/-- Walks the encoded template `bs`, which starts at `tplPtr + pos`, with running argument index
    `ai` and `fuel` steps. Byte classes of the first byte `n` (the `+0x028 .. +0x15c` loop):
    - `0x00`: end. Accepted only when it is the last byte of the owned template.
    - `0x01 .. 0x7f`: a literal of `n` bytes follows (`writeStr`).
    - `0x80`: a `u16` little-endian length `len`, then a literal of `len` bytes (`writeStr`).
    - `0xc0 .. 0xff`: a placeholder (`decodeFmtPlaceholder`), then `fmtArg idx value fmtFn opts`
      for `args[idx] = (value, fmtFn)`.
    - `0x81 .. 0xbf`: never emitted by rustc; `none`.
    Also `none` when a literal or field runs past the template, an argument index is out of
    range, or `fuel` runs out. -/
def decodeFmtTemplate (tplPtr : BitVec 64) (args : List (BitVec 64 × BitVec 64)) :
    Nat → Nat → Nat → List (BitVec 8) → Option (List FmtCall)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | fuel + 1, pos, ai, n :: rest =>
    if n = 0#8 then
      if rest = [] then some [] else none
    else if n.toNat < 0x80 then
      let len := n.toNat
      if rest.length < len then none else
      (decodeFmtTemplate tplPtr args fuel (pos + 1 + len) ai (rest.drop len)).map
        (FmtCall.writeStr (tplPtr + BitVec.ofNat 64 (pos + 1)) (rest.take len) :: ·)
    else if n = 0x80#8 then
      if rest.length < 2 then none else
      let len := leBytesNat (rest.take 2)
      let r := rest.drop 2
      if r.length < len then none else
      (decodeFmtTemplate tplPtr args fuel (pos + 3 + len) ai (r.drop len)).map
        (FmtCall.writeStr (tplPtr + BitVec.ofNat 64 (pos + 3)) (r.take len) :: ·)
    else if n.toNat < 0xc0 then none
    else
      match decodeFmtPlaceholder n rest args ai with
      | none => none
      | some (opts, idx, ai', k) =>
        match args[idx]? with
        | none => none
        | some (value, fmtFn) =>
          (decodeFmtTemplate tplPtr args fuel (pos + 1 + k) ai' (rest.drop k)).map
            (FmtCall.fmtArg idx value fmtFn opts :: ·)

/-- The calls `core::fmt::write(output, vt, x2, x3)` makes, given the owned bytes `tpl` at `x2`
    and the owned `rt::Argument` entries `args` at `x3` (each `(value, fmtFn or Count word)`).
    - `x3` odd: `tpl` is the whole `str` (`tpl.length = x3 >>> 1`), and the one call is
      `writeStr x2 tpl` (a tail call); `args` is not read.
    - `x3` even: `tpl` must be exactly the encoded template up to and including its end byte. -/
def decodeFmtArguments (x2 x3 : BitVec 64) (tpl : List (BitVec 8))
    (args : List (BitVec 64 × BitVec 64)) : Option (List FmtCall) :=
  if x3.getLsbD 0 then
    if tpl.length = (x3 >>> 1).toNat then some [FmtCall.writeStr x2 tpl] else none
  else
    decodeFmtTemplate x2 args tpl.length 0 0 tpl

/-! ## The `fmt::Arguments` memory -/

/-- `rt::Argument` entries from `a`, 16 bytes each: `value @ +0`, `fmtFn` (or the `Count` word)
    `@ +8`; read-write (`ro = false`, e.g. the caller's stack) or read-only (`ro = true`). -/
def fmtArgEntriesAt (ro : Bool) (a : BitVec 64) : List (BitVec 64 × BitVec 64) → SepProp
  | [] => emp
  | (v, f) :: rest =>
    (if ro then (a ↦₆₄ᵣ v) ∗ ((a + 8#64) ↦₆₄ᵣ f) else (a ↦₆₄ v) ∗ ((a + 8#64) ↦₆₄ f)) ∗
      fmtArgEntriesAt ro (a + 16#64) rest

/-- The memory of `fmt::Arguments { template = x2, args = x3 }`: the template bytes `tpl` at `x2`,
    read-only (rustc places templates and `from_str` strings in read-only data; a caller holding
    them read-write can give up write access), and for even `x3` the entries `args` at `x3`. -/
def fmtArgumentsAt (argsRo : Bool) (x2 x3 : BitVec 64) (tpl : List (BitVec 8))
    (args : List (BitVec 64 × BitVec 64)) : SepProp :=
  (x2 ↦ᵣ tpl) ∗ (if x3.getLsbD 0 then emp else fmtArgEntriesAt argsRo x3 args)

/-! ## The writer protocol -/

/-- Process state that `core::fmt::write`'s own instructions leave unchanged (they make no system
    call and no `msr tpidr_el0`): the client's writer predicate must be stable under it. It
    includes every field of `PoolPreserved` (`brkStart`, `brk`, `tpidrEl0`), and `oracle` /
    `symtab`, which an allocator's out-of-memory or `mremap` behaviour may depend on. -/
def FmtWriteFrame (s s' : State) : Prop :=
  s'.trace = s.trace ∧ s'.fs = s.fs ∧ s'.sigActions = s.sigActions ∧
    s'.tpidrEl0 = s.tpidrEl0 ∧ s'.brk = s.brk ∧ s'.brkStart = s.brkStart ∧
    s'.physMemAvail = s.physMemAvail ∧ s'.oracle = s.oracle ∧ s'.oracleIdx = s.oracleIdx ∧
    s'.symtab = s.symtab ∧ (∀ a, s'.mem.perm a = s.mem.perm a)

/-- The calls `cs` run in order from writer state `st`, each step related by `Step c st ok st'`
    (`ok = false` for `Err`). `FmtRun Step cs st true st'`: all returned `Ok`, ending in `st'`.
    `FmtRun Step cs st false st'`: a prefix returned `Ok` and the next call returned `Err` in
    `st'`; the calls after it are not made. -/
inductive FmtRun {σ : Type} (Step : FmtCall → σ → Bool → σ → Prop) :
    List FmtCall → σ → Bool → σ → Prop
  | nil (st : σ) : FmtRun Step [] st true st
  | cons_ok {c : FmtCall} {cs : List FmtCall} {st st' st'' : σ} {b : Bool} :
      Step c st true st' → FmtRun Step cs st' b st'' → FmtRun Step (c :: cs) st b st''
  | cons_err {c : FmtCall} {cs : List FmtCall} {st st' : σ} :
      Step c st false st' → FmtRun Step (c :: cs) st false st'

/-- Call `c` is made in writer state `st`: the calls before it in `cs` all returned `Ok`, from
    `st₀` to `st`. -/
def FmtReaches {σ : Type} (Step : FmtCall → σ → Bool → σ → Prop) (cs : List FmtCall) (st₀ : σ)
    (c : FmtCall) (st : σ) : Prop :=
  ∃ pre post, cs = pre ++ c :: post ∧ FmtRun Step pre st₀ true st

/-- What `core::fmt::write` assumes of `write_str` (`[vt + 0x18]`) for the call
    `.writeStr ptr bs`, with writer predicate `W`, writer step `Step`, panic and out-of-memory
    relations `Panic` / `Oom`, and `stackBytes` of stack. Ghost: the writer state `st`.
    - Pre: `x0 = out`, `x1 = ptr`, `x2 = bs.length`; `ptr ↦ᵣ bs`, `W st s`, the stack.
    - Post: `w0 = 0` (`Ok`) or `1` (`Err`) exactly (the whole word: `core::fmt::write` returns it
      unchanged on the `from_str` path) and `Step (.writeStr ptr bs) st ok st'` with `W st' sf`
      and the stack.
    - Panic: `Panic c st sf`. Out of memory: `Oom c st sf`. Exit: never. -/
def fmtWriteStrCallSpec {σ : Type} (W : σ → State → SepProp) (Step : FmtCall → σ → Bool → σ → Prop)
    (Panic Oom : FmtCall → σ → State → Prop) (stackBytes : Nat) (out ptr : BitVec 64)
    (bs : List (BitVec 8)) : Spec σ where
  pre := fun st s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = ptr ∧
      (s.readReg64 .x2).toNat = bs.length⌝ ∗
      (ptr ↦ᵣ bs) ∗ W st s ∗ stackFrameAt s.sp stackBytes
  post := fun st s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧
        Step (.writeStr ptr bs) st ok st'⌝ ∗ W st' sf ∗ stackFrameAt s0.sp stackBytes
  onPanic := fun st _ sf => ⌜Panic (.writeStr ptr bs) st sf⌝ ∗ anyHeap
  onOom := fun st _ sf => ⌜Oom (.writeStr ptr bs) st sf⌝

/-- What `core::fmt::write` assumes of `fmtFn` for the call `.fmtArg idx value fmtFn opts`, with
    the output `(out, vt)`. Ghost: `(st, f)`, the writer state and the `Formatter` address.
    - Pre: `x0 = value`, `x1 = f`; `formatterAt f out vt opts`, `W st s`, the stack.
    - Post: bit 0 of `w0` is `0` (`Ok`) or `1` (`Err`) (`core::fmt::write` tests only that bit
      here) and `Step (.fmtArg idx value fmtFn opts) st ok st'` with `W st' sf`, the stack, and
      any 24 bytes at `f` (the callee may change the `Formatter`; `core::fmt::write` rebuilds it).
    - Panic: `Panic c st sf`. Out of memory: `Oom c st sf`. Exit: never.
    - The pre gives no vtable slot and no `write_str` contract. A `fmtFn` that writes through
      `f.buf` (`Formatter::write_str`, `write_char`, `write_fmt` load `[vt + 0x18]`, `[vt + 0x20]`,
      `[vt + 0x28]`) needs `W` to carry read-only copies of the slots it uses and, as pure facts,
      the contracts of the functions they point to. -/
def fmtArgCallSpec {σ : Type} (W : σ → State → SepProp) (Step : FmtCall → σ → Bool → σ → Prop)
    (Panic Oom : FmtCall → σ → State → Prop) (stackBytes : Nat) (out vt : BitVec 64) (idx : Nat)
    (value fmtFn : BitVec 64) (opts : FmtOptions) : Spec (σ × BitVec 64) where
  pre := fun (st, f) s =>
    ⌜s.readReg64 .x0 = value ∧ s.readReg64 .x1 = f⌝ ∗
      formatterAt f out vt opts ∗ W st s ∗ stackFrameAt s.sp stackBytes
  post := fun (st, f) s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 &&& 1#32 = if ok then 0#32 else 1#32) ∧
        Step (.fmtArg idx value fmtFn opts) st ok st'⌝ ∗
        memRegion f 24 ∗ W st' sf ∗ stackFrameAt s0.sp stackBytes
  onPanic := fun (st, _) _ sf => ⌜Panic (.fmtArg idx value fmtFn opts) st sf⌝ ∗ anyHeap
  onOom := fun (st, _) _ sf => ⌜Oom (.fmtArg idx value fmtFn opts) st sf⌝

/-- What `core::fmt::write` assumes of its callbacks for the decoded calls `cs`, in program `P`
    with output `(out, vt)` and `write_str` at `writeStrFn`:
    - `transport`: `W st` is stable under `FmtWriteFrame` (it may depend on the process state only
      through fields `core::fmt::write` keeps).
    - `write_str`: `fmtWriteStrCallSpec` at `writeStrFn` for every `.writeStr` call in `cs`.
    - `fmt_arg`: `fmtArgCallSpec` at `fmtFn` for every `.fmtArg` call in `cs`. -/
structure FmtCallbacks {σ : Type} (P : Program) (W : σ → State → SepProp)
    (Step : FmtCall → σ → Bool → σ → Prop) (Panic Oom : FmtCall → σ → State → Prop)
    (stackBytes : Nat) (out vt writeStrFn : BitVec 64) (cs : List FmtCall) : Prop where
  transport : ∀ (st : σ) (s s' : State), FmtWriteFrame s s' → W st s ⊢ W st s'
  write_str : ∀ ptr bs, FmtCall.writeStr ptr bs ∈ cs →
    subroutine_ok P writeStrFn (fmtWriteStrCallSpec W Step Panic Oom stackBytes out ptr bs)
  fmt_arg : ∀ idx value fmtFn opts, FmtCall.fmtArg idx value fmtFn opts ∈ cs →
    subroutine_ok P fmtFn (fmtArgCallSpec W Step Panic Oom stackBytes out vt idx value fmtFn opts)

/-! ## The contract -/

/-- `core::fmt::write(output = x0, vt = x1, template = x2, args = x3)` in program `P`, over a
    client writer protocol `(σ, W, Step, Panic, Oom)` whose callbacks use at most `stackBytes` of
    stack. Ghost: `(out, vt, writeStrFn, argsRo, tpl, args, st₀)`.
    - Pre: the registers; `decodeFmtArguments x2 x3 tpl args = some cs` with `FmtCallbacks` for
      `cs`; `(vt + 0x18) ↦₆₄ᵣ writeStrFn`; `fmtArgumentsAt argsRo x2 x3 tpl args`; `W st₀ s`;
      `0x70 + stackBytes` bytes of stack (`0x70 + stackBytes ≤ 2 ^ 64`).
    - Post: for some `ok`, `st'`: `w0 = 0` if `ok`, else `w0 = 1` (exactly),
      `FmtRun Step cs st₀ ok st'`, `W st' sf`, the rest given back.
    - Panic / out of memory: some call `c` of `cs` was reached in writer state `st`
      (`FmtReaches`) and `Panic c st sf` / `Oom c st sf`. Exit: never. -/
def coreFmtWriteSpec {σ : Type} (P : Program) (W : σ → State → SepProp)
    (Step : FmtCall → σ → Bool → σ → Prop) (Panic Oom : FmtCall → σ → State → Prop)
    (stackBytes : Nat) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × Bool × List (BitVec 8) ×
      List (BitVec 64 × BitVec 64) × σ) where
  pre := fun (out, vt, writeStrFn, argsRo, tpl, args, st₀) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = vt ∧ 0x70 + stackBytes ≤ 2 ^ 64 ∧
      ∃ cs, decodeFmtArguments (s.readReg64 .x2) (s.readReg64 .x3) tpl args = some cs ∧
        FmtCallbacks P W Step Panic Oom stackBytes out vt writeStrFn cs⌝ ∗
      ((vt + 0x18#64) ↦₆₄ᵣ writeStrFn) ∗
      fmtArgumentsAt argsRo (s.readReg64 .x2) (s.readReg64 .x3) tpl args ∗
      W st₀ s ∗ stackFrameAt s.sp (0x70 + stackBytes)
  post := fun (_, vt, writeStrFn, argsRo, tpl, args, st₀) s0 sf =>
    ∃∗ ok : Bool, ∃∗ st' : σ,
      ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧
        ∃ cs, decodeFmtArguments (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args = some cs ∧
          FmtRun Step cs st₀ ok st'⌝ ∗
      ((vt + 0x18#64) ↦₆₄ᵣ writeStrFn) ∗
      fmtArgumentsAt argsRo (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args ∗
      W st' sf ∗ stackFrameAt s0.sp (0x70 + stackBytes)
  onPanic := fun (_, _, _, _, tpl, args, st₀) s0 sf =>
    ⌜∃ cs c st, decodeFmtArguments (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args = some cs ∧
      FmtReaches Step cs st₀ c st ∧ Panic c st sf⌝ ∗ anyHeap
  onOom := fun (_, _, _, _, tpl, args, st₀) s0 sf =>
    ⌜∃ cs c st, decodeFmtArguments (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args = some cs ∧
      FmtReaches Step cs st₀ c st ∧ Oom c st sf⌝

end VerifiedLibraries.RustStd
