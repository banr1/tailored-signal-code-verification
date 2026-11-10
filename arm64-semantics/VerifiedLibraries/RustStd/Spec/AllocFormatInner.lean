/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.RustStd.Spec.Alloc
public import VerifiedLibraries.RustStd.Spec.IoCommon
public import VerifiedLibraries.RustStd.Spec.CoreFmtWrite

/-!
# `alloc::fmt::format::format_inner` Specification

Specification of `"alloc::fmt::format::format_inner"` (block 3 of `allocMultiLib`, 432 bytes,
`0x60`-byte frame) and the `<String as fmt::Write>` vtable `"rust_alloc:.data.rel.ro..Lanon.34"`
(48 bytes; `+0x18` `write_str` in block 7, `+0x20` `write_char` in block 6, `+0x28` `write_fmt`
in block 8) from `alloc/src/fmt.rs`, `core/src/fmt/mod.rs` (`Arguments::estimated_capacity`), and
`alloc/src/raw_vec/mod.rs` (`grow_amortized`).

With `x0 = fmt.template`, `x1 = fmt.args`, and `x8` pointing to the 24-byte `String` result slot,
`format_inner`:
1. computes the initial capacity `fmtEstimatedCapacity` from the template without reading the
   argument array;
2. allocates via `String::with_capacity` (capacity `0` yields the dangling pointer `1`; capacity
   `>= 2 ^ 63` or a null return from `__rust_alloc(cap, 1)` panics);
3. invokes `core::fmt::write(&mut output, &vtable, template, args)`, panicking via `unwrap_failed`
   if `w0 != 0`;
4. copies the 24-byte `String` header to `x8`.

`<String as Write>::write_str` and `write_char` always return `Ok`, growing via `grow_amortized`
to capacity `max (max (2 * cap) (len + n)) 8` when needed (panicking on `len + n` overflow,
capacity `>= 2 ^ 63`, or null allocator return). Under `panic = abort`, a panic or OOM does not
run destructors and leaks any allocated buffer, so `onPanic` and `onOom` do not return the pool.

Client `fmtFn` callbacks are parameterized by `(R, ArgStep, ArgPanic)` and proved against
`fmtArgCallSpec` over `fmtInnerW` (`FmtInnerArgsOk`). Because callback-driven growth counts and
sizes are dynamic, this contract specifies unbudgeted allocators (`∀ lb lk n al, A.CanAlloc lb lk n al`);
stack usage is `formatInnerFrame` (`0x60`) plus `core::fmt::write` (`0x70`) plus `stackBytes`
(with `stringWriterStack <= stackBytes`).
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-! ## Harness Names and Addresses -/

/-- Demangled symbol name of `alloc::fmt::format::format_inner` in `allocMultiLib` (block 3). -/
abbrev allocFormatInnerSym : String :=
  "alloc::fmt::format::format_inner"

/-- Harness name of the `<String as fmt::Write>` vtable in `allocMultiLib`. -/
abbrev stringWriteVtableSym : String :=
  "rust_alloc:.data.rel.ro..Lanon.34"

/-- Where the `<String as fmt::Write>` vtable and the three methods its slots `+0x18`, `+0x20`,
    `+0x28` point to are placed (for a placement of `allocMultiLib`: the vtable symbol and
    blocks 7, 6 and 8). -/
structure StringWriteAddrs where
  vtable : BitVec 64
  writeStr : BitVec 64
  writeChar : BitVec 64
  writeFmt : BitVec 64

/-- The vtable's three method slots, read-only (they duplicate, so `core::fmt::write` and the
    `fmtFn`s each get a copy). The loader maps `.data.rel.ro` writable; read-only access is given
    up by the caller. -/
def stringWriteVtableAt (va : StringWriteAddrs) : SepProp :=
  ((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ ((va.vtable + 0x20#64) ↦₆₄ᵣ va.writeChar) ∗
    ((va.vtable + 0x28#64) ↦₆₄ᵣ va.writeFmt)

/-- `format_inner`'s own frame. -/
abbrev formatInnerFrame : Nat := 0x60

/-- Stack below `core::fmt::write`'s frame used by the `String` writer's own calls (`write_str` /
    `write_char` -> `do_reserve_and_handle` -> `finish_grow` -> allocator): `0x160 + 4096` from
    `format_inner`'s entry minus `format_inner`'s `0x60` and `core::fmt::write`'s `0x70`. -/
abbrev stringWriterStack : Nat := 0x90 + 4096

/-! ## The `String` Writer -/

/-- The local `String` while `core::fmt::write` runs: its bytes, capacity and buffer, and the
    allocator indices `(lb, lk)`. -/
structure FmtStr where
  bytes : List (BitVec 8)
  cap : BitVec 64
  ptr : BitVec 64
  lb : Nat
  lk : Nat

/-- `grow_amortized`'s new capacity when `n` bytes are appended to a `String` of length `len` and
    capacity `cap`. -/
def stringGrowCap (cap len n : Nat) : Nat :=
  max (max (2 * cap) (len + n)) 8

/-- What holds when appending `n` bytes to `st` panics: they do not fit, and either `len + n`
    overflows `usize` or the grown capacity is one the allocator may refuse (`NullAllowed _ 1`;
    this covers capacities `≥ 2 ^ 63`, which `finish_grow` rejects before calling it). -/
def StringAppendPanics (st : FmtStr) (n : Nat) : Prop :=
  st.cap.toNat < st.bytes.length + n ∧
    (2 ^ 64 ≤ st.bytes.length + n ∨ NullAllowed (stringGrowCap st.cap.toNat st.bytes.length n) 1)

variable {oom : State → State → Prop}

/-- Appending `bs` to `st` gives `st'` (no panic): if the bytes fit, the buffer and indices stay;
    otherwise the capacity becomes `stringGrowCap` with some new buffer, and the indices move as
    for `alloc` (no buffer before) or `realloc`. -/
def StringAppend (A : RustStdAlloc oom) (st : FmtStr) (bs : List (BitVec 8)) (st' : FmtStr) :
    Prop :=
  st'.bytes = st.bytes ++ bs ∧
    if st.bytes.length + bs.length ≤ st.cap.toNat then
      st'.cap = st.cap ∧ st'.ptr = st.ptr ∧ st'.lb = st.lb ∧ st'.lk = st.lk
    else
      st'.cap = BitVec.ofNat 64 (stringGrowCap st.cap.toNat st.bytes.length bs.length) ∧
        (if st.cap = 0#64 then
          st'.lb = st.lb + A.cost (stringGrowCap st.cap.toNat st.bytes.length bs.length) 1 ∧
            st'.lk = st.lk + 1
         else
          st'.lb = st.lb + A.cost (stringGrowCap st.cap.toNat st.bytes.length bs.length) 1 -
              A.cost st.cap.toNat 1 ∧
            st'.lk = st.lk)

/-- The `String` writer at `out` in state `st`, for a `format_inner` call entered in state `t0`:
    - the process fields every allocator call keeps (`IoCallFrame t0 s`) and the file system and
      trace of `t0` (formatting does no I/O);
    - the `String` header at `out`, its buffer and the pool;
    - musl's `errno` cell (allocator calls write it), the vtable slots and the client's `R`.
    It reads the state only through fields `FmtWriteFrame` keeps. -/
def fmtInnerW (A : RustStdAlloc oom) (va : StringWriteAddrs) (R : SepProp) (t0 : State)
    (out : BitVec 64) (st : FmtStr) (s : State) : SepProp :=
  ⌜IoCallFrame t0 s ∧ s.fs = t0.fs ∧ s.trace = t0.trace⌝ ∗
    vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
    ioVecBuf A st.cap st.ptr st.bytes ∗ A.pool st.lb st.lk s ∗ StdErrnoCell t0.tpidrEl0 ∗
    stringWriteVtableAt va ∗ R

/-- One call `core::fmt::write` makes on the `String` writer: a literal appends its bytes
    (`write_str`, always `Ok`); a `fmtFn` call transitions the `FmtStr` state (`bytes`, `cap`,
    `ptr`, `lb`, `lk`) as the client's `ArgStep` specifies. -/
def fmtInnerStep (A : RustStdAlloc oom)
    (ArgStep : FmtCall → FmtStr → Bool → FmtStr → Prop) :
    FmtCall → FmtStr → Bool → FmtStr → Prop
  | .writeStr _ bs, st, ok, st' => ok = true ∧ StringAppend A st bs st'
  | .fmtArg idx value fmtFn opts, st, ok, st' =>
    ArgStep (.fmtArg idx value fmtFn opts) st ok st'

/-- When a call may panic: a literal only by `StringAppendPanics`; a `fmtFn` call by the client's
    `ArgPanic`. -/
def fmtInnerCallPanics (ArgPanic : FmtCall → FmtStr → Prop) : FmtCall → FmtStr → Prop
  | .writeStr _ bs, st => StringAppendPanics st bs.length
  | .fmtArg idx value fmtFn opts, st => ArgPanic (.fmtArg idx value fmtFn opts) st

/-- The `Panic` relation of the `String` writer, for a call entered in `t0`: file system and trace
    unchanged, and the call may panic (`fmtInnerCallPanics`). -/
def fmtInnerPanic (ArgPanic : FmtCall → FmtStr → Prop) (t0 : State) (c : FmtCall) (st : FmtStr)
    (sf : State) : Prop :=
  sf.fs = t0.fs ∧ sf.trace = t0.trace ∧ fmtInnerCallPanics ArgPanic c st

/-- The `Oom` relation of the `String` writer, for a call entered in `t0`: some allocator call,
    made in a state `sm` with the trace, signal dispositions and file system of `t0`, ran out of
    memory (`oom sm sf`). -/
def fmtInnerOom (oom : State → State → Prop) (t0 : State) (_ : FmtCall) (_ : FmtStr) (sf : State) :
    Prop :=
  ∃ sm, IoFrame t0 sm ∧ sm.fs = t0.fs ∧ oom sm sf

/-! ## Initial Capacity -/

/-- Total length of the literal pieces. -/
def fmtLiteralLen : List FmtCall → Nat
  | [] => 0
  | .writeStr _ bs :: cs => bs.length + fmtLiteralLen cs
  | .fmtArg .. :: cs => fmtLiteralLen cs

/-- A placeholder comes before any non-empty literal (`starts_with_placeholder`). -/
def fmtStartsWithPlaceholder : List FmtCall → Bool
  | [] => false
  | .writeStr _ bs :: cs => bs.isEmpty && fmtStartsWithPlaceholder cs
  | .fmtArg .. :: _ => true

/-- `Arguments::estimated_capacity` for the decoded calls `cs` of `(template, x1)`: the string's
    length for `from_str` (`x1` odd); else `0` when the template starts with a placeholder and its
    literals total less than 16 bytes; else twice the literal length, wrapping. -/
def fmtEstimatedCapacity (x1 : BitVec 64) (cs : List FmtCall) : Nat :=
  if x1.getLsbD 0 then fmtLiteralLen cs
  else if fmtStartsWithPlaceholder cs && decide (fmtLiteralLen cs < 16) then 0
  else (2 * fmtLiteralLen cs) % 2 ^ 64

/-- The `String` after `String::with_capacity(cap0)` from pool indices `(lb, lk)`: empty; with no
    block and buffer `1` for `cap0 = 0`, else with a fresh block and indices
    `(lb + cost cap0 1, lk + 1)`. -/
def FmtInnerStart (A : RustStdAlloc oom) (cap0 lb lk : Nat) (st : FmtStr) : Prop :=
  st.bytes = [] ∧ st.cap = BitVec.ofNat 64 cap0 ∧
    if cap0 = 0 then st.ptr = 1#64 ∧ st.lb = lb ∧ st.lk = lk
    else st.lb = lb + A.cost cap0 1 ∧ st.lk = lk + 1

/-! ## Contract -/

/-- The client's obligation for the decoded calls `cs` of a `format_inner` call entered in `t0`:
    every `fmtFn` of a `fmtArg` call meets `fmtArgCallSpec` over the `String` writer at any header
    address `out`, with `stackBytes` of stack. -/
def FmtInnerArgsOk (P : Program) (A : RustStdAlloc oom) (va : StringWriteAddrs) (R : SepProp)
    (ArgStep : FmtCall → FmtStr → Bool → FmtStr → Prop)
    (ArgPanic : FmtCall → FmtStr → Prop) (stackBytes : Nat) (t0 : State) (cs : List FmtCall) :
    Prop :=
  ∀ idx value fmtFn opts, FmtCall.fmtArg idx value fmtFn opts ∈ cs → ∀ out : BitVec 64,
    subroutine_ok P fmtFn
      (fmtArgCallSpec (fmtInnerW A va R t0 out) (fmtInnerStep A ArgStep)
        (fmtInnerPanic ArgPanic t0) (fmtInnerOom oom t0) stackBytes out va.vtable idx value fmtFn
        opts)

/-- `alloc::fmt::format::format_inner(template = x0, args = x1)` with result slot `x8`, in program
    `P`, allocator `A`, vtable placement `va`, client protocol `(R, ArgStep, ArgPanic)` and
    `stackBytes` of callback stack. Ghost: `(ret, argsRo, tpl, args, lb, lk)`.
    - Pre: `x8 = ret`; every request fits; `x0`, `x1` decode with the owned `tpl`, `args` to
      calls `cs`, and the client's `fmtFn`s meet `FmtInnerArgsOk`; the `fmt::Arguments` memory, a
      24-byte result slot, the pool, `errno`, the vtable slots, `R` and the stack.
    - Post: the result is a `String` `st` at `ret` reached by running `cs` from the initial `String`
      (`FmtInnerStart` at `fmtEstimatedCapacity`) with every call `Ok`; the pool at its indices;
      the process fields, file system and trace unchanged; everything else given back.
    - Panic: file system and trace unchanged, and one of: the initial capacity is one the allocator
      may refuse (`NullAllowed _ 1`, which covers `≥ 2 ^ 63`); a call reached from the initial
      `String` may panic (`fmtInnerCallPanics`); or the calls end in `Err` (`unwrap_failed`).
    - Out of memory: some allocator call, made with the trace, signal dispositions and file system
      of the entry state, ran out of memory. -/
def allocFormatInnerSpec (P : Program) (A : RustStdAlloc oom) (va : StringWriteAddrs) (R : SepProp)
    (ArgStep : FmtCall → FmtStr → Bool → FmtStr → Prop)
    (ArgPanic : FmtCall → FmtStr → Prop) (stackBytes : Nat) :
    Spec (BitVec 64 × Bool × List (BitVec 8) × List (BitVec 64 × BitVec 64) × Nat × Nat) where
  pre := fun (ret, argsRo, tpl, args, lb, lk) s =>
    ⌜s.readReg64 .x8 = ret ∧ stringWriterStack ≤ stackBytes ∧
      formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64 ∧ (∀ lb' lk' n al, A.CanAlloc lb' lk' n al) ∧
      ∃ cs, decodeFmtArguments (s.readReg64 .x0) (s.readReg64 .x1) tpl args = some cs ∧
        FmtInnerArgsOk P A va R ArgStep ArgPanic stackBytes s cs⌝ ∗
      fmtArgumentsAt argsRo (s.readReg64 .x0) (s.readReg64 .x1) tpl args ∗ memRegion ret 24 ∗
      A.pool lb lk s ∗ StdErrnoCell s.tpidrEl0 ∗ stringWriteVtableAt va ∗ R ∗
      stackFrameAt s.sp (formatInnerFrame + 0x70 + stackBytes)
  post := fun (ret, argsRo, tpl, args, lb, lk) s0 sf =>
    ∃∗ st : FmtStr,
      ⌜IoCallFrame s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
        ∃ cs st₀, decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs ∧
          FmtInnerStart A (fmtEstimatedCapacity (s0.readReg64 .x1) cs) lb lk st₀ ∧
          FmtRun (fmtInnerStep A ArgStep) cs st₀ true st⌝ ∗
      vecHeader ret st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
      ioVecBuf A st.cap st.ptr st.bytes ∗ A.pool st.lb st.lk sf ∗
      fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
      StdErrnoCell s0.tpidrEl0 ∗ stringWriteVtableAt va ∗ R ∗
      stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)
  onPanic := fun (_, _, tpl, args, lb, lk) s0 sf =>
    ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      ∃ cs, decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs ∧
        (NullAllowed (fmtEstimatedCapacity (s0.readReg64 .x1) cs) 1 ∨
         (∃ st₀ c st, FmtInnerStart A (fmtEstimatedCapacity (s0.readReg64 .x1) cs) lb lk st₀ ∧
            FmtReaches (fmtInnerStep A ArgStep) cs st₀ c st ∧ fmtInnerCallPanics ArgPanic c st) ∨
         (∃ st₀ st, FmtInnerStart A (fmtEstimatedCapacity (s0.readReg64 .x1) cs) lb lk st₀ ∧
            FmtRun (fmtInnerStep A ArgStep) cs st₀ false st))⌝
  onOom := fun _ s0 sf => ⌜∃ sm, IoFrame s0 sm ∧ sm.fs = s0.fs ∧ oom sm sf⌝

end VerifiedLibraries.RustStd
