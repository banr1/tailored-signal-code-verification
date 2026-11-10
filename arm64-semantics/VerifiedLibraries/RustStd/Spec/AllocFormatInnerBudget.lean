/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.Mallocng.Spec.Cost
public import VerifiedLibraries.RustStd.Spec.AllocFormatInner
public import VerifiedLibraries.RustStd.Spec.CoreFmtDisplay

/-!
# Budget-Threaded `alloc::fmt::format::format_inner` Specification

Defines the heap-budgeted counterpart of [`AllocFormatInner`](AllocFormatInner.lean) over a
stateful allocator cost model (`RustAllocBudget`, reusing `VerifiedLibraries.Mallocng.AllocEvent`).
`A.pool st s` encapsulates all allocator-private state (including musl's TLS `errno` cell
`tpidr_el0 - 164`), and when the caller's event envelope `E` satisfies `FitsEnv A st0 E` and
`FormatInnerBudgetSafe`, both `.OutOfMemory` and `handle_error` / `unwrap_failed` panics are
statically unreachable (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`).
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64
open VerifiedLibraries.Mallocng (AllocEvent)

/-! ## Virtual-memory preservation and Rust allocator events -/

/-- Process and virtual-memory fields that a budgeted allocator pool may read:
    `PoolPreserved s s'` (`brkStart`, `brk`, `tpidrEl0`), `physMemAvail`, and page permissions
    `mem.perm`. Satisfied by `FmtWriteFrame`. -/
def VmPreserved (s s' : State) : Prop :=
  PoolPreserved s s' ∧ s'.physMemAvail = s.physMemAvail ∧
    ∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a

/-- `AllocEvent` list emitted by `__rust_alloc(size, align)`: `malloc(size)` when
    `align ≤ 16 ∧ align ≤ size`, else `posix_memalign(&slot, max align 8, size)`. -/
def rustAllocEvents (size align : Nat) : List AllocEvent :=
  if align ≤ 16 ∧ align ≤ size then [.alloc size]
  else [.aligned (max align 8) size]

/-- `AllocEvent` list emitted by `__rust_realloc(ptr, oldSize, align, newSize)`:
    `realloc(ptr, newSize)` when `align ≤ 16 ∧ align ≤ newSize`, else
    `posix_memalign(&slot, max align 8, newSize)`, `memcpy`, and `free(ptr)`. -/
def rustReallocEvents (oldSize newSize align : Nat) : List AllocEvent :=
  if align ≤ 16 ∧ align ≤ newSize then [.realloc align oldSize newSize]
  else [.aligned (max align 8) newSize, .free align oldSize]

/-! ## Budget-threaded Rust global allocator interface -/

/-- Stateful budget-threaded Rust global allocator:
    - `σ`: abstract cost-model state, advanced by `step` on each `AllocEvent`;
    - `FitsEvent st ev`: `ev` is within budget from state `st` (ruling out `.OutOfMemory`);
    - `pool st s`: allocator-private state at `s` (encapsulating any allocator-owned TLS/globals);
    - `live p n al`: live allocation of `n` bytes at `p` with alignment `al`. -/
structure RustAllocBudget : Type 1 where
  σ : Type
  step : AllocEvent → σ → σ
  FitsEvent : σ → AllocEvent → Prop
  pool : σ → State → SepProp
  live : BitVec 64 → Nat → Nat → SepProp
  block_valid : ∀ p n al, live p n al ⊢
    ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ live p n al
  pool_transport : ∀ st s s', VmPreserved s s' → pool st s' = pool st s
  fits_not_nullAllowed : ∀ st size align, align ≤ 2 ^ 31 →
    (FitsEvent st (.alloc size) ∨ FitsEvent st (.aligned (max align 8) size) ∨
      ∃ old, FitsEvent st (.realloc align old size)) →
    ¬ NullAllowed size align

/-- Advance `st` along `evs` from left to right. -/
def RustAllocBudget.stepEvents (A : RustAllocBudget) : List AllocEvent → A.σ → A.σ
  | [], st => st
  | ev :: evs, st => A.stepEvents evs (A.step ev st)

/-- Every event in `evs` satisfies `A.FitsEvent` at the state left by the preceding events. -/
def RustAllocBudget.FitsEvents (A : RustAllocBudget) : A.σ → List AllocEvent → Prop
  | _, [] => True
  | st, ev :: evs => A.FitsEvent st ev ∧ A.FitsEvents (A.step ev st) evs

/-- Envelope budget sufficiency: every event sequence in `E` fits starting from `st0`. -/
def FitsEnv (A : RustAllocBudget) (st0 : A.σ) (E : List AllocEvent → Prop) : Prop :=
  ∀ evs, E evs → A.FitsEvents st0 evs

/-- Conditional-OOM `__rust_alloc(size = x0, align = x1)` contract over `A : RustAllocBudget`
    (no external `StdErrnoCell` frame). Ghost: `(size, align, st)`. -/
def rustBudgetAllocSpec (A : RustAllocBudget) : Spec (Nat × Nat × A.σ) where
  pre := fun (size, align, st) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      RustLayoutOk size align⌝ ∗
      A.pool st s ∗ Rust.hookFrame s.sp
  post := fun (size, align, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else A.stepEvents (rustAllocEvents size align) st
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool st' sf ∗ Rust.hookFrame s0.sp ∗
      (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
         A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)
  onOom := fun (size, align, st) s0 sf =>
    ⌜¬ A.FitsEvents st (rustAllocEvents size align) ∧ OomPreserved s0 sf⌝

/-- Conditional-OOM `__rust_realloc(ptr = x0, old = x1, align = x2, new = x3)` contract over
    `A : RustAllocBudget` (no external `StdErrnoCell` frame). Ghost:
    `(ptr, old, align, new, bs, st)`. -/
def rustBudgetReallocSpec (A : RustAllocBudget) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × A.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
      bs.length ≤ new⌝ ∗
      A.pool st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ Rust.hookFrame s.sp
  post := fun (p, old, align, new, bs, st) s0 sf =>
    let st' :=
      if sf.readReg64 .x0 = 0 then st else A.stepEvents (rustReallocEvents old new align) st
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool st' sf ∗ Rust.hookFrame s0.sp ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜NullAllowed new align⌝ ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
          A.live (sf.readReg64 .x0) new align ∗ (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))
  onOom := fun (_, old, align, new, _, st) s0 sf =>
    ⌜¬ A.FitsEvents st (rustReallocEvents old new align) ∧ OomPreserved s0 sf⌝

/-! ## Budget-tracked `String` buffer state and `format_inner` writer -/

/-- Local `String` state during `format_inner`, carrying the cumulative `AllocEvent` log `evs`
    emitted since entry. -/
structure FmtBuf where
  bytes : List (BitVec 8)
  cap : BitVec 64
  ptr : BitVec 64
  evs : List AllocEvent

/-- Resulting capacity after appending `n` bytes to `st`. -/
def stringNextCap (st : FmtBuf) (n : Nat) : Nat :=
  if st.bytes.length + n ≤ st.cap.toNat then st.cap.toNat
  else stringGrowCap st.cap.toNat st.bytes.length n

/-- Resulting cumulative `AllocEvent` log after appending `n` bytes to `st` (`cap = 0` emits
    `rustAllocEvents newCap 1`; `cap ≠ 0` emits `rustReallocEvents cap newCap 1`). -/
def stringAppendEvents (st : FmtBuf) (n : Nat) : List AllocEvent :=
  if st.bytes.length + n ≤ st.cap.toNat then st.evs
  else
    let newCap := stringGrowCap st.cap.toNat st.bytes.length n
    st.evs ++
      (if st.cap = 0#64 then rustAllocEvents newCap 1
       else rustReallocEvents st.cap.toNat newCap 1)

/-- Appending `bs` to `st` yields `st'`: bytes concatenate, capacity and event log follow
    `stringNextCap` / `stringAppendEvents`, and `ptr` is unchanged when no growth occurs. -/
def StringBufAppend (st : FmtBuf) (bs : List (BitVec 8)) (st' : FmtBuf) : Prop :=
  st'.bytes = st.bytes ++ bs ∧
    st'.cap = BitVec.ofNat 64 (stringNextCap st bs.length) ∧
    st'.evs = stringAppendEvents st bs.length ∧
    (st.bytes.length + bs.length ≤ st.cap.toNat → st'.ptr = st.ptr)

/-- Initial `FmtBuf` after `String::with_capacity(cap0)`: empty `bytes`, dangling `ptr = 1` with
    `evs = []` when `cap0 = 0`, and `evs = rustAllocEvents cap0 1` when `0 < cap0`. -/
def FmtBufStart (cap0 : Nat) (st : FmtBuf) : Prop :=
  st.bytes = [] ∧ st.cap = BitVec.ofNat 64 cap0 ∧
    if cap0 = 0 then st.ptr = 1#64 ∧ st.evs = []
    else st.evs = rustAllocEvents cap0 1

/-- Heap buffer of a `Vec<u8>` / `String` over `A : RustAllocBudget`. -/
def fmtBufVecAt (A : RustAllocBudget) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    (if cap = 0#64 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

/-- Budget-threaded `String` writer predicate at `out` for `format_inner` entered at `(t0, st0)`.
    Owns `A.pool (A.stepEvents st.evs st0) s` directly with no external `StdErrnoCell` conjunct. -/
def fmtInnerBudgetW (A : RustAllocBudget) (st0 : A.σ) (va : StringWriteAddrs) (R : SepProp)
    (t0 : State) (out : BitVec 64) (st : FmtBuf) (s : State) : SepProp :=
  ⌜IoCallFrame t0 s ∧ s.fs = t0.fs ∧ s.trace = t0.trace⌝ ∗
    vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
    fmtBufVecAt A st.cap st.ptr st.bytes ∗
    A.pool (A.stepEvents st.evs st0) s ∗
    stringWriteVtableAt va ∗ R

/-- What holds when appending `n` bytes to `st` panics: they do not fit, and either `len + n`
    overflows `usize` or the grown capacity is one the allocator may refuse (`NullAllowed _ 1`;
    this covers capacities `≥ 2 ^ 63`, which `finish_grow` rejects before calling it). -/
def StringBufAppendPanics (st : FmtBuf) (n : Nat) : Prop :=
  st.cap.toNat < st.bytes.length + n ∧
    (2 ^ 64 ≤ st.bytes.length + n ∨ NullAllowed (stringGrowCap st.cap.toNat st.bytes.length n) 1)

/-- Writer step relation for `core::fmt::write` on `FmtBuf`: literals append via `StringBufAppend`;
    argument callbacks step via `ArgStep`. -/
def fmtInnerBudgetStep (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop) :
    FmtCall → FmtBuf → Bool → FmtBuf → Prop
  | .writeStr _ bs, st, ok, st' => ok = true ∧ StringBufAppend st bs st'
  | .fmtArg idx value fmtFn opts, st, ok, st' =>
    ArgStep (.fmtArg idx value fmtFn opts) st ok st'

/-- Per-call panic relation on `FmtBuf` for a `format_inner` call entered at `t0`: a literal
    `write_str` panics only on `StringBufAppendPanics` with `fs` and `trace` unchanged; an argument
    callback panics only when `ArgPanic` holds. -/
def fmtInnerBudgetPanic (t0 : State)
    (ArgPanic : FmtCall → FmtBuf → State → Prop) : FmtCall → FmtBuf → State → Prop
  | .writeStr _ bs, st, sf =>
    sf.fs = t0.fs ∧ sf.trace = t0.trace ∧ StringBufAppendPanics st bs.length
  | .fmtArg idx value fmtFn opts, st, sf =>
    ArgPanic (.fmtArg idx value fmtFn opts) st sf

/-- Per-call out-of-memory relation on `FmtBuf`: a literal `write_str` can hit `.OutOfMemory` only
    when `stringAppendEvents st bs.length` does not fit from `st0`; an argument callback can hit
    `.OutOfMemory` only when `ArgOom` holds. -/
def fmtInnerBudgetOom (A : RustAllocBudget) (st0 : A.σ)
    (ArgOom : FmtCall → FmtBuf → State → Prop) : FmtCall → FmtBuf → State → Prop
  | .writeStr _ bs, st, _ =>
    ¬ A.FitsEvents st0 (stringAppendEvents st bs.length)
  | .fmtArg idx value fmtFn opts, st, sf =>
    ArgOom (.fmtArg idx value fmtFn opts) st sf

/-! ## The budgeted `format_inner` contract -/

/-- Client callback obligation for the decoded calls `cs` of a budgeted `format_inner` call entered
    at `(t0, st0)`: every `fmtFn` in `cs` meets `fmtArgCallSpec` with
    `Panic = fmtInnerBudgetPanic t0 ArgPanic` and `Oom = fmtInnerBudgetOom A st0 ArgOom` over
    `fmtInnerBudgetW A st0 va R t0 out`. -/
def FmtInnerBudgetArgsOk (P : Program) (A : RustAllocBudget) (st0 : A.σ) (va : StringWriteAddrs)
    (R : SepProp) (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop) (stackBytes : Nat) (t0 : State)
    (cs : List FmtCall) : Prop :=
  ∀ idx value fmtFn opts, FmtCall.fmtArg idx value fmtFn opts ∈ cs → ∀ out : BitVec 64,
    subroutine_ok P fmtFn
      (fmtArgCallSpec (fmtInnerBudgetW A st0 va R t0 out) (fmtInnerBudgetStep ArgStep)
        (fmtInnerBudgetPanic t0 ArgPanic) (fmtInnerBudgetOom A st0 ArgOom) stackBytes out
        va.vtable idx value fmtFn opts)

/-- Safety and envelope coverage conditions ruling out panics and `.OutOfMemory` along `cs`:
    1. `fmtLiteralLen cs < 2 ^ 60` (`2 * fmtLiteralLen cs` neither wraps 64 bits nor reaches
       `2 ^ 63`, and every literal `write_str` slice is shorter than `2 ^ 60`);
    2. the initial `String::with_capacity` event trace is a prefix of some trace in `E`;
    3. every complete `Ok` run ends with `E st.evs`;
    4. no run ends in `Err` (`unwrap_failed` is unreachable);
    5. under `FitsEnv A st0 E`, no reachable argument callback satisfies `ArgPanic` and no
       reachable literal or argument step satisfies `fmtInnerBudgetOom` (literal `write_str` panics
       are ruled out automatically via `A.fits_not_nullAllowed`). -/
def FormatInnerBudgetSafe (A : RustAllocBudget) (st0 : A.σ)
    (E : List AllocEvent → Prop)
    (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop)
    (x1 : BitVec 64) (cs : List FmtCall) : Prop :=
  fmtLiteralLen cs < 2 ^ 60 ∧
    (∀ st₀, FmtBufStart (fmtEstimatedCapacity x1 cs) st₀ → ∃ suf, E (st₀.evs ++ suf)) ∧
    (∀ st₀ st, FmtBufStart (fmtEstimatedCapacity x1 cs) st₀ →
      FmtRun (fmtInnerBudgetStep ArgStep) cs st₀ true st → E st.evs) ∧
    (¬ ∃ st₀ st, FmtBufStart (fmtEstimatedCapacity x1 cs) st₀ ∧
      FmtRun (fmtInnerBudgetStep ArgStep) cs st₀ false st) ∧
    (FitsEnv A st0 E →
      ∀ st₀ c st sf, FmtBufStart (fmtEstimatedCapacity x1 cs) st₀ →
        FmtReaches (fmtInnerBudgetStep ArgStep) cs st₀ c st →
        (∀ idx value fmtFn opts, c = .fmtArg idx value fmtFn opts → ¬ ArgPanic c st sf) ∧
          ¬ fmtInnerBudgetOom A st0 ArgOom c st sf)

/-- Budget-threaded `alloc::fmt::format::format_inner(template = x0, args = x1)` with result slot
    `x8`, over `A : RustAllocBudget`, event envelope `E`, vtable placement `va`, client protocol
    `(R, ArgStep, ArgPanic, ArgOom)`, and `stackBytes` of callback stack.
    Ghost: `(ret, argsRo, tpl, args, st0)`.
    - Pre: `FitsEnv A st0 E`, `FormatInnerBudgetSafe`, and `FmtInnerBudgetArgsOk`; owns `A.pool st0 s`
      with no external `StdErrnoCell` frame.
    - Post: `String` result `st` at `ret` with `E st.evs`, `A.pool (A.stepEvents st.evs st0) sf`,
      and process fields, file system, and trace preserved.
    - Panic, exit, and out of memory: `⌜False⌝`. -/
def allocFormatInnerBudgetSpec (P : Program) (A : RustAllocBudget)
    (E : List AllocEvent → Prop) (va : StringWriteAddrs) (R : SepProp)
    (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop) (stackBytes : Nat) :
    Spec (BitVec 64 × Bool × List (BitVec 8) × List (BitVec 64 × BitVec 64) × A.σ) where
  pre := fun (ret, argsRo, tpl, args, st0) s =>
    ⌜s.readReg64 .x8 = ret ∧ stringWriterStack ≤ stackBytes ∧
      formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64 ∧ FitsEnv A st0 E ∧
      ∃ cs, decodeFmtArguments (s.readReg64 .x0) (s.readReg64 .x1) tpl args = some cs ∧
        FormatInnerBudgetSafe A st0 E ArgStep ArgPanic ArgOom (s.readReg64 .x1) cs ∧
        FmtInnerBudgetArgsOk P A st0 va R ArgStep ArgPanic ArgOom stackBytes s cs⌝ ∗
      fmtArgumentsAt argsRo (s.readReg64 .x0) (s.readReg64 .x1) tpl args ∗ memRegion ret 24 ∗
      A.pool st0 s ∗ stringWriteVtableAt va ∗ R ∗
      stackFrameAt s.sp (formatInnerFrame + 0x70 + stackBytes)
  post := fun (ret, argsRo, tpl, args, st0) s0 sf =>
    ∃∗ st : FmtBuf,
      ⌜IoCallFrame s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ E st.evs ∧
        ∃ cs st₀, decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs ∧
          FmtBufStart (fmtEstimatedCapacity (s0.readReg64 .x1) cs) st₀ ∧
          FmtRun (fmtInnerBudgetStep ArgStep) cs st₀ true st⌝ ∗
      vecHeader ret st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
      fmtBufVecAt A st.cap st.ptr st.bytes ∗ A.pool (A.stepEvents st.evs st0) sf ∗
      fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
      stringWriteVtableAt va ∗ R ∗
      stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)

end VerifiedLibraries.RustStd
