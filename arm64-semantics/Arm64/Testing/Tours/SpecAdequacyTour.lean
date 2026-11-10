/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted
public import Arm64.Testing.Proofs.SpecAdequacyKit
public import Arm64.Testing.Tours.Demo

/-!
# Specification-Language Adequacy: A Guided Tour (`Arm64.Testing.Tours.SpecAdequacyTour`)

- **Layer / Role**: Untrusted test code (`Lib::Arm64Testing`, `Role::Test`, outside the TCB). Imports
  `Arm64.Trusted`, the supporting lemmas in
  [`Proofs/SpecAdequacyKit.lean`](../Proofs/SpecAdequacyKit.lean), and the verified demo and
  fixture theorems in [`Tours/Demo.lean`](Demo.lean);
  nothing in the TCB or proofs imports this file.
- **Audience**: A human reviewer auditing the specification language in
  [`Arm64/Trusted/Spec/`](../../Trusted/Spec/Hoare.lean). Read this file top to bottom; the supporting
  proofs live in [`Proofs/SpecAdequacyKit.lean`](../Proofs/SpecAdequacyKit.lean) and are not part of the
  reading path.
- **Key results**: `rustMemSwap_adequacy` & `rustSliceIndex_adequacy` (for verified `rust_spec`
  contracts in `Tours/Demo.lean`) and `memset_adequacy` (for the
  `c_type_spec` contract `memsetSpec`) show that
  `subroutine_ok prog entry spec` — and therefore the compiled binary theorem on `Obj.PlacedLib.Placeable` —
  implies a plain statement about `Arm64.Steps`, `State.readReg64`, `Memory.read64`,
  `Memory.readBytes`, and `Memory.read8`, with no separation logic in the conclusion.

## Why this file exists: the Iris analogy

Iris proves program properties in a higher-order separation logic with ghost state and invariants,
then uses an *adequacy theorem* to project a triple `{P} e {Q}` down to the plain operational
semantics: `e` does not fault, and if it terminates its result satisfies `Q`. A reviewer can read
that final statement without knowing how the logic is built.

Our specification language has the same layered shape:

| Surface layer (`Arm64/Trusted/Spec/`) | What it means |
| :--- | :--- |
| `c_spec` / `rust_spec` / `c_type_spec` macros (`Abi.lean`, `CType.lean`) | syntax that elaborates to a `Spec α` record |
| `Spec α` with `pre` / `post` (`Hoare.lean`) | separation-logic assertions over a ghost value `x : α` |
| `SepProp`, `∗`, `↦₈`, `↦₆₄`, `↦ₛ`, `memRegion`, `⌜φ⌝` (`SepLogic.lean`) | predicates on partial byte heaps |
| `T.interp`, `UninitSlot n ⇝ MutSlice8 bs`, `Val T` (`CType.lean`) | per-C-type ownership, lowered to the above |
| `subroutine_ok prog entry spec` (`Hoare.lean`) | for every ghost value `x` and every frame `R`, ... |

This file proves, inside Lean, that for representative verified specs in the repository,
`subroutine_ok prog entry spec` (and the concrete binary proofs `rustMemSwap_ok`,
`rustSliceIndex_ok`, and `memset_image_ok`) implies a theorem whose statement mentions only:

- `Arm64.State` fields (`status`, `pc`, `mem`) and `Arm64.Steps prog`,
- `State.readReg64`, `Memory.read8`, `Memory.read64`, `Memory.readBytes`, `Memory.perm`, `Memory.isLazyFree`,
- `Program.CodeLoaded` (code bytes mapped `r-x` and non-`MADV_FREE`) and bit-vector arithmetic.

A reviewer reading `rustMemSwap_adequacy`, `rustSliceIndex_adequacy`, or `memset_adequacy` sees what
the spec guarantees on the hardware model without unfolding `SepProp`, `∗`, or the macros. If a
macro expansion dropped a clause (such as `returns`) or `subroutine_ok` forgot the frame `R`, the
proofs in [`Proofs/SpecAdequacyKit.lean`](../Proofs/SpecAdequacyKit.lean) would not typecheck.
-/

@[expose] public section

namespace Arm64.Testing.SpecAdequacyTour

open Arm64
open Arm64.Testing.Tours.Demo
open Testing.Generators

/-! ## §0 Reading guide: the trusted definitions behind `subroutine_ok`

Here are the definitions in `Arm64/Trusted/Spec/` that the supporting proofs unfold (see
`SepLogic.lean` and `Hoare.lean` for exact definitions):

* `Heap := BitVec 64 → Option HeapCell` is a partial byte map with `.rw b`, `.ro b`, `.protNone b`,
  `.lazy`, and `.protNoneLazy` cells; `SepProp := Heap → Prop`.
* `m ⊨ P` holds when some heap `h` satisfies `P h` and `h.Matches m` (every `.rw b` cell has value
  `b`, permission `Perm.rw`, and `isLazyFree = false` in `m`; every `.ro b` cell has value `b`, is
  readable, and has `isLazyFree = false` in `m`; every `.protNone b` cell has preserved byte value
  `b`, permission `Perm.protNone`, and `isLazyFree = false` in `m`; `.lazy` and `.protNoneLazy`
  also allow `MADV_FREE` bytes where `isLazyFree = true`).
* `P ∗ Q` splits a heap into disjoint parts (sharing only identical `.ro` cells).
* `a ↦₈ v` is the singleton `.rw` byte cell; `a ↦ₛ bs` and `a ↦₆₄ v` are iterated `↦₈`
  (little-endian for `↦₆₄`); `⌜φ⌝` holds of the empty heap when `φ` holds.
* `subroutine_ok prog entry spec` says: for every ghost value `x`, **every frame `R : SepProp`**,
  and every `.Running` state `s₀` at `entry` with 16-byte-aligned `SP`, `prog.CodeLoaded s₀.mem`,
  and `s₀.mem ⊨ spec.pre x s₀ ∗ R`, execution reaches `s'` via `Steps prog s₀ s'` with
  `SubroutineOutcome spec x R s₀ s'`: either a normal return (`pc = X30`, `Running`, calling
  convention preserved, and `s'.mem ⊨ spec.post x s₀ s' ∗ R`), or a panic/exit/out-of-memory stop
  allowed by `spec.onPanic` / `spec.onExit` / `spec.onOom` (all three default to `⌜False⌝`).

Quantifying over **every** frame `R` yields the frame property: [`SpecAdequacyKit.lean`](../Proofs/SpecAdequacyKit.lean)
instantiates `R` with `frameOf fp s₀.mem` ("every readable byte outside footprint `fp` holds its
entry value from `s₀`"), forcing every readable byte outside `fp` to keep its value at `s'`.
-/

/-! ## §1 Example 1: verified `rust_spec` contracts (`mem_swap` and `slice_index`)

We start with two compiled and verified functions from
[`Arm64/Testing/Fixtures/compiled-binary/src/functions.rs`](../Fixtures/compiled-binary/src/functions.rs)
(specified and proved in [`Arm64/Testing/Tours/Demo.lean`](Demo.lean)):

```rust
/// 10. In-place 64-bit memory swap (`ldr` + `str`).
#[inline(never)]
pub fn mem_swap(a: &mut u64, b: &mut u64) {
    core::mem::swap(a, b);
}

/// 9. 64-bit slice indexing (`ldr x0, [x0, x1, lsl #3]`).
#[inline(never)]
pub unsafe fn slice_index(ptr: *const u64, idx: usize) -> u64 {
    unsafe { *ptr.add(idx) }
}
```

### (a) The surface specs (`Arm64/Testing/Tours/Demo.lean`)

In `rustMemSwapSpec`, `(ptrA : ptr)` binds `X0`, `(ptrB : ptr)` binds `X1`, and `(ghost valA : u64)` /
`(ghost valB : u64)` name the 64-bit words at `ptrA` and `ptrB` on entry:
```lean
rust_spec rustMemSwapSpec (ptrA : ptr) (ptrB : ptr) (ghost valA : u64) (ghost valB : u64)
  requires (ptrA ↦₆₄ valA) ∗ (ptrB ↦₆₄ valB)
  ensures  (ptrA ↦₆₄ valB) ∗ (ptrB ↦₆₄ valA)
```
In `rustSliceIndexSpec`, `(ptr : ptr)` binds `X0`, `(idx : usize)` binds `X1`, `(ghost elem : u64)`
is the 64-bit element at `ptr + (idx <<< 3)`, `preserves` requires and ensures that memory cell, and
`returns elem` constrains `X0` on exit:
```lean
rust_spec rustSliceIndexSpec (ptr : ptr) (idx : usize) (ghost elem : u64) : u64
  preserves (ptr + (idx <<< 3)) ↦₆₄ elem
  returns   elem
```

### (b) The elaborated `Spec` records, checked by `rfl` -/

example (ptrA ptrB valA valB : BitVec 64) (s0 : State) :
    rustMemSwapSpec.pre (ptrA, ptrB, valA, valB) s0 =
      (⌜s0.readReg64 .x0 = ptrA ∧ s0.readReg64 .x1 = ptrB⌝ ∗
        ((ptrA ↦₆₄ valA) ∗ (ptrB ↦₆₄ valB))) := rfl

example (ptrA ptrB valA valB : BitVec 64) (s0 sf : State) :
    rustMemSwapSpec.post (ptrA, ptrB, valA, valB) s0 sf =
      ((ptrA ↦₆₄ valB) ∗ (ptrB ↦₆₄ valA)) := rfl

example (x : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (s0 sf : State) :
    rustMemSwapSpec.onPanic x s0 sf = ⌜False⌝ ∧
    rustMemSwapSpec.onOom x s0 sf = ⌜False⌝ := ⟨rfl, rfl⟩

example (ptr idx elem : BitVec 64) (s0 sf : State) :
    rustSliceIndexSpec.pre (ptr, idx, elem) s0 =
      (⌜s0.readReg64 .x0 = ptr ∧ s0.readReg64 .x1 = idx⌝ ∗
        (ptr + (idx <<< 3)) ↦₆₄ elem) ∧
    rustSliceIndexSpec.post (ptr, idx, elem) s0 sf =
      (⌜sf.readReg64 .x0 = elem⌝ ∗ (ptr + (idx <<< 3)) ↦₆₄ elem) := ⟨rfl, rfl⟩

/-! ### (c) Operational adequacy theorems (no `SepProp`, `∗`, `↦`, or `Spec`) -/

/-- **Adequacy of `rustMemSwapSpec`.** Any program meeting `rustMemSwapSpec` terminates without
    fault, panic, exit, or OOM before return, swaps the 64-bit values at `ptrA` and `ptrB`
    whenever `[ptrA, ptrA + 8)` and `[ptrB, ptrB + 8)` are disjoint writable regions, and leaves
    all other readable memory unchanged. -/
theorem rustMemSwapSpec_adequacy (prog : Program) (entry : BitVec 64) :
    subroutine_ok prog entry rustMemSwapSpec →
    ∀ (s₀ : State) (ptrA ptrB : BitVec 64),
      -- ENTRY CONDITIONS: running at `entry`, 16-byte aligned SP, code loaded, X0 = ptrA, X1 = ptrB,
      s₀.status = .Running →
      s₀.pc = entry →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      s₀.readReg64 .x0 = ptrA →
      s₀.readReg64 .x1 = ptrB →
      -- and the 8-byte regions [ptrA, ptrA + 8) and [ptrB, ptrB + 8) are mapped read-write, non-MADV_FREE, and disjoint:
      (∀ a : BitVec 64, (a - ptrA).toNat < 8 → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      (∀ a : BitVec 64, (a - ptrB).toNat < 8 → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      (∀ a : BitVec 64, (a - ptrA).toNat < 8 → 8 ≤ (a - ptrB).toNat) →
      -- CONCLUSION: execution reaches a state s' via the trusted small-step semantics
      ∃ s' : State,
        Steps prog s₀ s' ∧
        -- that returned to the caller's return address X30 in Running status,
        s'.status = .Running ∧
        s'.pc = s₀.readReg64 .x30 ∧
        -- with no fault, halt, panic, exit, or OOM before s' (every state reached from s₀ is
        -- either Running or comes at/after the return state s'; see §3),
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
        -- *ptrA and *ptrB have swapped their 64-bit values,
        s'.mem.read64 ptrA = s₀.mem.read64 ptrB ∧
        s'.mem.read64 ptrB = s₀.mem.read64 ptrA ∧
        -- and every other readable byte is unchanged (the frame property).
        (∀ a : BitVec 64, 8 ≤ (a - ptrA).toNat → 8 ≤ (a - ptrB).toNat →
          (s₀.mem.perm a).r = true → s₀.mem.isLazyFree a = false → s'.mem.read8 a = s₀.mem.read8 a) :=
  fun h_ok => memSwap_spec_adequacy h_ok

/-- **End-to-end operational correctness of `examples::functions::mem_swap` in `examplesLib`.**
    Composes `rustMemSwap_ok` (`Arm64/Testing/Tours/Demo.lean`) with `rustMemSwapSpec_adequacy`. -/
theorem rustMemSwap_adequacy (pl : Obj.Placement) (h : examplesLib.Placeable pl) :
    let prog := examplesLib.program pl Rust.withPanics
    ∀ (s₀ : State) (ptrA ptrB : BitVec 64),
      s₀.status = .Running →
      s₀.pc = prog.fnAddr "examples::functions::mem_swap" →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      s₀.readReg64 .x0 = ptrA →
      s₀.readReg64 .x1 = ptrB →
      (∀ a : BitVec 64, (a - ptrA).toNat < 8 → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      (∀ a : BitVec 64, (a - ptrB).toNat < 8 → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      (∀ a : BitVec 64, (a - ptrA).toNat < 8 → 8 ≤ (a - ptrB).toNat) →
      ∃ s' : State,
        Steps prog s₀ s' ∧
        s'.status = .Running ∧
        s'.pc = s₀.readReg64 .x30 ∧
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
        s'.mem.read64 ptrA = s₀.mem.read64 ptrB ∧
        s'.mem.read64 ptrB = s₀.mem.read64 ptrA ∧
        (∀ a : BitVec 64, 8 ≤ (a - ptrA).toNat → 8 ≤ (a - ptrB).toNat →
          (s₀.mem.perm a).r = true → s₀.mem.isLazyFree a = false → s'.mem.read8 a = s₀.mem.read8 a) :=
  rustMemSwapSpec_adequacy _ _ (rustMemSwap_ok pl h)

/-- **End-to-end operational correctness of `examples::functions::slice_index` in `examplesLib`.**
    Composes `rustSliceIndex_ok` (`Arm64/Testing/Tours/Demo.lean`) with `sliceIndex_spec_adequacy`. -/
theorem rustSliceIndex_adequacy (pl : Obj.Placement) (h : examplesLib.Placeable pl) :
    let prog := examplesLib.program pl Rust.withPanics
    ∀ (s₀ : State) (ptr idx : BitVec 64),
      s₀.status = .Running →
      s₀.pc = prog.fnAddr "examples::functions::slice_index" →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      s₀.readReg64 .x0 = ptr →
      s₀.readReg64 .x1 = idx →
      (∀ a : BitVec 64, (a - (ptr + (idx <<< 3))).toNat < 8 → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      ∃ s' : State,
        Steps prog s₀ s' ∧
        s'.status = .Running ∧
        s'.pc = s₀.readReg64 .x30 ∧
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
        s'.readReg64 .x0 = s₀.mem.read64 (ptr + (idx <<< 3)) ∧
        s'.mem.read64 (ptr + (idx <<< 3)) = s₀.mem.read64 (ptr + (idx <<< 3)) ∧
        (∀ a : BitVec 64, 8 ≤ (a - (ptr + (idx <<< 3))).toNat → (s₀.mem.perm a).r = true → s₀.mem.isLazyFree a = false →
          s'.mem.read8 a = s₀.mem.read8 a) :=
  sliceIndex_spec_adequacy (rustSliceIndex_ok pl h)

/-! ## §2 Example 2: a `c_type_spec` (`memset`)

```c
/* Fill the n bytes at dst with (uint8_t)c and return dst. */
void *memset(void *dst, int c, size_t n);
```

### (a) The surface spec

In `memsetSpec`, `UninitSlot n.toNat ⇝ MutSlice8 (List.replicate n.toNat (c.setWidth 8))`
owns an uninitialized writable buffer `memRegion dst n.toNat` on entry and updates it to the
byte slice `dst ↦ₛ List.replicate n.toNat (c.setWidth 8)` on exit, while `returns dst` constrains
`X0 = dst`: -/

open CType in
c_type_spec memsetSpec (dst : ptr) (c : u32) (n : u64) : ptr where
  c_arg dst : UninitSlot n.toNat ⇝ MutSlice8 (List.replicate n.toNat (c.setWidth 8))
  c_arg c : Val U32
  c_arg n : Val SizeT
  returns dst

/-! ### (b) The elaborated `Spec` record, checked by `rfl` -/

example (dst : BitVec 64) (c : BitVec 32) (n : BitVec 64) (s0 : State) :
    memsetSpec.pre (dst, c, n) s0 =
      (⌜s0.readReg64 .x0 = dst ∧ (s0.readReg64 .x1).truncate 32 = c ∧ s0.readReg64 .x2 = n ∧
          CType.U32.valWf c ∧ CType.SizeT.valWf n⌝ ∗
        memRegion dst n.toNat) := rfl

example (dst : BitVec 64) (c : BitVec 32) (n : BitVec 64) (s0 sf : State) :
    memsetSpec.post (dst, c, n) s0 sf =
      (⌜CType.MutSlice8.pureWf dst (List.replicate n.toNat (c.setWidth 8)) ∧
          sf.readReg64 .x0 = dst⌝ ∗
        CType.MutSlice8.interp dst (List.replicate n.toNat (c.setWidth 8))) := rfl

example (dst : BitVec 64) (c : BitVec 32) (n : BitVec 64) (bs : List (BitVec 8)) :
    CType.MutSlice8.interp dst bs = (dst ↦ₛ bs) ∧
    CType.U32.valWf c = True ∧
    CType.SizeT.valWf n = True := ⟨rfl, rfl, rfl⟩

/-! ### (c) Operational adequacy theorems -/

/-- **Adequacy of `memsetSpec`.** Any program meeting `memsetSpec` terminates without fault,
    panic, exit, or OOM before return, returns `dst` in `X0`, fills the `n.toNat` bytes at `dst`
    with `c.setWidth 8`, and leaves all other readable memory unchanged. -/
theorem memsetSpec_adequacy (prog : Program) (entry : BitVec 64) :
    subroutine_ok prog entry memsetSpec →
    ∀ (s₀ : State) (dst : BitVec 64) (c : BitVec 32) (n : BitVec 64),
      s₀.status = .Running →
      s₀.pc = entry →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      s₀.readReg64 .x0 = dst →
      (s₀.readReg64 .x1).truncate 32 = c →
      s₀.readReg64 .x2 = n →
      -- the n.toNat bytes [dst, dst + n) are mapped read-write and non-MADV_FREE:
      (∀ a : BitVec 64, (a - dst).toNat < n.toNat → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      ∃ s' : State,
        Steps prog s₀ s' ∧
        s'.status = .Running ∧
        s'.pc = s₀.readReg64 .x30 ∧
        -- no fault, halt, panic, exit, or OOM occurs before the return state s' (see §3),
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
        -- X0 returns dst,
        s'.readReg64 .x0 = dst ∧
        -- every byte in [dst, dst + n) is set to the low 8 bits of c,
        s'.mem.readBytes dst n.toNat = List.replicate n.toNat (c.setWidth 8) ∧
        -- and every readable byte outside [dst, dst + n) is unchanged (frame).
        (∀ a : BitVec 64, n.toNat ≤ (a - dst).toNat → (s₀.mem.perm a).r = true → s₀.mem.isLazyFree a = false →
          s'.mem.read8 a = s₀.mem.read8 a) :=
  fun h_ok => memset_spec_adequacy h_ok

/-- **Symbol-level operational adequacy of `memsetSpec`.**
    Composes `prog.subroutineOk "memset" memsetSpec` with `memsetSpec_adequacy`. -/
theorem memset_adequacy (prog : Program) (h_ok : prog.subroutineOk "memset" memsetSpec) :
    ∀ (s₀ : State) (dst : BitVec 64) (c : BitVec 32) (n : BitVec 64),
      s₀.status = .Running →
      s₀.pc = prog.fnAddr "memset" →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      s₀.readReg64 .x0 = dst →
      (s₀.readReg64 .x1).truncate 32 = c →
      s₀.readReg64 .x2 = n →
      (∀ a : BitVec 64, (a - dst).toNat < n.toNat → s₀.mem.perm a = some Perm.rw ∧ s₀.mem.isLazyFree a = false) →
      ∃ s' : State,
        Steps prog s₀ s' ∧
        s'.status = .Running ∧
        s'.pc = s₀.readReg64 .x30 ∧
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
        s'.readReg64 .x0 = dst ∧
        s'.mem.readBytes dst n.toNat = List.replicate n.toNat (c.setWidth 8) ∧
        (∀ a : BitVec 64, n.toNat ≤ (a - dst).toNat → (s₀.mem.perm a).r = true → s₀.mem.isLazyFree a = false →
          s'.mem.read8 a = s₀.mem.read8 a) :=
  memsetSpec_adequacy _ _ h_ok

/-! ## §3 Why "no fault, panic, exit, or OOM before return" depends on determinism

On its own, an existential `∃ s', Steps prog s₀ s' ∧ s'.status = .Running ∧ ...` only says that
*some* execution from `s₀` reaches `s'`. In a nondeterministic semantics, another execution path
from `s₀` could still fault, panic, exit, or run out of memory first.

Here the conclusion rules out every early fault because the trusted small-step semantics `Step`
([`Arm64/Trusted/ISA/Semantics.lean`](../../Trusted/ISA/Semantics.lean)) is **deterministic** and only
`.Running` states can step:

1. **Non-`Running` states are terminal (`Step.status_running`).** Every constructor of `Step`
   requires `s.status = .Running`, so `.Exception`, `.Halted`, `.Panicked`, `.Exited`, and
   `.OutOfMemory` cannot take any further step.
2. **`Step` is a partial function (`Step.deterministic`).** At an extern address exactly one of
   `extern` / `extern_fault` applies (`fetchMem` returns `none` there); elsewhere `externAt?` is
   `none` and at most one of `exec` / `halt_unmapped` applies. Environment nondeterminism (such as
   syscall results) enters only through `State.oracle`, which is fixed as part of `s₀`.
3. **Runs from `s₀` are prefix-comparable (`Steps.compare`).** By induction along `Step.deterministic`,
   for any `Steps prog s₀ s'` and `Steps prog s₀ t`, either `Steps prog s' t` (`t` is at or after
   `s'`) or `Steps prog t s'` (`t` is at or before `s'`, so either `t = s'` or `t` takes a step
   and therefore has `t.status = .Running` by `Step.status_running`).

[`ProofLib/Hoare/Safety.lean`](../../../ProofLib/Hoare/Safety.lean) (and the tour in
[`SepLogicLawsTour.lean`](SepLogicLawsTour.lean)) packages this argument generically for any spec as
`subroutine_ok.no_fault_before_outcome`, `raw_subroutine_ok.no_fault_before_outcome`, and the
`Returned`-disjunct corollaries `subroutine_ok.no_fault_before_return` and
`raw_subroutine_ok.no_fault_before_return`. Because Lean's kernel checks the proof of
`Step.deterministic`, an auditor only needs to **read its statement**: -/

/-- **Read this statement (`Step.deterministic`).** The trusted small-step relation `Step` is
    deterministic: from any state `s`, at most one next state is reachable in a single step. -/
theorem step_deterministic (prog : Program) (s s₁ s₂ : State) :
    Step prog s s₁ → Step prog s s₂ → s₁ = s₂ :=
  Arm64.Step.deterministic

/-! Two properties of the safety conjunct `∀ t, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t`
are worth noting:

* **The guarantee stops at the outcome `s'`.** `prog` is the whole linked program. Once the
  subroutine returns to `s₀.readReg64 .x30` at `s'`, `Steps prog s₀ t` continues into the
  **caller's** code (`Steps prog s' t`), which may later halt, exit, or fault for reasons unrelated
  to the callee. Before `s'`, every reachable state is `.Running`.
* **Why `reaches_outcome` uses `Steps`, and how a sentinel `X30` pins `s'` to the first stop (`StepsUntil (SubroutineStop s₀)`).**
  `subroutine_ok` is defined via `reaches_outcome` using `Steps` rather than `StepsUntil (SubroutineStop s₀)`
  because `AapcsEntry` places no constraint on the caller's entry link register `s₀.readReg64 .x30`
  (as an informal design note, constraining `X30` in `AapcsEntry` would also complicate call-site composition across recursive and multi-return subroutines).
  In particular, if `s₀.pc = s₀.readReg64 .x30`, `SubroutineStop s₀ s₀` already holds on entry and
  `StepsUntil prog (SubroutineStop s₀)` collapses in 0 steps (`stepsUntil_subroutineStop_eq_self_of_lr_eq_pc`).
  Determinism still forces every state prior to `s'` to be `.Running`, so no fault, panic, exit, or
  OOM can occur before `s'`. Whenever a top-level caller or harness sets `X30` to a universal-fetch-none
  sentinel return address (`∀ m, prog.fetchMem m lr = none`, e.g. any unaligned address `lr &&& 3 ≠ 0` such as
  `1#64`, or `subroutineHook`'s `sentinelReturnPC`), execution halts if it ever steps from `X30`, so
  no later `SubroutineOutcome` state exists and `Steps prog s₀ s'` strengthens directly to
  `StepsUntil prog (SubroutineStop s₀) s₀ s'` (`subroutine_ok_stepsUntil_of_sentinel_lr` and
  `subroutine_ok_stepsUntil_of_unaligned_lr` below, proved in
  [`ProofLib/Hoare/Safety.lean`](../../../ProofLib/Hoare/Safety.lean)). -/

/-- **Read this statement (`stepsUntil_subroutineStop_eq_self_of_lr_eq_pc`, 0-step `SubroutineStop` collapse lemma).** Because `AapcsEntry`
    does not constrain `s₀.readReg64 .x30`, setting `s₀.readReg64 .x30 = s₀.pc` at a `.Running`
    entry state makes `SubroutineStop s₀ s₀` hold immediately on entry, forcing
    `StepsUntil prog (SubroutineStop s₀)` to terminate in 0 steps (`sf = s₀`) before the subroutine
    executes a single instruction. -/
theorem stepsUntil_subroutineStop_eq_self_of_lr_eq_pc
    {prog : Program} {s₀ sf : State}
    (hrun : s₀.status = .Running)
    (hlr : s₀.readReg64 Reg.lr = s₀.pc)
    (hsteps : StepsUntil prog (SubroutineStop s₀) s₀ sf) :
    sf = s₀ :=
  ProofLib.stepsUntil_subroutineStop_eq_self_of_lr_eq_pc hrun hlr hsteps

/-- **Read this statement (`subroutine_ok.stepsUntil_of_sentinel_lr`).** When `s₀.readReg64 .x30`
    is a universal-fetch-none return sentinel (`∀ m, prog.fetchMem m lr = none` and `prog.externAt? lr = none`;
    `steps_eq_of_subroutineStop_sentinel_lr` only needs `prog.fetchMem sm.mem lr = none`), `subroutine_ok`
    guarantees `StepsUntil prog (SubroutineStop s₀) s₀ sf`: `sf` is the *first* stopping/return state
    along the deterministic execution from `s₀`. -/
theorem subroutine_ok_stepsUntil_of_sentinel_lr
    {α : Type} {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (hok : subroutine_ok prog entry_pc spec)
    (x : α) (R : SepProp) (s₀ : State)
    (hpc : s₀.pc = entry_pc) (hrun : s₀.status = .Running)
    (hpre : s₀.mem ⊨ spec.pre x s₀ ∗ R) (hsp : s₀.spAligned = true)
    (hL : prog.CodeLoaded s₀.mem)
    (h_fetch : ∀ m, prog.fetchMem m (s₀.readReg64 Reg.lr) = none)
    (h_ext : prog.externAt? (s₀.readReg64 Reg.lr) = none) :
    ∃ sf : State, StepsUntil prog (SubroutineStop s₀) s₀ sf ∧ SubroutineOutcome spec x R s₀ sf :=
  hok.stepsUntil_of_sentinel_lr x R s₀ hpc hrun hpre hsp hL h_fetch h_ext

/-- **Read this statement (`subroutine_ok.stepsUntil_of_unaligned_lr`).** Any non-4-byte-aligned
    sentinel return address (`(s₀.readReg64 .x30).toNat % 4 ≠ 0`, e.g. `X30 = 1#64`) without an
    extern hook automatically satisfies `fetchMem = none` for every memory state, pinning
    `subroutine_ok`'s outcome witness `sf` to `StepsUntil prog (SubroutineStop s₀) s₀ sf`. -/
theorem subroutine_ok_stepsUntil_of_unaligned_lr
    {α : Type} {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (hok : subroutine_ok prog entry_pc spec)
    (x : α) (R : SepProp) (s₀ : State)
    (hpc : s₀.pc = entry_pc) (hrun : s₀.status = .Running)
    (hpre : s₀.mem ⊨ spec.pre x s₀ ∗ R) (hsp : s₀.spAligned = true)
    (hL : prog.CodeLoaded s₀.mem)
    (h_unalign : (s₀.readReg64 Reg.lr).toNat % 4 ≠ 0)
    (h_ext : prog.externAt? (s₀.readReg64 Reg.lr) = none) :
    ∃ sf : State, StepsUntil prog (SubroutineStop s₀) s₀ sf ∧ SubroutineOutcome spec x R s₀ sf :=
  hok.stepsUntil_of_unaligned_lr x R s₀ hpc hrun hpre hsp hL h_unalign h_ext

/-! ## §4 What the adequacy theorems do *not* say

* **Calling-convention registers and permissions.** `subroutine_ok` also guarantees that `SP` and
  callee-saved registers `X19`–`X29` are restored (`subroutine_ok_adequacy` in
  [`SpecAdequacyKit.lean`](../Proofs/SpecAdequacyKit.lean) includes both) and that writable bytes in the frame stay
  writable. The statements above omit those clauses to focus on functional behavior and the memory
  frame; caller-saved `X1`–`X18`, SIMD registers, and `NZCV` may be clobbered per AAPCS64.
* **Unreadable bytes.** `Heap.Matches` describes only readable memory, so the frame clause ranges
  over bytes readable on entry. Non-readable bytes are protected by the ISA itself (`canWrite` and
  `Memory.KeepsFrozen` on every `Step`).
* **Non-zero step count.** `Steps` is reflexive-transitive; a zero-step run can satisfy the
  conclusion only if `s₀` already has `pc = X30` and the post-state memory. After a `BL` call,
  `X30` points past the call site, so the run is non-trivial.
* **Stack usage, hooks, panics, and OOM.** Neither spec has a `stack` / `c_stack` clause (so bytes
  below `SP` are part of the frame `R` and cannot be modified) or allows `panics_when` / `on_exit` /
  `oom_when`. A spec with `stack N` adds `[sp - N, sp)` to the footprint.
* **No `ProofLib` dependency.** Unlike campaign proofs that use `ProofLib`'s `AgreesOutside`, these
  theorems derive the frame property directly from the trusted `subroutine_ok`.

## §5 Small Rust Programs: Operational Hoare Triples

Sections §1–§4 showed how a separation-logic contract (`subroutine_ok prog entry spec`) projects
down to an operational statement about `Arm64.Steps`. To make the hardware and OS boundary equally
concrete on **real compiled Rust**, the eight examples below (compiled from
[`Arm64/Testing/Fixtures/compiled-binary/src/functions.rs`](../Fixtures/compiled-binary/src/functions.rs) and
[`Arm64/Testing/Fixtures/adequacy-tour/src/lib.rs`](../Fixtures/adequacy-tour/src/lib.rs) via the standard
`rust-obj2lean` pipeline at `opt-level = 2`) state operational Hoare triples **directly over
`Obj.PlacedLib.Placeable` and `Arm64.Steps`** with the pre- and postconditions **inlined** (no separate `Spec`
definition). Each theorem proves only what is needed to classify the outcome—either that the
subroutine is **safe until it returns** (or exits the process), or that under a satisfiable
precondition it **definitely reaches an unsafe/terminal state** (`.Panicked`, `.Exception`, or
`.OutOfMemory`, from which no further `Step` is possible by `Step.status_running`). Every theorem is
paired with a machine-checked **precondition-satisfiability witness (`*_pre_sat`)** proving its
hypotheses are non-vacuous; the proofs live in
[`Proofs/SpecAdequacyRustExamples.lean`](../Proofs/SpecAdequacyRustExamples.lean).

### Example 1: `assert!(x == 0)` panics when `x != 0`

```rust
pub fn bad(x: u64) {
    assert!(x == 0);
}
```

* **What it demonstrates**: Calling `examples::functions::bad` with `X0 ≠ 0` branches to
  `core::panicking::panic`, which `tourWithPanics` hooks to `Rust.panicked`, transitioning the
  machine to `ExecStatus.Panicked` (a terminal state by `Step.status_running`).
* **Trust-story claims illustrated**:
  - `docs/trust-story/trust-story.md` **("Safety" &
    "Concrete demo")**: real Rust
    compiled to relocatable ELF (`examplesLib.Placeable pl`) cannot satisfy a safety-until-return
    contract when an assertion can fail. -/

theorem bad_panics (pl : Obj.Placement) (h : examplesLib.Placeable pl) (s₀ : State) :
    let prog := examplesLib.program pl tourWithPanics
    s₀.status = .Running →
    s₀.pc = prog.fnAddr "examples::functions::bad" →
    s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
    prog.CodeLoaded s₀.mem →
    s₀.mem.canWrite (s₀.sp - 16#64) 16 = true →
    s₀.readReg64 .x0 ≠ 0#64 →
    ∃ s' : State, Steps prog s₀ s' ∧ s'.status = .Panicked :=
  bad_panics_proof pl h s₀

#nonvacuous bad_panics :=
  bad_panics_pre_sat

/-! ### Example 2: `assert!(getrandom() > 5)` is unsafe (syscall nondeterminism)

```rust
#[inline(never)]
pub fn assert_getrandom_gt_5() {
    let r = getrandom_u8();
    assert!(r > 5);
}
```

* **What it demonstrates**: `SVC #0` with `X8 = 278` invokes `execSyscall`, which fills the
  1-byte stack buffer from `s₀.oracle.getrandom s₀.oracleIdx 0` and advances `oracleIdx`. Whenever
  the environment oracle supplies a byte `≤ 5`, the assertion fails and reaches `.Panicked`.
* **Trust-story claims illustrated**:
  - `docs/trust-story/trust-story.md` **("Other
    syscalls" & "Safety")**: `Step` stays
    deterministic by parameterizing `State` over `oracle : Oracle`; universally
    quantifying over `s₀` (and hence `s₀.oracle`) ranges over *every* possible random stream. -/

theorem assert_getrandom_gt_5_panics (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    s₀.status = .Running →
    s₀.pc = prog.fnAddr "adequacy_tour::assert_getrandom_gt_5" →
    s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
    prog.CodeLoaded s₀.mem →
    s₀.mem.canRead (s₀.sp - 20#64) 1 = true →
    s₀.mem.canWrite (s₀.sp - 20#64) 20 = true →
    (s₀.oracle.getrandom s₀.oracleIdx 0).ule 5#8 = true →
    ∃ s' : State, Steps prog s₀ s' ∧ s'.status = .Panicked :=
  assert_getrandom_gt_5_panics_proof pl h s₀

theorem assert_getrandom_gt_5_panics_satisfiable :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::assert_getrandom_gt_5" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem ∧
      s₀.mem.canRead (s₀.sp - 20#64) 1 = true ∧
      s₀.mem.canWrite (s₀.sp - 20#64) 20 = true ∧
      (s₀.oracle.getrandom s₀.oracleIdx 0).ule 5#8 = true :=
  assert_getrandom_gt_5_panics_pre_sat

/-! ### Example 3: `mmap` page allocation — safe until return vs. `OutOfMemory`

```rust
#[inline(never)]
pub fn mmap_write_and_verify(x: u64) -> u64 {
    let page = mmap_one_page();
    // SAFETY: When `mmap` succeeds in the model, `page` points to a freshly mapped,
    // zero-initialized 4096-byte `Perm.rw` region.
    let v0 = unsafe { core::ptr::read_volatile(page) };
    let expected = x.wrapping_add(7);
    unsafe {
        core::ptr::write_volatile(page, expected.wrapping_add(v0));
    }
    let v1 = unsafe { core::ptr::read_volatile(page) };
    assert!(v1 == expected);
    v1
}
```

* **What it demonstrates**: `SVC #0` with `X8 = 222` invokes `execMmap`. When the oracle page
  `p := s₀.oracle.mmap s₀.oracleIdx` is non-zero, 4096-aligned, within the 48-bit user VA space,
  and unmapped (`s₀.mem.canMap p 4096 = true`), `execMmap` maps `[p, p + 4096)` as zero-filled
  `Perm.rw`, and the function verifies zero-initialization, writes `x + 7`, reads it back, and
  returns safely (`mmap_write_and_verify_safe`). Conversely, when no 4 KiB page can be mapped in
  user VA space (`sanitizeMmapAddr s₀.mem (s₀.oracle.mmap s₀.oracleIdx) 4096 = none`), `execMmap`
  transitions to `ExecStatus.OutOfMemory` (`mmap_write_and_verify_oom`).
* **Trust-story claims illustrated**:
  - `docs/trust-story/trust-story.md` **("Virtual
    memory and memory exhaustion")**:
    `canMap` guarantees no existing mapping is overwritten (`KeepsFrozen`), newly mapped pages are
    zero-filled `Perm.rw`, and OOM is a distinguished terminal status (`ExecStatus.OutOfMemory`). -/

theorem mmap_write_and_verify_safe (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    let page := s₀.oracle.mmap s₀.oracleIdx
    s₀.status = .Running →
    s₀.pc = prog.fnAddr "adequacy_tour::mmap_write_and_verify" →
    s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
    prog.CodeLoaded s₀.mem →
    MMAP_MIN_ADDR ≤ page.toNat →
    page.toNat % 4096 = 0 →
    page.toNat + 4096 ≤ 2 ^ 48 →
    s₀.mem.canMap page 4096 = true →
    4096 ≤ s₀.physMemAvail →
    ∃ s' : State,
      Steps prog s₀ s' ∧
      s'.status = .Running ∧
      s'.pc = s₀.readReg64 .x30 ∧
      (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) :=
  mmap_write_and_verify_safe_proof pl h s₀

theorem mmap_write_and_verify_safe_satisfiable :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::mmap_write_and_verify" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem ∧
      MMAP_MIN_ADDR ≤ (s₀.oracle.mmap s₀.oracleIdx).toNat ∧
      (s₀.oracle.mmap s₀.oracleIdx).toNat % 4096 = 0 ∧
      (s₀.oracle.mmap s₀.oracleIdx).toNat + 4096 ≤ 2 ^ 48 ∧
      s₀.mem.canMap (s₀.oracle.mmap s₀.oracleIdx) 4096 = true ∧
      4096 ≤ s₀.physMemAvail :=
  mmap_write_and_verify_safe_pre_sat

theorem mmap_write_and_verify_oom (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    s₀.status = .Running →
    s₀.pc = prog.fnAddr "adequacy_tour::mmap_write_and_verify" →
    s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
    prog.CodeLoaded s₀.mem →
    sanitizeMmapAddr s₀.mem (s₀.oracle.mmap s₀.oracleIdx) 4096 = none →
    ∃ s' : State,
      Steps prog s₀ s' ∧
      s'.status = .OutOfMemory ∧
      (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) :=
  mmap_write_and_verify_oom_proof pl h s₀

theorem mmap_write_and_verify_oom_satisfiable :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::mmap_write_and_verify" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem ∧
      sanitizeMmapAddr s₀.mem (s₀.oracle.mmap s₀.oracleIdx) 4096 = none :=
  mmap_write_and_verify_oom_pre_sat

/-! ### Example 4: Exiting the whole process with exit status 1

```rust
#[inline(never)]
pub fn nonzero_exit_one(x: u64) -> ! {
    let code = if x == 0 { 0 } else { 1 };
    exit_group(code)
}
```

* **What it demonstrates**: When `X0 ≠ 0`, `nonzero_exit_one` executes `SVC #0` with `X8 = 94`
  (`__NR_exit_group`) and `X0 = 1`, reaching `s'.status = .Exited 1#64` with no fault prior to exit
  (`∀ t, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t`).
* **Trust-story claims illustrated**:
  - `docs/trust-story/trust-story.md` **("Other
    syscalls" & "Safety")**:
    whole-process termination is modeled explicitly via `ExecStatus.Exited (s.readReg64 .x0)`,
    corresponding to the `SubroutineOutcome` `.Exited` branch (`onExit`). -/

theorem nonzero_exit_one (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl) (s₀ : State) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    s₀.status = .Running →
    s₀.pc = prog.fnAddr "adequacy_tour::nonzero_exit_one" →
    s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
    prog.CodeLoaded s₀.mem →
    s₀.readReg64 .x0 ≠ 0#64 →
    ∃ s' : State,
      Steps prog s₀ s' ∧
      s'.status = .Exited 1#64 ∧
      (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) :=
  nonzero_exit_one_proof pl h s₀

theorem nonzero_exit_one_satisfiable :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::nonzero_exit_one" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem ∧
      s₀.readReg64 .x0 ≠ 0#64 :=
  nonzero_exit_one_pre_sat

/-! ### Example 5: Reading from an unmapped fixed address via inline assembly faults

```rust
#[inline(never)]
pub fn read_fixed_addr() -> u64 {
    let val: u64;
    // SAFETY (intentionally unsafe when `FIXED_ADDR` is unmapped):
    // Reads 8 bytes from the hardcoded address `0xdead_beef_0000`.
    unsafe {
        asm!(
            "ldr {val}, [{addr}]",
            addr = in(reg) FIXED_ADDR,
            val = lateout(reg) val,
            options(nostack, preserves_flags)
        );
    }
    val
}
```

* **What it demonstrates**: Loading 8 bytes from `0x0000_dead_beef_0000` when those bytes are not
  mapped readable (`s₀.mem.canRead 0xdeadbeef0000#64 8 = false`) transitions to
  `ExecStatus.Exception msg` (`"permission fault"`).
* **Trust-story claims illustrated**:
  - `docs/trust-story/trust-story.md` **("Virtual
    memory and memory exhaustion" & "Safety")**: `execLdr` checks
    `s.mem.canRead addr width` on every load and transitions to `ExecStatus.Exception` on failure. -/

theorem read_fixed_addr_faults (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    s₀.status = .Running →
    s₀.pc = prog.fnAddr "adequacy_tour::read_fixed_addr" →
    s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
    prog.CodeLoaded s₀.mem →
    s₀.mem.canRead 0xdeadbeef0000#64 8 = false →
    ∃ s' : State, ∃ msg : String, Steps prog s₀ s' ∧ s'.status = .Exception msg :=
  read_fixed_addr_faults_proof pl h s₀

theorem read_fixed_addr_faults_satisfiable :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::read_fixed_addr" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem ∧
      s₀.mem.canRead 0xdeadbeef0000#64 8 = false :=
  read_fixed_addr_faults_pre_sat

/-! ### Example 6: Reading one's own code bytes and asserting their encoding is safe

```rust
#[inline(never)]
pub fn verify_own_code_bytes() {
    let insn_word: u32;
    // SAFETY: `adr` computes the runtime address of label `2:` inside this function's
    // own `.text` section, and `ldr` reads that 4-byte instruction word (`Perm.rx`).
    unsafe {
        asm!(
            "adr {tmp}, 2f",
            "2:",
            "nop",
            "ldr {w:w}, [{tmp}]",
            tmp = out(reg) _,
            w = out(reg) insn_word,
            options(nostack, preserves_flags)
        );
    }
    assert!(insn_word == NOP_INSN_WORD);
}
```

* **What it demonstrates**: `verify_own_code_bytes` computes the runtime PC-relative address of its
  own `nop` instruction via `adr`, loads the 32-bit word (`ldr w9, [x8]`), and asserts that it
  equals the A64 encoding of `NOP` (`0xd503_201f`). Because `prog.CodeLoaded s₀.mem` requires every
  code byte `[prog.base, prog.base + prog.code.length)` to be mapped with `Perm.rx` (readable and
  executable) and equal to the compiled code byte, `canRead` succeeds and `read32` returns
  `0xd503_201f`, so the assertion never panics—requiring **no stack or data preconditions at all**.
* **Trust-story claims illustrated**:
  - `docs/trust-story/trust-story.md` **("Arm64 ISA
    semantics — `Program.CodeLoaded`")**: `prog.CodeLoaded s₀.mem`
    ties the execution semantics `Step.exec` and data loads `Memory.read32` to the exact same
    underlying `Perm.rx` byte array in `s₀.mem`. -/

theorem verify_own_code_bytes_safe (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    s₀.status = .Running →
    s₀.pc = prog.fnAddr "adequacy_tour::verify_own_code_bytes" →
    s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
    prog.CodeLoaded s₀.mem →
    ∃ s' : State,
      Steps prog s₀ s' ∧
      s'.status = .Running ∧
      s'.pc = s₀.readReg64 .x30 ∧
      (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) :=
  verify_own_code_bytes_safe_proof pl h s₀

theorem verify_own_code_bytes_safe_satisfiable :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::verify_own_code_bytes" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem :=
  verify_own_code_bytes_safe_pre_sat

/-! ### Example 7: Attempting to overwrite one's own code bytes faults (W^X enforcement)

```rust
#[inline(never)]
pub fn write_own_code_bytes() {
    // SAFETY (intentionally faults under W^X): attempts to store a 32-bit word into
    // this function's own `.text` section (`Perm.rx`).
    unsafe {
        asm!(
            "adr {tmp}, 2f",
            "str {val:w}, [{tmp}]",
            "2:",
            "nop",
            tmp = out(reg) _,
            val = in(reg) NOP_INSN_WORD,
            options(nostack, preserves_flags)
        );
    }
}
```

* **What it demonstrates**: `write_own_code_bytes` computes the address of its own `nop` instruction
  via `adr` and attempts `str w8, [x9]`. Because `prog.CodeLoaded s₀.mem` maps code bytes with
  `Perm.rx` (`w = false, x = true`) and `Memory.canWrite` requires `p.w && !p.x`, the store
  necessarily faults with `ExecStatus.Exception msg` under `CodeLoaded` alone.
* **Trust-story claims illustrated**:
  - `docs/trust-story/trust-story.md` **("Arm64 ISA
    semantics — `Program.CodeLoaded` `Perm.rx`")**: the permission
    type (`Perm.protNone`, `.ro`, `.rw`, `.rx`) and `canWrite` enforce W^X on `Perm.rx` code pages, making
    self-modifying writes impossible without an explicit permission fault. -/

theorem write_own_code_bytes_faults (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    s₀.status = .Running →
    s₀.pc = prog.fnAddr "adequacy_tour::write_own_code_bytes" →
    s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
    prog.CodeLoaded s₀.mem →
    ∃ s' : State, ∃ msg : String, Steps prog s₀ s' ∧ s'.status = .Exception msg :=
  write_own_code_bytes_faults_proof pl h s₀

theorem write_own_code_bytes_faults_satisfiable :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::write_own_code_bytes" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem :=
  write_own_code_bytes_faults_pre_sat

/-! ### Example 8: Hardware SP 16-byte alignment check (`SCTLR_EL1.SA`) vs. aligned stack safety

```rust
#[inline(never)]
pub fn stack_spill_verify(x: u64) -> u64 {
    let mut slot: u64 = 0;
    let ptr = core::ptr::addr_of_mut!(slot);
    let expected = x.wrapping_add(1);
    // SAFETY: `ptr` points to the 8-byte stack slot `slot`.
    let loaded = unsafe {
        core::ptr::write_volatile(ptr, expected);
        core::ptr::read_volatile(ptr)
    };
    assert!(loaded == expected);
    loaded
}
```

* **What it demonstrates**: Compiling `stack_spill_verify` emits a standard stack-frame prologue
  (`sub sp, sp, #32; str x30, [sp, #16]`). When `SP` is **not** 16-byte aligned on entry
  (`s₀.readReg64 .sp &&& 0xF#64 ≠ 0#64`), `sub sp, sp, #32` preserves `(sp &&& 15) ≠ 0`, and the
  very first SP-based store `str x30, [sp, #16]` faults with `ExecStatus.Exception "SP alignment fault"`
  (`stack_spill_verify_unaligned_faults`)—even if the stack bytes are mapped `Perm.rw`! Conversely,
  when `SP` is 16-byte aligned and `[sp - 24, sp)` is mapped `Perm.rw`, the function spills `x + 1`,
  reads it back, passes the assertion, and returns safely (`stack_spill_verify_safe`).
* **Trust-story claims illustrated**:
  - `docs/trust-story/trust-story.md` **("Safety" &
    "Modeling the Rust and arm64 ABIs — `AapcsEntry`")**: explains why
    `s₀.readReg64 .sp &&& 0xF#64 = 0#64` is an essential hardware precondition of `subroutine_ok`
    rather than a bureaucratic artifact. -/

theorem stack_spill_verify_unaligned_faults (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    s₀.status = .Running →
    s₀.pc = prog.fnAddr "adequacy_tour::stack_spill_verify" →
    prog.CodeLoaded s₀.mem →
    s₀.readReg64 .sp &&& 0xF#64 ≠ 0#64 →
    ∃ s' : State, ∃ msg : String, Steps prog s₀ s' ∧ s'.status = .Exception msg :=
  stack_spill_verify_unaligned_faults_proof pl h s₀

theorem stack_spill_verify_unaligned_faults_satisfiable :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::stack_spill_verify" ∧
      prog.CodeLoaded s₀.mem ∧
      s₀.readReg64 .sp &&& 0xF#64 ≠ 0#64 :=
  stack_spill_verify_unaligned_faults_pre_sat

theorem stack_spill_verify_safe (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    s₀.status = .Running →
    s₀.pc = prog.fnAddr "adequacy_tour::stack_spill_verify" →
    s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
    prog.CodeLoaded s₀.mem →
    s₀.mem.canRead (s₀.sp - 24#64) 24 = true →
    s₀.mem.canWrite (s₀.sp - 24#64) 24 = true →
    ∃ s' : State,
      Steps prog s₀ s' ∧
      s'.status = .Running ∧
      s'.pc = s₀.readReg64 .x30 ∧
      (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) :=
  stack_spill_verify_safe_proof pl h s₀

theorem stack_spill_verify_safe_satisfiable :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::stack_spill_verify" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem ∧
      s₀.mem.canRead (s₀.sp - 24#64) 24 = true ∧
      s₀.mem.canWrite (s₀.sp - 24#64) 24 = true :=
  stack_spill_verify_safe_pre_sat

/-! ## §6 Axiom check

All tour theorems depend only on Lean's three standard axioms.
-/

/--
info: 'Arm64.Testing.SpecAdequacyTour.rustMemSwap_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rustMemSwap_adequacy

/--
info: 'Arm64.Testing.SpecAdequacyTour.rustSliceIndex_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rustSliceIndex_adequacy

/--
info: 'Arm64.Testing.SpecAdequacyTour.memset_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms memset_adequacy

/--
info: 'Arm64.Testing.SpecAdequacyTour.step_deterministic' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms step_deterministic

/--
info: 'Arm64.Testing.SpecAdequacyTour.stepsUntil_subroutineStop_eq_self_of_lr_eq_pc' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms stepsUntil_subroutineStop_eq_self_of_lr_eq_pc

/--
info: 'Arm64.Testing.SpecAdequacyTour.subroutine_ok_stepsUntil_of_sentinel_lr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms subroutine_ok_stepsUntil_of_sentinel_lr

/--
info: 'Arm64.Testing.SpecAdequacyTour.subroutine_ok_stepsUntil_of_unaligned_lr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms subroutine_ok_stepsUntil_of_unaligned_lr

/--
info: 'Arm64.Testing.SpecAdequacyTour.bad_panics' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bad_panics

/--
info: 'Arm64.Testing.SpecAdequacyTour.assert_getrandom_gt_5_panics' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms assert_getrandom_gt_5_panics

/--
info: 'Arm64.Testing.SpecAdequacyTour.mmap_write_and_verify_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mmap_write_and_verify_safe

/--
info: 'Arm64.Testing.SpecAdequacyTour.mmap_write_and_verify_oom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mmap_write_and_verify_oom

/--
info: 'Arm64.Testing.SpecAdequacyTour.nonzero_exit_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nonzero_exit_one

/--
info: 'Arm64.Testing.SpecAdequacyTour.read_fixed_addr_faults' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms read_fixed_addr_faults

/--
info: 'Arm64.Testing.SpecAdequacyTour.verify_own_code_bytes_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms verify_own_code_bytes_safe

/--
info: 'Arm64.Testing.SpecAdequacyTour.write_own_code_bytes_faults' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms write_own_code_bytes_faults

/--
info: 'Arm64.Testing.SpecAdequacyTour.stack_spill_verify_unaligned_faults' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms stack_spill_verify_unaligned_faults

/--
info: 'Arm64.Testing.SpecAdequacyTour.stack_spill_verify_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stack_spill_verify_safe

/-! ## §7 Unfolding `Program.subroutineOk` at a named symbol

Top-level library theorems state function contracts by symbol name (`prog.subroutineOk fnName spec`).
Looking up `fnName` in `prog`'s symbol table (`prog.findSymbol? fnName = some off`) fixes the entry
address `prog.base + BitVec.ofNat 64 off` and unpacks `Program.subroutineOk` directly into:
1. termination in some state `sf` (`Steps prog s₀ sf`);
2. pre-outcome safety (`∀ t, Steps prog s₀ t → t.status = .Running ∨ Steps prog sf t`), ruling out
   any `.Exception` (such as an out-of-bounds memory access) or `.Halted` state before `sf`; and
3. the explicit four-way outcome disjunction (where `onPanic`, `onExit`, and `onOom` all default to
   `⌜False⌝`, leaving only normal return when left unspecified). -/

theorem subroutineOk_unfold {α : Type} (prog : Program) (fnName : String) (off : Nat)
    (spec : Spec α) :
    prog.subroutineOk fnName spec →
    prog.findSymbol? fnName = some off →
    ∀ (x : α) (R : SepProp) (s₀ : State),
      s₀.pc = prog.base + BitVec.ofNat 64 off →
      s₀.status = .Running →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      (s₀.mem ⊨ spec.pre x s₀ ∗ R) →
      ∃ sf : State,
        Steps prog s₀ sf ∧
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog sf t) ∧
        ((sf.status = .Running ∧
          sf.pc = s₀.readReg64 .x30 ∧
          sf.sp = s₀.sp ∧
          CalleeSavedPreserved s₀ sf ∧
          (sf.mem ⊨ spec.post x s₀ sf ∗ R)) ∨
         (sf.status = .Panicked ∧ (sf.mem ⊨ spec.onPanic x s₀ sf ∗ R)) ∨
         (∃ code, sf.status = .Exited code ∧ (sf.mem ⊨ spec.onExit x code s₀ sf ∗ R)) ∨
         (sf.status = .OutOfMemory ∧ (sf.mem ⊨ spec.onOom x s₀ sf ∗ R))) :=
  subroutineOk_unfold_proof prog fnName off spec

/--
info: 'Arm64.Testing.SpecAdequacyTour.subroutineOk_unfold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms subroutineOk_unfold

end Arm64.Testing.SpecAdequacyTour
