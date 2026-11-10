/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec.Top

/-!
# Cost-Model-Parametric `mallocng` Specification

Parameterizes the six placed C allocator specifications of `mallocng` over an abstract stateful
memory cost model `AllocCostModel`, decoupling caller out-of-memory reasoning from fixed
allocator-internal budget constants. Also defines `mallocngTight2CostModel`, a usage-indexed cost
model parameterized by `U = peakCount + 6` via explicit root-group step tables.
-/

@[expose] public section

namespace VerifiedLibraries.Mallocng

open Arm64 Arm64.CType

/-! ## Allocator Events and Cost Models -/

/-- One successful allocator call, as recorded in a caller's ghost allocation log:
    - `alloc req`: `malloc(req)` or `calloc` with `req = nmemb * size`;
    - `aligned align req`: `aligned_alloc(align, req)` or `posix_memalign(_, align, req)`;
    - `free align req`: `free(p)` of a live block of `req` bytes allocated at alignment `align`;
    - `realloc align old new`: `realloc(p, new)` of a live block of `old` bytes allocated at
      alignment `align` (`realloc(NULL, new)` is `alloc new`). -/
inductive AllocEvent where
  | alloc (req : Nat)
  | aligned (align req : Nat)
  | free (align req : Nat)
  | realloc (align old new : Nat)
  deriving DecidableEq, Repr

/-- Stateful memory cost model for `mallocng`: abstract state `σ` starting at `init` for the empty
    heap, advanced by `step` on every successful call, bounding the allocator's dynamic mappings by
    `maxDynIvs` intervals of `footprint` total bytes, and bounding the bytes newly mapped (and any
    failing `mmap` request) by one call executing `ev` from state `st` by `stepReserve ev st`. -/
structure AllocCostModel : Type 1 where
  σ : Type
  init : σ
  step : AllocEvent → σ → σ
  footprint : σ → Nat
  maxDynIvs : σ → Nat
  stepReserve : AllocEvent → σ → Nat

/-- Out-of-memory postcondition of one `mallocng` call with step reserve `stepBytes`: preserves
    `fs`, `trace`, and `sigActions`, and maps at most `16` new intervals `ivs` of `≤ stepBytes`
    total bytes; under sanitized `mmap` it witnesses a failing page-aligned request `sz` with
    `ivs` bytes plus `sz` together `≤ stepBytes` (so one reserve covers both the partial mappings
    and the refused request) and no unmapped VA gap of size `sz` or `sf.physMemAvail < sz`.
    Implies `MallocngOomCond svc reqBytes peakCount` whenever
    `stepBytes ≤ MallocngStepBound reqBytes peakCount`. -/
def MallocngStepOomCond (svc : State → State) (stepBytes : Nat) (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
  sf.trace = s0.trace ∧
  sf.sigActions = s0.sigActions ∧
  ∃ ivs : List (BitVec 64 × Nat),
    ivs.length ≤ 16 ∧
    (ivs.map Prod.snd).sum ≤ stepBytes ∧
    (∀ a : BitVec 64, (sf.mem.perm a).mapped = true →
      (s0.mem.perm a).mapped = true ∨ MallocngInIntervals ivs a) ∧
    (MallocngSanitizedSvc svc →
      ∃ sz : Nat,
        PAGE_SIZE ≤ sz ∧
        sz % PAGE_SIZE = 0 ∧
        (ivs.map Prod.snd).sum + sz ≤ stepBytes ∧
        MallocngNoGapOrPhys sf sz)

/-! ## Model-Indexed Interface, Environment, and Block Types -/

/-- Separation-logic predicates of a `mallocng` instance indexed by `M.σ`: `HeapM` / `CoreM` as in
    `MallocngIface` with the model state in place of `MallocngBudget`, and the ghost block token
    `BlockM γ p n effAlign` carrying the effective alignment (`16` for `malloc` / `calloc`,
    `max align 16` for `aligned_alloc` / `posix_memalign`) needed by `free` / `realloc` events. -/
structure MallocngCostModelIface (M : AllocCostModel) where
  HeapM :
    GhostName → MallocngAddrs → BitVec 64 → BitVec 64 → BitVec 64 →
      M.σ → List (BitVec 64 × Nat) → SepProp
  CoreM :
    GhostName → MallocngAddrs → BitVec 64 → BitVec 64 →
      M.σ → List (BitVec 64 × Nat) → SepProp
  BlockM : GhostName → BitVec 64 → Nat → Nat → SepProp
  block_noWrap : ∀ (γ : GhostName) (p : BitVec 64) (n effAlign : Nat),
    BlockM γ p n effAlign ⊢ ⌜p.toNat + n ≤ 2 ^ 64⌝ ∗ BlockM γ p n effAlign

/-- Model-indexed allocator environment (`MallocngEnv` over `I`). -/
def MallocngModelEnv (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (st : M.σ) (ivs : List (BitVec 64 × Nat)) (s : State) : SepProp :=
  ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
    I.HeapM γ A tp brkStart s.brk st ivs

/-- Model-indexed post-call allocator environment (`MallocngPostEnv` over `I`). -/
def MallocngModelPostEnv (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (stf : M.σ) (ivs0 : List (BitVec 64 × Nat)) (s0 sf : State) : SepProp :=
  ∃∗ ivsf : List (BitVec 64 × Nat),
    ⌜MallocngNoOrphanMappings ivs0 ivsf s0.mem sf.mem⌝ ∗
    MallocngModelEnv M I γ A tp brkStart stf ivsf sf

/-- Live uninitialized block of `n` bytes at effective alignment `effAlign`. -/
@[reducible] def MallocngModelBlock {M : AllocCostModel} (I : MallocngCostModelIface M)
    (γ : GhostName) : SemType (Nat × Nat) where
  tyName := "void * (mallocng allocated block)"
  interp := fun p (n, effAlign) => I.BlockM γ p n effAlign ∗ memRegion p n
  pureWf := fun p (n, effAlign) => p ≠ 0#64 ∧ effAlign ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

/-- Live zero-initialized block of `n` bytes at effective alignment `effAlign`. -/
@[reducible] def MallocngModelZeroedBlock {M : AllocCostModel} (I : MallocngCostModelIface M)
    (γ : GhostName) : SemType (Nat × Nat) where
  tyName := "void * (zero-initialized mallocng block)"
  interp := fun p (n, effAlign) => I.BlockM γ p n effAlign ∗ (p ↦ₛ List.replicate n 0#8)
  pureWf := fun p (n, effAlign) => p ≠ 0#64 ∧ effAlign ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

/-- Live block of `sz` bytes allocated at alignment `align` whose first `bs.length` bytes hold
    `bs`. -/
@[reducible] def MallocngModelInitBlock {M : AllocCostModel} (I : MallocngCostModelIface M)
    (γ : GhostName) : SemType (Nat × Nat × List (BitVec 8)) where
  tyName := "void * (mallocng block with initialized prefix)"
  interp := fun p (sz, align, bs) =>
    I.BlockM γ p sz (max align 16) ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (sz - bs.length)
  pureWf := fun p (sz, _, bs) =>
    p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + sz < 2 ^ 64 ∧ bs.length ≤ sz

/-- Nullable block of `n` bytes allocated at alignment `align` passed to `free`. -/
@[reducible] def MallocngModelFreeableBlock {M : AllocCostModel} (I : MallocngCostModelIface M)
    (γ : GhostName) : SemType (Nat × Nat) where
  tyName := "void * (nullable mallocng allocated block)"
  interp := fun p (n, align) =>
    if p = 0#64 then emp else I.BlockM γ p n (max align 16) ∗ memRegion p n
  pureWf := fun p (n, _) => if p = 0#64 then n = 0 else 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

/-! ## Model-Indexed Public C Allocator Specifications

Each successful call advances the model state by exactly one `AllocEvent`; a failing call
(`NULL` / `ENOMEM`) leaves it unchanged. Newly mapped bytes on `.Running` and the out-of-memory
witness on `.OutOfMemory` are both bounded by the model's `stepReserve` of that event (of
`.alloc 0` for a request rejected before any mapping, and of `.realloc 16 0 new` for
`realloc(NULL, new)`). -/

/-- `void *malloc(size_t req)` over `M`. -/
c_type_spec mallocngModelMallocSpec (ctx M : AllocCostModel) (ctx I : MallocngCostModelIface M)
    (ctx svc : State → State) (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (req : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost st : M.σ)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := decide (req.toNat ≤ MallocngMaxAllocSize)
  let ev := AllocEvent.alloc req.toNat
  let st' := if ok then M.step ev st else st
  let stepB := if ok then M.stepReserve ev st else M.stepReserve (.alloc 0) st
  c_arg req : Val SizeT
  c_ret : Own (OptOwn (MallocngModelBlock I γ))
    (if ok then some (req.toNat, 16) else none)
  c_env (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when MallocngStepOomCond svc stepB s0 sf

/-- `void free(void *p)` over `M` (maps nothing). -/
c_type_spec mallocngModelFreeSpec (ctx M : AllocCostModel) (ctx I : MallocngCostModelIface M)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (p : ptr) (sp : sp)
    (ghost n align : Nat) (ghost tp brkStart : BitVec 64) (ghost st : M.σ)
    (ghost ivs0 : List (BitVec 64 × Nat)) where
  let st' := if p == 0#64 then st else M.step (.free align n) st
  c_arg p : Own (MallocngModelFreeableBlock I γ) (n, align)
  c_env (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 0 0 s0 sf

/-- `void *calloc(size_t nmemb, size_t size)` over `M` (emits `.alloc (nmemb * size)`). -/
c_type_spec mallocngModelCallocSpec (ctx M : AllocCostModel) (ctx I : MallocngCostModelIface M)
    (ctx svc : State → State) (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (nmemb : u64) (size : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost st : M.σ)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let total := nmemb.toNat * size.toNat
  let ok := decide (total ≤ MallocngMaxAllocSize)
  let ev := AllocEvent.alloc total
  let st' := if ok then M.step ev st else st
  let stepB := if ok then M.stepReserve ev st else M.stepReserve (.alloc 0) st
  c_arg nmemb : Val SizeT
  c_arg size : Val SizeT
  c_ret : Own (OptOwn (MallocngModelZeroedBlock I γ))
    (if ok then some (total, 16) else none)
  c_env (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when MallocngStepOomCond svc stepB s0 sf

/-- `void *realloc(void *p, size_t newSize)` over `M`: emits `.alloc newSize` when
    `oldBlk = none` (`p = NULL`) and `.realloc align oldSize newSize` when
    `oldBlk = some (oldSize, align, bs)`. -/
c_type_spec mallocngModelReallocSpec (ctx M : AllocCostModel) (ctx I : MallocngCostModelIface M)
    (ctx svc : State → State) (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (p : ptr) (newSize : u64) (sp : sp)
    (ghost oldBlk : Option (Nat × Nat × List (BitVec 8)))
    (ghost tp brkStart : BitVec 64) (ghost st : M.σ)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
  let keptBs := ((oldBlk.map fun (_, _, bs) => bs).getD []).take newSize.toNat
  let ev : AllocEvent := match oldBlk with
    | none => .alloc newSize.toNat
    | some (oldSize, align, _) => .realloc align oldSize newSize.toNat
  let evRes : AllocEvent := match oldBlk with
    | none => .realloc 16 0 newSize.toNat
    | some (oldSize, align, _) => .realloc align oldSize newSize.toNat
  let outAlign : Nat := match oldBlk with
    | none => 16
    | some (_, align, _) => max align 16
  let st' := if ok then M.step ev st else st
  let stepB := if ok then M.stepReserve evRes st else M.stepReserve (.alloc 0) st
  c_arg p : MutRef (CondOwn (OptOwn (MallocngModelInitBlock I γ))) (some oldBlk) ⇝
    (if ok then none else some oldBlk)
  c_arg newSize : Val SizeT
  c_ret : Own (OptOwn (MallocngModelInitBlock I γ))
    (if ok then some (newSize.toNat, outAlign, keptBs) else none)
  c_env (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when MallocngStepOomCond svc stepB s0 sf

/-- `void *aligned_alloc(size_t align, size_t len)` over `M`. -/
c_type_spec mallocngModelAlignedAllocSpec (ctx M : AllocCostModel)
    (ctx I : MallocngCostModelIface M) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (align : u64) (len : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost st : M.σ)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := mallocngAlignedAllocOk align len
  let ev := AllocEvent.aligned align.toNat len.toNat
  let st' := if ok then M.step ev st else st
  let stepB := if ok then M.stepReserve ev st else M.stepReserve (.alloc 0) st
  caveat [API_RESTRICTION] "align ≤ 2^31 avoids musl 1.2.5 set_size int32 reserved overflow" :
    align.toNat ≤ MaxAlignedAllocAlign
  c_arg align : Val SizeT
  c_arg len : Val SizeT
  c_ret : Own (OptOwn (MallocngModelBlock I γ))
    (if ok then some (len.toNat, max align.toNat 16) else none)
  c_env (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when MallocngStepOomCond svc stepB s0 sf

/-- `int posix_memalign(void **res, size_t align, size_t len)` over `M`. -/
c_type_spec mallocngModelPosixMemalignSpec (ctx M : AllocCostModel)
    (ctx I : MallocngCostModelIface M) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (res : ptr) (align : u64) (len : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost st : M.σ)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : u32) where
  let ok := mallocngPosixMemalignOk align len
  let ev := AllocEvent.aligned align.toNat len.toNat
  let st' := if ok then M.step ev st else st
  let stepB := if ok then M.stepReserve ev st else M.stepReserve (.alloc 0) st
  caveat [API_RESTRICTION] "align ≤ 2^31 avoids musl 1.2.5 set_size int32 reserved overflow" :
    align.toNat ≤ MaxAlignedAllocAlign
  c_arg res : MutRef (OptOutPtr (MallocngModelBlock I γ)) none ⇝
    (if ok then some (len.toNat, max align.toNat 16) else none)
  c_arg align : Val SizeT
  c_arg len : Val SizeT
  c_env (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  returns mallocngPosixMemalignRet align len
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when MallocngStepOomCond svc stepB s0 sf

/-! ## Model-Indexed Soundness Record -/

/-- The six placed C allocator entry points over `(M, I)`. -/
structure MallocngModelPlacedEntryContracts (M : AllocCostModel) (I : MallocngCostModelIface M)
    (mpl : Obj.MultiPlacement) (svc : State → State) : Prop where
  malloc_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "malloc"
      (mallocngModelMallocSpec M I svc γ (mallocngAddrsOfPlacement mpl))
  free_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "free"
      (mallocngModelFreeSpec M I γ (mallocngAddrsOfPlacement mpl))
  calloc_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "calloc"
      (mallocngModelCallocSpec M I svc γ (mallocngAddrsOfPlacement mpl))
  realloc_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "realloc"
      (mallocngModelReallocSpec M I svc γ (mallocngAddrsOfPlacement mpl))
  alignedAlloc_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "aligned_alloc"
      (mallocngModelAlignedAllocSpec M I svc γ (mallocngAddrsOfPlacement mpl))
  posixMemalign_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (mallocngModelPosixMemalignSpec M I svc γ (mallocngAddrsOfPlacement mpl))

/-- Soundness of cost model `M` with representation `I` for the compiled `mallocngLib`:
    startup into `I.HeapM ... M.init []`, the runtime split, block facts, the dynamic footprint
    bound by `M.maxDynIvs` / `M.footprint`, and all six placed entry contracts. -/
structure MallocngCostModelSound (M : AllocCostModel) (I : MallocngCostModelIface M) : Prop where
  init :
    ∀ (mpl : Obj.MultiPlacement) (tp brkStart auxvPtr : BitVec 64) (R : SepProp) (m : Memory),
      let A := mallocngAddrsOfPlacement mpl
      0xa4 ≤ tp.toNat →
      tp.toNat ≤ 2 ^ 48 →
      MallocngBrkStartWf brkStart →
      (m ⊨
        VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime A tp ∗
        ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) →
      ∃ γ : GhostName,
        m ⊨ |==> (I.HeapM γ A tp brkStart brkStart M.init [] ∗ R)
  init_resources :
    ∀ (A : MallocngAddrs) (tp brkStart : BitVec 64),
      0xa4 ≤ tp.toNat →
      tp.toNat ≤ 2 ^ 48 →
      MallocngBrkStartWf brkStart →
      MallocngStartupResources A tp ⊢
        |==> (∃∗ γ : GhostName, I.HeapM γ A tp brkStart brkStart M.init [])
  heap_split_runtime :
    ∀ (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
      (st : M.σ) (ivs : List (BitVec 64 × Nat)),
      I.HeapM γ A tp brkStart brk st ivs =
        (I.CoreM γ A brkStart brk st ivs ∗ MallocngRuntime A tp)
  block_nonnull :
    ∀ (γ : GhostName) (p : BitVec 64) (n effAlign : Nat),
      I.BlockM γ p n effAlign ⊢
        ⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + n ≤ 2 ^ 48 ∧ n ≤ MallocngMaxAllocSize⌝ ∗
          I.BlockM γ p n effAlign
  block_exclusive :
    ∀ (γ : GhostName) (p₁ : BitVec 64) (n₁ al₁ : Nat) (p₂ : BitVec 64) (n₂ al₂ : Nat),
      I.BlockM γ p₁ n₁ al₁ ∗ I.BlockM γ p₂ n₂ al₂ ⊢
        ⌜p₁ ≠ p₂⌝ ∗ I.BlockM γ p₁ n₁ al₁ ∗ I.BlockM γ p₂ n₂ al₂
  heap_footprint_bound :
    ∀ (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
      (st : M.σ) (ivs : List (BitVec 64 × Nat)) (h : Heap),
      SepProp.Holds (I.HeapM γ A tp brkStart brk st ivs) h →
      ivs.length ≤ M.maxDynIvs st ∧
      (ivs.map Prod.snd).sum ≤ M.footprint st ∧
      ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48
  entries_ok :
    ∀ (mpl : Obj.MultiPlacement) (svc : State → State),
      VerifiedLibraries.mallocngLib.Placeable mpl →
      MallocngSvcValid svc →
      MallocngModelPlacedEntryContracts M I mpl svc

/-! ## Usage-Indexed Tight Cost Model

`alloc_group` sizes a new root group of size class `sc` from the per-class usage counter
`ctx.usage_by_class[sc]`, which never exceeds `peakCount + 6`. The two step functions below tabulate,
at usage bound `U`, the largest root-group `mmap` length over all classes and the total length of the
root groups that `mallocng` may keep mapped while empty (one per class `7 ≤ sc ≤ 38`). -/

/-- Largest root-group `mmap` length (bytes) at usage bound `U`:

    | `U`       | bytes     |
    |-----------|-----------|
    | `0 - 3`   | `131072`  |
    | `4 - 5`   | `176128`  |
    | `6 - 15`  | `315392`  |
    | `16 - 31` | `524288`  |
    | `≥ 32`    | `1048576` | -/
def mallocngGroupMaxTab (U : Nat) : Nat :=
  if U < 4 then 131072
  else if U < 6 then 176128
  else if U < 16 then 315392
  else if U < 32 then 524288
  else 1048576

/-- Total length (bytes) of the kept-empty root groups at usage bound `U`:

    | `U`         | bytes     |   | `U`         | bytes     |
    |-------------|-----------|---|-------------|-----------|
    | `0 - 7`     | `675840`  |   | `56 - 63`   | `1818624` |
    | `8 - 15`    | `704512`  |   | `64 - 79`   | `2080768` |
    | `16 - 23`   | `770048`  |   | `80 - 95`   | `2605056` |
    | `24 - 31`   | `901120`  |   | `96 - 111`  | `3129344` |
    | `32 - 39`   | `1032192` |   | `112 - 123` | `3653632` |
    | `40 - 47`   | `1294336` |   | `124 - 127` | `3657728` |
    | `48 - 55`   | `1556480` |   | `≥ 128`     | `4177920` | -/
def mallocngKeptGroupsTab (U : Nat) : Nat :=
  if U < 8 then 675840
  else if U < 16 then 704512
  else if U < 24 then 770048
  else if U < 32 then 901120
  else if U < 40 then 1032192
  else if U < 48 then 1294336
  else if U < 56 then 1556480
  else if U < 64 then 1818624
  else if U < 80 then 2080768
  else if U < 96 then 2605056
  else if U < 112 then 3129344
  else if U < 124 then 3653632
  else if U < 128 then 3657728
  else 4177920

/-- Per-call step reserve at peak block count `pc` for an effective request of `req` bytes: the
    larger of the small-slot path (`4` metadata allocations of `180224 + 325 * pc` bytes each plus one
    root group) and the large path (`req + 4115` bytes plus one metadata allocation). It bounds the
    newly mapped bytes plus any refused `mmap` request. -/
def mallocngTight2Reserve (req pc : Nat) : Nat :=
  max (4 * (180224 + 325 * pc) + mallocngGroupMaxTab (pc + 6)) (req + 4115 + (180224 + 325 * pc))

/-- Usage-indexed tight cost model over `MallocngBudget` (`U = peakCount + 6`). Transitions are the
    `Top.lean` budget transitions (`mallocngAllocBudget`, `mallocngAlignedBudget`,
    `mallocngFreeBudget`, `mallocngReallocBudget`). The dynamic footprint is
    `mallocngKeptGroupsTab U + 24576 * ((88 + 8 * peakCount) / 101) + 40960 +
    mallocngGroupMaxTab U * liveCount + liveCost` bytes in `48 + 2 * peakCount` intervals. The step
    reserve is `mallocngTight2Reserve` of the effective request (`len + align - 16` for aligned
    allocations and reallocations at `align > 16`). -/
def mallocngTight2CostModel : AllocCostModel where
  σ := MallocngBudget
  init := mallocngZeroBudget
  step
    | .alloc req, b => mallocngAllocBudget true req b
    | .aligned align req, b => mallocngAlignedBudget true align req b
    | .free _ req, b => mallocngFreeBudget false req b
    | .realloc _ old new, b => mallocngReallocBudget true (some (old, [])) new b
  footprint b :=
    mallocngKeptGroupsTab (b.peakCount + 6) + 24576 * ((88 + 8 * b.peakCount) / 101) + 40960 +
      mallocngGroupMaxTab (b.peakCount + 6) * b.liveCount + b.liveCost
  maxDynIvs b := 48 + 2 * b.peakCount
  stepReserve
    | .alloc req, b => mallocngTight2Reserve req b.peakCount
    | .aligned align req, b => mallocngTight2Reserve (mallocngAlignedEffSize align req) b.peakCount
    | .free _ _, b => mallocngTight2Reserve 0 b.peakCount
    | .realloc align _ new, b =>
      mallocngTight2Reserve (mallocngAlignedEffSize align new) b.peakCount

/-- `mallocng` is sound for the usage-indexed tight cost model. -/
def MallocngTight2CostStmt : Prop :=
  ∃ I : MallocngCostModelIface mallocngTight2CostModel,
    MallocngCostModelSound mallocngTight2CostModel I

end VerifiedLibraries.Mallocng
